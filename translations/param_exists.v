(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils All.
From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Template Require Import Pretty.

Local Infix "<=" := Nat.leb.

Definition default_term := tVar "constant_not_found".
Definition debug_term msg:= tVar ("debug: " ^ msg).


Definition tsl_ident id := "EX"^id . (* ∃∃ *)



(*
Environment mappings are used as a generalized lifting function
n ↦ S n
is a lifting like lift0 1
*)
Definition Env := nat -> nat.
(*
Encapsulate element 0,
useful for lambda λ, let and products ∀
⇑ E 0 = 0
⇑ E (S n) = E (S n)
also used inside the application of lifting environments
*)
Definition EnvUp (E:Env) : Env :=
  fun n => match n with
  | O =>  O
  | S x => S (E x)
  end.

(*
lift all variables larger or equal to k by n
↑^n_k ≈ lift n k
the syntax reflects lift n k and lift0 n
*)
Definition EnvLift (E:Env) (n:nat) (k:nat) : Env :=
  fun x => let y := E x in
  if k<=y then n+y else y.

Definition EnvLift0 E n := EnvLift E n 0.

(*
application of a lifting environment to a term
under binders the given environment is transformed using up
*)
Fixpoint applyEnv (rel:Env) (t : term) {struct t} : term :=
  match t with
  | tRel k => tRel (rel k)
  | tEvar k ts => tEvar k (map (applyEnv rel ) ts)
  | tCast t c a => tCast (applyEnv rel t) c (applyEnv rel a)
  | tProd na A B => tProd na (applyEnv rel A) (applyEnv (EnvUp rel) B)
  | tLambda na A t => tLambda na (applyEnv rel A) (applyEnv (EnvUp rel) t)
  | tLetIn na t A u => tLetIn na (applyEnv rel t) (applyEnv rel A) (applyEnv (EnvUp rel) u)
  | tApp t lu => tApp (applyEnv rel t) (map (applyEnv rel) lu)
  | tCase ik t u br => tCase ik (applyEnv rel t) (applyEnv rel u)
                            (map (fun x => (fst x, applyEnv rel (snd x))) br)
  | tProj p t => tProj p (applyEnv rel t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

From MetaCoq Require Import Checker.
(* Checker for eq_term *)
(* checker is already required for translation utils *)
Existing Instance config.default_checker_flags.

(*
check if the term is suitable for translation with additional information
=> is a (recursive) argument, or a type
*)
Fixpoint isAugmentable (t:term) := 
  match t with 
  | tRel _ | tSort _ => true
  | tProd _ _ t2 => isAugmentable t2
  (* | tApp t1 t2 => isAugmentable t1 || existsb isAugmentable t2 *)
  (* not list recursive *)
  | tApp t1 t2 => isAugmentable t1
  | _ => false
  end.

(*
jointly handling of constants:
* definitions (tConst)
* inductive types (tInd)
* constructors (tConstruct)
*)
Inductive isConstant : term -> Type :=
| constIsConstant s univs: isConstant (tConst s univs)
| indIsConstant i univs: isConstant (tInd i univs)
| constructIsConstant i n univs: isConstant (tConstruct i n univs).
Hint Constructors isConstant.

Definition getRef (t:term) {h:isConstant t} : global_reference.
inversion h.
- exact (ConstRef s).
- exact (IndRef i).
- exact (ConstructRef i n).
Defined.

Definition getKername (t:term) {h:isConstant t} : kername.
inversion h.
- exact s.
- destruct i. exact (inductive_mind).
- destruct i. exact (inductive_mind).
Defined.

Definition isConstantBool (t:term) : bool :=
match t with 
| tConst _ _ | tInd _ _ | tConstruct _ _ _ => true
| _ => false
end.


(* Fixpoint tsl_rec1' (Env Envt: nat -> nat) (E : tsl_table) (t : term) : term :=
  let debug case symbol :=
      debug_term ("tsl_rec1: " ^ case ^ " " ^ symbol ^ " not found") in
  match t with
  (* types *)
  | tSort s => (* s ⇒ λ (A:s). A → s *)
  (* s_1: s -> s' and for A:s, s_1 A holds and A_1 : s_1 A *)
  (* a relation over types A of sort s, the s in the end is the property *)
    tLambda (nNamed "X") (tSort s) (tProd nAnon (tRel 0) (tSort s))
  | tProd na A B =>
  (* ∀ (x:A). B ⇒ λ(f:∀(x:A_0,B_0)). ∀(x:A_0) (xᵗ:A_1 x). B_1 (f x) *)
  (* the translation relates functions A->B 
    by the relation of their results (B) on related inputs (x) *)
    let generate := isAugmentable A || (negb deleteNonTypes) in

    tLambda (nNamed "f") (tProd na (tsl_rec0_2 Env A) (tsl_rec0_2 (EnvUp Env) B))
      (tProd na (tsl_rec0_2 (EnvLift0 Env 1) A)
      (*     x  :  A      *)
                          (* lift over f *)
          (if generate then
             (tProd (tsl_name tsl_ident na)
                    (subst_app (tsl_rec1' deleteNonTypes (EnvLift0 Env 2) (EnvLift0 Envt 2) E A) [tRel 0])
                    (* xᵗ  :        Aᵗ                                                              x  *)
                                                              (* lift over x and f *)
                    (subst_app (tsl_rec1' deleteNonTypes (EnvLift (EnvLift (EnvUp Env) 1 1) 1 0) (EnvLift (EnvUp Envt) 2 1) E B)
                                                        (* go under ∀ x binder, lift over xᵗ and f *)
                                                                                            (* go under ∀ x binder, lift over x and f *)
                               [tApp (tRel 2) [tRel 1]]))
                              (* f x *)
          else
            (subst_app 
              (tsl_rec1' deleteNonTypes (EnvLift (EnvUp Env) 1 1) (EnvLift (EnvUp Envt) 1 1) E B)
              [tApp (tRel 1) [tRel 0]]))
      )

  | tRel k => (* x ⇒ xᵗ *)
  (* 
  Q x, T  -> Q x x^t, T
  0(x) => 0(x^t)

  Q y z, T -> Q y y^t z z^t, T
  1(y) => 2(y^t)

  the arguments are translated 
  to the newly added translations
  the indices are handeled by the
  translated environment
  *)
    tRel (Envt k)
  | tLambda na A t =>
    (* λ(x:A).t ⇒ λ(x:A_0)(xᵗ:A_1 x). t_1 *)

    (* proof of function A->B is translated to proof 
      of a relation of B taking related arguments
    *)
    tLambda na (tsl_rec0_2 Env A) 
      (tLambda (tsl_name tsl_ident na)
               (subst_app (tsl_rec1' deleteNonTypes (EnvLift0 Env 1) (EnvLift0 Envt 1) E A) [tRel 0])
                                                          (* lift over x *)
                           (tsl_rec1' deleteNonTypes (EnvLift (EnvUp Env) 1 0) (EnvLift (EnvUp Envt) 1 1)  E t))
                                                                    (* go under binder x *)
                                                      (* lift over x^t *)
                                                                                (* use x^t, lift over x *)
  | tApp t us =>
  (* t1 t2 ⇒ t1ᵗ t2 t2ᵗ *)
  (* for every argument t2 the relation of t1 is supplied with
   the argument t2 and the relation over t2 *)
    let us' := concat (map (fun v => 
      let arg := tsl_rec0_2 Env v in
      let argt :=  tsl_rec1' deleteNonTypes Env Envt E v in
      if (eq_term init_graph arg argt || negb(isAugmentable arg)) && deleteNonTypes then [arg] else  (* not S -> S^t *)
      [arg;argt]) us) in
    mkApps (tsl_rec1' deleteNonTypes Env Envt E t) us'
  | tLetIn na t A u =>
  (* let x := t : A in u ⇒ 
     let x := t : A in 
       let xᵗ := tᵗ : Aᵗ x in
       uᵗ
    *)
    tLetIn na (tsl_rec0_2 Env t) (tsl_rec0_2 Env A) 
    (tLetIn (tsl_name tsl_ident na) 
          (tsl_rec1' deleteNonTypes (EnvLift0 Env 1) (EnvLift0 Envt 1) E t)
                                           (* lift over x *)
          (subst_app (tsl_rec1' deleteNonTypes (EnvLift0 Env 1) (EnvLift0 Envt 1) E A) [tRel 0]) 
                                                        (* lift over x *)
          (tsl_rec1' deleteNonTypes (EnvLift (EnvUp Env) 1 0) (EnvLift (EnvUp Envt) 1 1)  E u))
                                                  (* go under x binder *)
                                    (* lift over xᵗ *)
                                                              (* lift over x *)
  | tCast t c A => 
  (* (A) t ⇒ (Aᵗ ((A) x)) tᵗ *)
  (* casting of t into A is transformed
  to the casting of the translation of t 
  into the translation fo A applied to the 
  original casting

  no lifting is required
   *)
  tCast (tsl_rec1' deleteNonTypes Env Envt E t) c 
    (mkApps (tsl_rec1' deleteNonTypes Env Envt E A) 
      [tCast (tsl_rec0_2 Env t) c (tsl_rec0_2 Env A)])


  (* all three constants are translated by a lookup in the table *)
  (* combination of the three cases would need equation to remember the case *)
  | tConst s univs =>
    match lookup_tsl_table E (ConstRef s) with
    | Some t => t
    | None => debug "tConst" (string_of_kername s)
    end
  | tInd i univs =>
    match lookup_tsl_table E (IndRef i) with
    | Some t => t
    | None => debug "tInd" (match i with mkInd s _ => string_of_kername s end)
    end
  | tConstruct i n univs =>
    match lookup_tsl_table E (ConstructRef i n) with
    | Some t => t
    | None => debug "tConstruct" (match i with mkInd s _ => string_of_kername s end)
    end

  | tCase _ _ _ _ => todo "tsl"
  | tProj _ _ => todo "tsl"
  | tFix _ _ | tCoFix _ _ => todo "tsl"
  | tVar _ | tEvar _ _ => todo "tsl var"
  end. *)

Notation "'if' x 'is' p 'then' A 'else' B" :=
  (match x with p => A | _ => B end)
    (at level 200, p pattern,right associativity).

(* Fixpoint tsl_rec1' (Env Envt: nat -> nat) (E : tsl_table) (t : term) : option term :=
  let debug case symbol :=
      debug_term ("tsl_rec1: " ^ case ^ " " ^ symbol ^ " not found") in
  Some t. *)

(* deletes lambdas in front of a term *)
(* used for product relation function *)
Fixpoint remove_lambda (t : term) : term :=
  match t with
  | tLambda _ _ B => remove_lambda B
  | _ => t
  end.

(* collect prods into context list and remaining term *)
(* inverse (up to reversion) of it_mkProd_or_LetIn 
  (for vass in back direction) *)
Fixpoint decompose_prod_context (t : term) : context * term :=
  match t with
  | tProd n A B => let (Cs, B) := decompose_prod_context B in
                  (vass n A :: Cs, B)
  | _ => ([], t)
  end.

(* translates a parameter list *)
(* moves parameters as prods in front of Type,
  translates it,
  removes first relation lambda, converts back to context (declaration list)
  and deletes sort translation prod at the end
*)
(* the parameters are stored in reverse order,
but the it_mkProd_or_LetIn uses a reversed list
in the end a reversion is needed as decompose
is in correct order *)
(* Definition transformParams (prune:bool) (E:tsl_table) (params:context) : context :=
    (let paramType := it_mkProd_or_LetIn params <% Type %> in
    let transformRel := tsl_rec1_prune prune E paramType in
    let prods := fst(decompose_prod_context (remove_lambda transformRel)) in
    tl (rev prods)). *)

(* Definition tsl_rec1' (Env Envt: nat -> nat) (E : tsl_table) (t : term) : term := t. *)

(* Definition tsl_rec1 := tsl_rec1' (fun n => n) (fun n => n). *)

(* rec, apply list *)
(* lift everything else by 1 *)
Definition augment (t:term) : option term :=
  match t with 
  | tSort u => Some(tProd nAnon (tRel 0) t)
  | _ => None
  end.

Definition on_fst {X Y Z} (f:X->Z) (p:X*Y) := match p with (x,y) => (f x,y) end.

Definition name_map f (na:name) := if na is nNamed id then nNamed (f id) else nAnon.

Fixpoint transformParams (env:Env) (E:tsl_table) (params:context) : context*Env :=
  match params with 
  | nil => (nil,env)
  | (mkdecl name _ type as decl)::xs =>
    on_fst (cons (vass name (applyEnv env type)))
    (if augment (applyEnv env type) is Some t' then 
      on_fst (cons (vass (name_map tsl_ident name) (t'))) (transformParams (EnvLift0 (EnvUp env) 1) E xs)
    else 
      transformParams (EnvUp env) E xs)
  end.


Definition paramTermTrans E (t:term) :=
  let (ctx,tb) := decompose_prod_context t in
  let (ctx',env) := transformParams (fun n => n) E ctx in
  it_mkProd_or_LetIn (rev ctx') tb.

MetaCoq Quote Definition testQ := (forall (X:Type) (x1:X) (Y:Type) (y1:Y) (x2:X) (y2:Y), Type).
Compute (paramTermTrans [] testQ).

Fixpoint makeRels (n:nat) :=
  match n with 
  | O => []
  | S m => tRel m::makeRels m 
  end.

Fixpoint cutList {X} n (xs:list X) :=
  match n with 
  | O => xs
  | S m => tl (cutList m xs)
  end.

Definition removeApps n t :=
  if t is tApp tb args then mkApps tb (cutList n args) else t.

Definition idEnv n : nat := n.


Fixpoint tsl_rec1' (E : tsl_table) (oldParamCount:nat) (rec:term) (recInd:inductive) (t : term) : option term :=
  let debug case symbol :=
      debug_term ("tsl_rec1: " ^ case ^ " " ^ symbol ^ " not found") in
      (* if rec => already replaced *)
  (* let handleInd ind inst arg := None
    if eq_inductive ind recInd then 
      Some rec (* transfer indices *)
    else
      Some (tApp (tVar "IND") [t])
  in *)
  match t with
  | tRel (S n) => Some (tRel (n))
  | tInd ind inst => 
    if eq_inductive ind recInd then 
      Some rec else 
      None
      (* Some (tApp (tVar "IND") [t;tInd recInd []]) *)
  | tApp (tInd _ _ as iT) args => 
    if tsl_rec1' E oldParamCount rec recInd iT is Some r then
    Some(mkApps r (cutList oldParamCount args)) else None
  (* | tInd ind inst => handleInd ind inst [] *)
  (* | tApp (tInd ind inst) args => handleInd ind inst args *)
  | _ => None
      (* Some (tApp (tVar "OTHER") [t]) *)
  end.
  (* lookup decl/ind *)


(* translates a mutual inductive definition *)
(* the translation is constructed in proof mode 
to follow the structure, keep track of types,
avoid deep nesting and delay application arguments
*)
Definition tsl_mind_body (prune:bool) (E : tsl_table) (mp : modpath) (kn : kername)
           (mind : mutual_inductive_body) : tsl_table * list mutual_inductive_body.
  (* computes the new parameters *)
  (* the unquoting does not care about the parameters but only about the length
  of ind_params *)
  (* for a pure unary parametricity translation even
  mind.(ind_params) ++ mind.(ind_params) workds *)
 (* the universe of the inductive and the variance are not changed by the translation *)
  set(paramlist_env := on_fst rev (transformParams (fun n => n) E (rev mind.(ind_params)))).
  destruct paramlist_env as [paramlist env].
  refine (_, [{| ind_npars := #|paramlist|;
                 ind_params := paramlist;
                 ind_bodies := _;
                 ind_finite := mind.(ind_finite);
                 ind_universes := mind.(ind_universes);
                 ind_variance := mind.(ind_variance)|}]).
  - (* new translations for the one_inductive_bodies in the 
     mutual inductive definition *)
    refine (let kn' : kername := (mp, tsl_ident kn.2) in
            fold_left_i (fun E i ind => _ :: _ ++ E) mind.(ind_bodies) []).
    (* for each one_inductive ind with index i, add new table *)
    + (* translation reference of inductive *)
      (* the new type kn' does not exists yet, but will in future translations *)
      exact (IndRef (mkInd kn i), tInd (mkInd kn' i) []).
    + (* translation references of ctors of ind *)
    (* create reference for each constructor k *)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd kn i) k, tConstruct (mkInd kn' i) k []).
  - (* translate the one_inductive_bodys individually *)
    refine (mapi _ mind.(ind_bodies)).
    intros i ind. (* number of inductive body and body *)
    refine {| ind_name := tsl_ident ind.(ind_name);
              ind_type := _;
              ind_kelim := ind.(ind_kelim);
              ind_ctors := _;
              ind_projs := [] |}.
    + (* translate the type (with parameters) of the inductive body *)
      refine (
        let (ctx,tb) := decompose_prod_context (remove_arity mind.(ind_npars) ind.(ind_type)) in
        it_mkProd_or_LetIn paramlist (
          it_mkProd_or_LetIn ctx (* indices *)
          (tProd nAnon 
          (mkApps (lift0 #|ctx| (applyEnv env (tApp (tInd (mkInd kn i) []) (makeRels mind.(ind_npars))))) (makeRels #|ctx|)) (* old type with params *)
            (lift0 1 tb))) (* later tProd element *)
      ).
      (* refine (subst_app (tsl_rec1 E ind.(ind_type))
                                  [tInd (mkInd kn i) []]). *)
    + (* constructors *)
      (* definition as function for better control flow overview *)
      refine (concat _).
    refine(
      mapi 
      (
        fun k '((name,typ,nargs)) => 
        let typInd :=  (* fillin inductives for recursion *)
          (fold_left_i 
            (fun t0 i u  => t0 {i := u})
            (rev (mapi (fun i _ => tInd (mkInd kn i) [])
                              mind.(ind_bodies)))
            typ) in
        let typ' := remove_arity (mind.(ind_npars)) typInd in
        let (args,tb) := decompose_prod_context (applyEnv env typ') in
        let inst :=
          mkApps (lift0 #|args| (applyEnv env (tApp (tConstruct (mkInd kn i) k []) (makeRels mind.(ind_npars))))) (makeRels #|args|)
        in
        (* apply new params => remove old app add new *)
        let recInst := tRel (#|paramlist| + #|args|) in
        let tbNewParams :=
          mkApps recInst (map (lift0 #|args|) (makeRels #|paramlist|))
        in
        let tbNewIndApp :=
          (if tb is (tApp tI appargs) then
          (* tI was replace by ind filling *)
            mkApps tbNewParams (cutList mind.(ind_npars) appargs)
          else recInst)
        in
(* mkApps (removeApps mind.(ind_npars) tb) (map (lift0 #|args| )) *)
        let tb' := mkApp tbNewIndApp inst in
        (* let tb' :=
          (tProd nAnon 
          (mkApps (lift0 #|args| (applyEnv env (tApp (tInd (mkInd kn i) []) (makeRels mind.(ind_npars))))) (makeRels #|args|)) (* old type with params *)
            (lift0 1 tb))) *)
        let na := tsl_ident name in
        _)
      ind.(ind_ctors)
    ).
    refine(
        rev(fold_left_i
        (fun acc j arg => 
          (* rec is replaced *)
          let rec :=  tbNewParams in
          let augArgO := tsl_rec1' E mind.(ind_npars) rec (mkInd kn i) (lift0 (#|args| - j) (decl_type arg)) in
          (* let augArgO := Some (lift0 (#|args| - j) (decl_type arg)) in *)
          (* let augArg := Some (tRel 0) in *)
          if augArgO is Some augArgP then
          let augArg := mkApp augArgP (tRel (#|args| - S j)) in
          (* let augArg := augArgP in *)
          (let ctor_type := 
          it_mkProd_or_LetIn paramlist (
          it_mkProd_or_LetIn (rev args) (
            tProd nAnon augArg
            (lift0 1 tb')
          )) in
          (na^(string_of_nat j), 
          ctor_type, 
          #|fst (decompose_prod_context ctor_type)|)
          :: acc)
          else acc
        ) args [])
    ).
Defined.


(* one way to get the dot character '.' *)
Definition dot : Ascii.ascii.
destruct "." eqn:H;[discriminate|assumption].
Defined.

(* computes last part after dot *)
(* needed to find identifies of, for example, local definitions *)
(* definitions and fresh names can not be generated 
  when a modpath-part with '.' is present *)
Fixpoint lastPart (id:ident) :=
  match id with
  | EmptyString => (id,false)
  | String a id' => 
    let (idr,b) := lastPart id' in
    if b then (idr,b) else
    (
      if Ascii.eqb a dot then (idr,true) else (String a idr,false) 
    )
  end.

(* removed the modpath in front of the identifier *)
Definition tsl_ident' id := tsl_ident(fst(lastPart id)).

(* registeres the unary parametricity translations as translation instance *)
Instance param : Translation :=
  {| tsl_id := tsl_ident' ;
     tsl_tm := fun ΣE t => ret (paramTermTrans (snd ΣE) t);
     (* Implement and Implement Existing cannot be used with this translation *)
     tsl_ty := None ;
     tsl_ind := fun ΣE mp kn mind => 
     ret (tsl_mind_body false (snd ΣE) mp kn mind) |}.


(* stores translation of definitions *)
(* global context is not important => always use empty_ext [] *)
(* better would be the translated global_reference but 
  this is not accessible from the outside *)
Class translated (ref:global_reference) := 
{
  (* content : term  *) (* would be enough for constant *)
  content : tsl_table (* needed for inductive translations *)
  (* for constants this degenerates to [(ref,contentTerm)] *)
}.

(* lookup a global reference in the translation database and add its
  translation table to the context *)
Definition checkTranslation (ΣE:tsl_context) (ref:global_reference) : TemplateMonad tsl_context :=
      match lookup_tsl_table (snd ΣE) ref with
      | Some _ => ret ΣE
      | None => 
      (* lookup if a translation exists *)
          opt <- tmInferInstance None (translated ref);;
          match opt with (* match over custom option type for inference results *)
          | my_Some x => 
            let Σ' := fst ΣE in
            let E' := ((@content _ x)  ++ (snd ΣE))%list in (* TODO: can contain duplicates (see below) *)
            Σ' <- tmEval lazy Σ' ;;
            E' <- tmEval lazy E' ;;
            ret (Σ', E')
          | my_None => ret ΣE
          end
      end.

(* quotes the environment and adds translations of declarations 
  from it to the context *)
(* for additional creation of missing translations,
use TranslateRec with constructed table as seed *)
Definition ConstructTable {A} (t:A) : TemplateMonad tsl_context :=
  p <- tmQuoteRec t ;;
  tmPrint "~~~~~~~~~~~~~~~~~~" ;;
  monad_fold_right (fun ΣE '(kn, decl) =>
    print_nf ("Looking up " ^ string_of_kername kn) ;;
    match decl with
    | ConstantDecl decl => checkTranslation ΣE (ConstRef kn)
    | InductiveDecl d => checkTranslation ΣE (IndRef (mkInd kn 0))
    end)
  (fst p) (emptyTC).

(* the cases could be all in one and the command with 
  distinction on references/other terms could be a Template command
 *)
Definition getIdentKername' (t:term)  : TemplateMonad kername :=
  tmReturn match t with
  (* handle all cases in one *)
  | tInd (mkInd kername _) _
  | tConst kername _
  | tConstruct (mkInd kername _) _ _ => 
    kername
  | _ => (MPfile [],"") (* dummy value *)
  end.
Definition getIdentKername {A} (t:A)  : TemplateMonad kername :=
  q <- tmQuote t;;
  getIdentKername' (if q is tApp q' _ then q' else q).

(* gets the local identifier (short name) *)
Definition getIdent {A} (t:A)  : TemplateMonad string :=
  kername <- getIdentKername t;;
  tmReturn (snd kername).

(* full mod path and identifier (separated by '.') *)
Definition getIdentComplete {A} (t:A)  : TemplateMonad string :=
  kername <- getIdentKername t;;
  tmReturn (string_of_kername kername).

  (* retrieves a reference from a coq term of a definition *)
Definition tmLookup {A} (t:A) : TemplateMonad global_reference :=
  getIdentComplete t >>= tmLocate1.

(* generates a table with all translations possibly needed for lookup *)
Definition persistentTranslate_prune {A} (t:A) (prune:bool) : TemplateMonad tsl_context :=
  tc <- ConstructTable t;; (* get table *)
  id <- getIdentComplete t;;
  idname <- getIdent t;;
  tmMsg ("Complete Identifier: "^id);;
  tmMsg ("Short Identifier: "^idname);;
  tc' <- (@Translate param) tc id;; (* translate new definition *)
  (* TODO: chose pruning translation *)

  gr <- tmLookup t;;
  (* extend table *)
  (* TODO: too large only needs new part *)
  (* easiest way would be to undup (or track what is new) *)
  (* variant 1: new-old *)
  (* variant 2: undup in creation *)
  (* variant 3: tracking *)
      nameString <- tmEval lazy (append idname "_tableLookup");;
      newName <- tmFreshName nameString;;
      tmDefinition newName (
        {|
            content := snd tc';
        |} : translated gr
      );;
  (* save new table for the translation definition t *)
  tmExistingInstance (VarRef newName);;
  tmReturn tc'
  .

Definition persistentTranslate {A} (t:A) : TemplateMonad tsl_context :=
  persistentTranslate_prune t false.