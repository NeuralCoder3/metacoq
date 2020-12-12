(** Distributed under the terms of the MIT license. **)

(*** param_unary: Unary parametricity translation ***)

From MetaCoq.Template Require Import utils All.
From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Template Require Import Pretty.

Local Infix "<=" := Nat.leb.

Definition default_term := tVar "constant_not_found".
Definition debug_term msg:= tVar ("debug: " ^ msg).

(** for debugging **)
(** Definition subst_app := mkApps. **)
  (** Definition todo := tVar. **)


Definition tsl_ident_unparam id := id^"ᵗ".
Definition tsl_ident := tsl_ident_unparam.





(**
Environment mappings are used as a generalized lifting function
n ↦ S n
is a lifting like lift0 1
**)
Definition Env := nat -> nat.
(**
Encapsulate element 0,
useful for lambda λ, let and products ∀
⇑ E 0 = 0
⇑ E (S n) = E (S n)
also used inside the application of lifting environments
**)
Definition EnvUp (E:Env) : Env :=
  fun n => match n with
  | O =>  O
  | S x => S (E x)
  end.

(**
lift all variables larger or equal to k by n
↑^n_k ≈ lift n k
the syntax reflects lift n k and lift0 n
**)
Definition EnvLift (E:Env) (n:nat) (k:nat) : Env :=
  fun x => let y := E x in
  if k<=y then n+y else y.

Definition EnvLift0 E n := EnvLift E n 0.

(**
application of a lifting environment to a term
under binders the given environment is transformed using up
**)
Fixpoint tsl_rec0_2 (rel:Env) (t : term) {struct t} : term :=
  match t with
  | tRel k => tRel (rel k)
  | tEvar k ts => tEvar k (map (tsl_rec0_2 rel ) ts)
  | tCast t c a => tCast (tsl_rec0_2 rel t) c (tsl_rec0_2 rel a)
  | tProd na A B => tProd na (tsl_rec0_2 rel A) (tsl_rec0_2 (EnvUp rel) B)
  | tLambda na A t => tLambda na (tsl_rec0_2 rel A) (tsl_rec0_2 (EnvUp rel) t)
  | tLetIn na t A u => tLetIn na (tsl_rec0_2 rel t) (tsl_rec0_2 rel A) (tsl_rec0_2 (EnvUp rel) u)
  | tApp t lu => tApp (tsl_rec0_2 rel t) (map (tsl_rec0_2 rel) lu)
  | tCase ik t u br => tCase ik (tsl_rec0_2 rel t) (tsl_rec0_2 rel u)
                            (map (fun x => (fst x, tsl_rec0_2 rel (snd x))) br)
  | tProj p t => tProj p (tsl_rec0_2 rel t)
  (** | tFix : mfixpoint term -> nat -> term **)
  (** | tCoFix : mfixpoint term -> nat -> term **)
  | _ => t
  end.

From MetaCoq Require Import Checker.
(** Checker for eq_term **)
(** checker is already required for translation utils **)
Existing Instance config.default_checker_flags.

(**
check if the term is suitable for translation with additional information
=> is a (recursive) argument, or a type
**)
Fixpoint isAugmentable (t:term) := 
  match t with 
  | tRel _ | tSort _ => true
  | tProd _ _ t2 => isAugmentable t2
  (** | tApp t1 t2 => isAugmentable t1 || existsb isAugmentable t2 **)
  (** not list recursive **)
  | tApp t1 t2 => isAugmentable t1
  | _ => false
  end.

(**
jointly handling of constants:
- definitions (tConst)
- inductive types (tInd)
- constructors (tConstruct)
**)
Inductive isConstant : term -> Type :=
| constIsConstant s univs: isConstant (tConst s univs)
| indIsConstant i univs: isConstant (tInd i univs)
| constructIsConstant i n univs: isConstant (tConstruct i n univs).

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


(** the unary parametricity translation of an object is
a relation over the objects **)
(** X_1 is the unary parametricity translation
where the identifiers are Xᵗ **)
(**
types T are translated into relations of objects of type T
  (using lambas for the objects)
terms are translated to proofs of the relations
**)
(**
two environments are used:
Env for normal (not translated) terms
and Envt for the translations of the original terms
**)
Fixpoint tsl_rec1' (deleteNonTypes:bool) (Env Envt: nat -> nat) (E : tsl_table) (t : term) : term :=
  let debug case symbol :=
      debug_term ("tsl_rec1: " ^ case ^ " " ^ symbol ^ " not found") in
  match t with
  (** types **)
  | tSort s => (** s ⇒ λ (A:s). A → s **)
  (** s_1: s -> s' and for A:s, s_1 A holds and A_1 : s_1 A **)
  (** a relation over types A of sort s, the s in the end is the property **)
    tLambda (nNamed "X") (tSort s) (tProd nAnon (tRel 0) (tSort s))
  | tProd na A B =>
  (** ∀ (x:A). B ⇒ λ(f:∀(x:A_0,B_0)). ∀(x:A_0) (xᵗ:A_1 x). B_1 (f x) **)
  (** the translation relates functions A->B 
    by the relation of their results (B) on related inputs (x) **)
    let generate := isAugmentable A || (negb deleteNonTypes) in

    tLambda (nNamed "f") (tProd na (tsl_rec0_2 Env A) (tsl_rec0_2 (EnvUp Env) B))
      (tProd na (tsl_rec0_2 (EnvLift0 Env 1) A)
      (**     x  :  A      **)
                          (** lift over f **)
          (if generate then
             (tProd (tsl_name tsl_ident na)
                    (subst_app (tsl_rec1' deleteNonTypes (EnvLift0 Env 2) (EnvLift0 Envt 2) E A) [tRel 0])
                    (** xᵗ  :        Aᵗ                                                              x  **)
                                                              (** lift over x and f **)
                    (subst_app (tsl_rec1' deleteNonTypes (EnvLift (EnvLift (EnvUp Env) 1 1) 1 0) (EnvLift (EnvUp Envt) 2 1) E B)
                                                        (** go under ∀ x binder, lift over xᵗ and f **)
                                                                                            (** go under ∀ x binder, lift over x and f **)
                               [tApp (tRel 2) [tRel 1]]))
                              (** f x **)
          else
            (subst_app 
              (tsl_rec1' deleteNonTypes (EnvLift (EnvUp Env) 1 1) (EnvLift (EnvUp Envt) 1 1) E B)
              [tApp (tRel 1) [tRel 0]]))
      )

  | tRel k => (** x ⇒ xᵗ **)
  (** 
  Q x, T  -> Q x x^t, T
  0(x) => 0(x^t)

  Q y z, T -> Q y y^t z z^t, T
  1(y) => 2(y^t)

  the arguments are translated 
  to the newly added translations
  the indices are handeled by the
  translated environment
  **)
    tRel (Envt k)
  | tLambda na A t =>
    (** λ(x:A).t ⇒ λ(x:A_0)(xᵗ:A_1 x). t_1 **)

    (** proof of function A->B is translated to proof 
      of a relation of B taking related arguments
    **)
    tLambda na (tsl_rec0_2 Env A) 
      (tLambda (tsl_name tsl_ident na)
               (subst_app (tsl_rec1' deleteNonTypes (EnvLift0 Env 1) (EnvLift0 Envt 1) E A) [tRel 0])
                                                          (** lift over x **)
                           (tsl_rec1' deleteNonTypes (EnvLift (EnvUp Env) 1 0) (EnvLift (EnvUp Envt) 1 1)  E t))
                                                                    (** go under binder x **)
                                                      (** lift over x^t **)
                                                                                (** use x^t, lift over x **)
  | tApp t us =>
  (** t1 t2 ⇒ t1ᵗ t2 t2ᵗ **)
  (** for every argument t2 the relation of t1 is supplied with
   the argument t2 and the relation over t2 **)
    let us' := concat (map (fun v => 
      let arg := tsl_rec0_2 Env v in
      let argt :=  tsl_rec1' deleteNonTypes Env Envt E v in
      if (eq_term init_graph arg argt || negb(isAugmentable arg)) && deleteNonTypes then [arg] else  (** not S -> S^t **)
      [arg;argt]) us) in
    mkApps (tsl_rec1' deleteNonTypes Env Envt E t) us'
  | tLetIn na t A u =>
  (** let x := t : A in u ⇒ 
     let x := t : A in 
       let xᵗ := tᵗ : Aᵗ x in
       uᵗ
    **)
    tLetIn na (tsl_rec0_2 Env t) (tsl_rec0_2 Env A) 
    (tLetIn (tsl_name tsl_ident na) 
          (tsl_rec1' deleteNonTypes (EnvLift0 Env 1) (EnvLift0 Envt 1) E t)
                                           (** lift over x **)
          (subst_app (tsl_rec1' deleteNonTypes (EnvLift0 Env 1) (EnvLift0 Envt 1) E A) [tRel 0]) 
                                                        (** lift over x **)
          (tsl_rec1' deleteNonTypes (EnvLift (EnvUp Env) 1 0) (EnvLift (EnvUp Envt) 1 1)  E u))
                                                  (** go under x binder **)
                                    (** lift over xᵗ **)
                                                              (** lift over x **)
  | tCast t c A => 
  (** (A) t ⇒ (Aᵗ ((A) x)) tᵗ **)
  (** casting of t into A is transformed
  to the casting of the translation of t 
  into the translation fo A applied to the 
  original casting

  no lifting is required
   **)
  tCast (tsl_rec1' deleteNonTypes Env Envt E t) c 
    (mkApps (tsl_rec1' deleteNonTypes Env Envt E A) 
      [tCast (tsl_rec0_2 Env t) c (tsl_rec0_2 Env A)])


  (** all three constants are translated by a lookup in the table **)
  (** combination of the three cases would need equation to remember the case **)
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
  end.

Notation "'if' x 'is' p 'then' A 'else' B" :=
  (match x with p => A | _ => B end)
    (at level 200, p pattern,right associativity).

(** initial translation of outside variables (like inductive types) are 
most clearly stated by multiplication **)
Definition tsl_rec1_prune (prune:bool) := tsl_rec1' prune (fun n => S(2*n)) (fun n => 2*n)%nat.
Definition tsl_rec1 := tsl_rec1_prune false.


(** deletes lambdas in front of a term **)
(** used for product relation function **)
Fixpoint remove_lambda (t : term) : term :=
  match t with
  | tLambda _ _ B => remove_lambda B
  | _ => t
  end.

(** collect prods into context list and remaining term **)
(** inverse (up to reversion) of it_mkProd_or_LetIn 
  (for vass in back direction) **)
Fixpoint decompose_prod_context (t : term) : context * term :=
  match t with
  | tProd n A B => let (Cs, B) := decompose_prod_context B in
                  (vass n A :: Cs, B)
  | _ => ([], t)
  end.

(** translates a parameter list **)
(** moves parameters as prods in front of Type,
  translates it,
  removes first relation lambda, converts back to context (declaration list)
  and deletes sort translation prod at the end
**)
(** the parameters are stored in reverse order,
but the it_mkProd_or_LetIn uses a reversed list
in the end a reversion is needed as decompose
is in correct order **)
Definition transformParams (prune:bool) (E:tsl_table) (params:context) : context :=
    (let paramType := it_mkProd_or_LetIn params <% Type %> in
    let transformRel := tsl_rec1_prune prune E paramType in
    let prods := fst(decompose_prod_context (remove_lambda transformRel)) in
    tl (rev prods)).

(** translates a mutual inductive definition **)
(** the translation is constructed in proof mode 
to follow the structure, keep track of types,
avoid deep nesting and delay application arguments
**)
Definition tsl_mind_body (prune:bool) (E : tsl_table) (mp : modpath) (kn : kername)
           (mind : mutual_inductive_body) : tsl_table * list mutual_inductive_body.
  (** computes the new parameters **)
  (** the unquoting does not care about the parameters but only about the length
  of ind_params **)
  (** for a pure unary parametricity translation even
  mind.(ind_params) ++ mind.(ind_params) workds **)
 (** the universe of the inductive and the variance are not changed by the translation **)
  set(paramlist := transformParams prune E mind.(ind_params)).
  refine (_, [{| ind_npars := #|paramlist|;
                 ind_params := paramlist;
                 ind_bodies := _;
                 ind_finite := mind.(ind_finite);
                 ind_universes := mind.(ind_universes);
                 ind_variance := mind.(ind_variance)|}]).
  - (** new translations for the one_inductive_bodies in the 
     mutual inductive definition **)
    refine (let kn' : kername := (mp, tsl_ident kn.2) in
            fold_left_i (fun E i ind => _ :: _ ++ E) mind.(ind_bodies) []).
    (** for each one_inductive ind with index i, add new table **)
    + (** translation reference of inductive **)
      (** the new type kn' does not exists yet, but will in future translations **)
      exact (IndRef (mkInd kn i), tInd (mkInd kn' i) []).
    + (** translation references of ctors of ind **)
    (** create reference for each constructor k **)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd kn i) k, tConstruct (mkInd kn' i) k []).
  - (** translate the one_inductive_bodys individually **)
    refine (mapi _ mind.(ind_bodies)).
    intros i ind. (** number of inductive body and body **)
    refine {| ind_name := tsl_ident ind.(ind_name);
              ind_type := _;
              ind_kelim := ind.(ind_kelim);
              ind_ctors := _;
              ind_projs := [] |}.
    + (** translate the type (with parameters) of the inductive body **)
      refine (subst_app (tsl_rec1_prune prune E ind.(ind_type))
                                  [tInd (mkInd kn i) []]).
    + (** constructors **)
      (** definition as function for better control flow overview **)
    refine(
      mapi 
      (
        fun k '((name,typ,nargs)) => 
        let ctor_type :=
        subst_app 
        (** possibility: add nat -> tRel 0 in table for 
          fill-in and then translate **)
          ((fold_left_i 
            (** fill in implicit tRel for 
                mutual types and inductive type itself **)
            (fun t0 i u  => t0 {S i := u})
            (rev (mapi (fun i _ => tInd (mkInd kn i) [])
                              mind.(ind_bodies)))
            (tsl_rec1_prune prune E typ)) (** first translate s.t. tRel 0 => tRel 0 ; tRel 1 
              instead of nat => nat ; nat^t (does not exists) **)
          )
         [tConstruct (mkInd kn i) k []] 
         (** place original constructor in generated relation as tRel 0 **) in
        (tsl_ident name, (** translate constructor name **)
        ctor_type, (** translated constructor type **)
        #|fst (decompose_prod_context ctor_type)|) (** all prods are arguments **)
      )
      ind.(ind_ctors)
    ).
Defined.


(** one way to get the dot character '.' **)
Definition dot : Ascii.ascii.
destruct "." eqn:H;[discriminate|assumption].
Defined.

(** computes last part after dot **)
(** needed to find identifies of, for example, local definitions **)
(** definitions and fresh names can not be generated 
  when a modpath-part with '.' is present **)
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

(** removed the modpath in front of the identifier **)
Definition tsl_ident' id := tsl_ident(fst(lastPart id)).

Instance param_prune : Translation :=
  {| tsl_id := tsl_ident' ;
     tsl_tm := fun ΣE t => ret (tsl_rec1_prune true (snd ΣE) t) ;
     (** Implement and Implement Existing cannot be used with this translation **)
     tsl_ty := None ;
     tsl_ind := fun ΣE mp kn mind => 
     ret (tsl_mind_body true (snd ΣE) mp kn mind) |}.

(** registeres the unary parametricity translations as translation instance **)
Instance param : Translation :=
  {| tsl_id := tsl_ident' ;
     tsl_tm := fun ΣE t => ret (tsl_rec1_prune false (snd ΣE) t) ;
     (** Implement and Implement Existing cannot be used with this translation **)
     tsl_ty := None ;
     tsl_ind := fun ΣE mp kn mind => 
     ret (tsl_mind_body false (snd ΣE) mp kn mind) |}.


(** stores translation of definitions **)
(** global context is not important => always use empty_ext [] **)
(** better would be the translated global_reference but 
  this is not accessible from the outside **)
Class translated (ref:global_reference) := 
{
  (** content : term  **) (** would be enough for constant **)
  content : tsl_table (** needed for inductive translations **)
  (** for constants this degenerates to [(ref,contentTerm)] **)
}.

(** lookup a global reference in the translation database and add its
  translation table to the context **)
Definition checkTranslation (ΣE:tsl_context) (ref:global_reference) : TemplateMonad tsl_context :=
      match lookup_tsl_table (snd ΣE) ref with
      | Some _ => ret ΣE
      | None => 
      (** lookup if a translation exists **)
          opt <- tmInferInstance None (translated ref);;
          match opt with (** match over custom option type for inference results **)
          | my_Some x => 
            let Σ' := fst ΣE in
            let E' := ((@content _ x)  ++ (snd ΣE))%list in 
            Σ' <- tmEval lazy Σ' ;;
            E' <- tmEval lazy E' ;;
            ret (Σ', E')
          | my_None => ret ΣE
          end
      end.

(** quotes the environment and adds translations of declarations 
  from it to the context **)
(** for additional creation of missing translations,
use TranslateRec with constructed table as seed **)
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

(** the cases could be all in one and the command with 
  distinction on references/other terms could be a Template command
 **)
Definition getIdentKername' (t:term)  : TemplateMonad kername :=
  tmReturn match t with
  (** handle all cases in one **)
  | tInd (mkInd kername _) _
  | tConst kername _
  | tConstruct (mkInd kername _) _ _ => 
    kername
  | _ => (MPfile [],"") (** dummy value **)
  end.
Definition getIdentKername {A} (t:A)  : TemplateMonad kername :=
  q <- tmQuote t;;
  getIdentKername' (if q is tApp q' _ then q' else q).

(** gets the local identifier (short name) **)
Definition getIdent {A} (t:A)  : TemplateMonad string :=
  kername <- getIdentKername t;;
  tmReturn (snd kername).

(** full mod path and identifier (separated by '.') **)
Definition getIdentComplete {A} (t:A)  : TemplateMonad string :=
  kername <- getIdentKername t;;
  tmReturn (string_of_kername kername).

  (** retrieves a reference from a coq term of a definition **)
Definition tmLookup {A} (t:A) : TemplateMonad global_reference :=
  getIdentComplete t >>= tmLocate1.

(** generates a table with all translations possibly needed for lookup **)
Definition persistentTranslate_prune {A} (t:A) (prune:bool) : TemplateMonad tsl_context :=
  tc <- ConstructTable t;; (** get table **)
  id <- getIdentComplete t;;
  idname <- getIdent t;;
  tmMsg ("Complete Identifier: "^id);;
  tmMsg ("Short Identifier: "^idname);;
  tc' <- (if prune then @Translate param_prune else @Translate param) tc id;; (** translate new definition **)

  gr <- tmLookup t;;
  (** extend table **)
      nameString <- tmEval lazy (append idname "_tableLookup");;
      newName <- tmFreshName nameString;;
      tmDefinition newName (
        {|
            content := snd tc';
        |} : translated gr
      );;
  (** save new table for the translation definition t **)
  tmExistingInstance (VarRef newName);;
  tmReturn tc'
  .

Definition persistentTranslate {A} (t:A) : TemplateMonad tsl_context :=
  persistentTranslate_prune t false.