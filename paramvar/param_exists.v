(**  **)

(*** param_exists: ∃∃ translation of inductive types ***)
From MetaCoq.Template Require Import utils All.
From MetaCoq.Translations Require Import translation_utils param_unary.
From MetaCoq.Template Require Import Pretty.

Local Infix "<=" := Nat.leb.

Definition default_term := tVar "constant_not_found".
Definition debug_term msg:= tVar ("debug: " ^ msg).


Definition tsl_ident_exists id := id^"ᴱ".
Definition tsl_ident := tsl_ident_exists.

(***
application of a lifting environment to a term
under binders the given environment is transformed using up
**)
Definition applyEnv := tsl_rec0_2.

From MetaCoq Require Import Checker.
(** Checker for eq_term **)
(** checker is already required for translation utils **)
Existing Instance config.default_checker_flags.

(** simpler version of parametricity translation
transforms a type parameter into a unary predicate
 **)
Fixpoint augment (t:term) : option term :=
  match t with 
  | tSort u => Some (tLambda nAnon t (tProd nAnon (tRel 0) t))
  | tProd na t1 t2 => 
    if augment t2 is Some t2' then
    (Some
    (tLambda na t
    (lift0 1 (tProd na t1
      (if augment t1 is Some t1' then
        tProd na (lift0 1 t1') (subst_app(lift0 1 t2') [tApp (tRel 2) [tRel 0]])
      else
        subst_app t2' [tApp (tRel 1) [tRel 0]])))
    ))
    else None
  | _ => None
  end.

Definition on_fst {X Y Z} (f:X->Z) (p:X*Y) := match p with (x,y) => (f x,y) end.

Definition name_map f (na:name) := if na is nNamed id then nNamed (f id) else nAnon.

(** transforms a list of parameters and add new ones (the predicates) if possible **)
Fixpoint transformParams (env:Env) (params:context) : context*Env :=
  match params with 
  | nil => (nil,env)
  | (mkdecl name _ type as decl)::xs =>
    on_fst (cons (vass name (applyEnv env type)))
    (if augment (applyEnv env type) is Some tL then 
      let t' := subst_app tL [tRel 0] in
      on_fst (cons (vass (name_map tsl_ident name) (t'))) (transformParams (EnvLift0 (EnvUp env) 1) xs)
    else 
      transformParams (EnvUp env) xs)
  end.

(** auxiliary function to test parameter transform on ∀ terms **)
Definition paramTermTrans (E:tsl_table) (t:term) :=
  let (ctx,tb) := decompose_prod_context t in
  let (ctx',env) := transformParams (fun n => n) ctx in
  it_mkProd_or_LetIn (rev ctx') tb.

(** auxiliary function to apply all parameters in correct order **)
Fixpoint makeRels (n:nat) :=
  match n with 
  | O => []
  | S m => tRel m::makeRels m 
  end.

(** removed n elements from the front, 
useful to delete parameter application
and only keep indices **)
Fixpoint cutList {X} n (xs:list X) :=
  match n with 
  | O => xs
  | S m => tl (cutList m xs)
  end.

(** delete n application from a term **)
Definition removeApps n t :=
  if t is tApp tb args then mkApps tb (cutList n args) else t.

(** ∃ dual to ∀ construct used to simplify creation of ∃ x. Pₓ x **)
Definition tExists na t1 t2 :=
  tApp (<% @sigT %>) [t1;tLambda na t1 t2].

(** transformation of a constructor argument **)
Fixpoint tsl_rec1' (E : tsl_table) (oldParamCount argCount:nat) (rec:term) (recInd:inductive) (t : term) : option term :=
  let debug case symbol :=
      debug_term ("tsl_rec1: " ^ case ^ " " ^ symbol ^ " not found") in
  match t with
  | tRel (S n) => 
  (** X → Pₓ **)
  (** all arguments with parameter type x:X are replaced by Pₓ **)
  (** possible because the structure is `Inductive T (X:Type) (Pₓ:X→Type)` **)
    if leb argCount n then
      Some (tRel (n))
    else None

  | tInd ind inst => 
    (** ind → ∃∃ind **)
    if eq_inductive ind recInd then 
    (** recursive type is replaced by recursive instance (parameters are handeled by tApp)  **)
      Some rec else  
    (lookup_tsl_table E (IndRef ind) )
    (** otherwise lookup the inductive type (parameters are handeled by tApp) **)

  | tApp tb args => 
    if tsl_rec1' E oldParamCount argCount rec recInd tb is Some r then
    (** translate body first => r **)
      Some (mkApps r (concat (map (fun a => 
      (** for each argument add possible translation **)
        if tsl_rec1' E oldParamCount argCount rec recInd a is Some ra then
        [a;ra] (** B A → B' A A' **)
        else [a] (** B A → B' A **)
      ) args)))
    else None
  | tProd na t1 t2 => 
  (** ∀ x:A. B → λ (f:∀x:A. B). ∃ x:A. B (f x) **)
  if tsl_rec1' E oldParamCount argCount rec recInd t2 is Some r then
    Some (tLambda nAnon t (
      tExists na (lift0 1 t1) (** universe problems **)
      (
        subst_app (lift0 1 r) [tApp (tRel 1) [tRel 0]]
      )
    ))
  else None
  | _ => None
  end.

(** general function to fill in redundant information **)

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
  set(paramlist_env := on_fst rev (transformParams (fun n => n) (rev mind.(ind_params)))).
  destruct paramlist_env as [paramlist env].
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
      refine (
        let (ctx,tb) := decompose_prod_context (remove_arity mind.(ind_npars) ind.(ind_type)) in
        it_mkProd_or_LetIn paramlist (
          it_mkProd_or_LetIn ctx (** indices **)
          (tProd nAnon 
          (mkApps (lift0 #|ctx| (applyEnv env (tApp (tInd (mkInd kn i) []) (makeRels mind.(ind_npars))))) (makeRels #|ctx|)) (** old type with params **)
            (lift0 1 tb))) (** later tProd element **)
      ).
    + (** constructors **)
      (** definition as function for better control flow overview **)
      refine (concat _).
    refine(
      mapi 
      (
        fun k '((name,typ,nargs)) => 
        let typInd :=  (** fillin inductives for recursion **)
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
        (** apply new params => remove old app add new **)
        let recInst := tRel (#|paramlist| + #|args|) in
        let tbNewParams :=
          mkApps recInst (map (lift0 #|args|) (makeRels #|paramlist|))
        in
        let tbNewIndApp :=
          (if tb is (tApp tI appargs) then
          (** tI was replace by ind filling **)
            mkApps tbNewParams (cutList mind.(ind_npars) appargs)
          else recInst)
        in
        let tb' := mkApp tbNewIndApp inst in
        let na := tsl_ident name in
        _)
      ind.(ind_ctors)
    ).
    refine(
        rev(fold_left_i
        (fun acc j arg => 
          (** rec is already replaced **)
          let rec := recInst in
          (** augment argument **)
          let augArgO := tsl_rec1' E mind.(ind_npars) #|args| rec (mkInd kn i) (lift0 (#|args| - j) (decl_type arg)) in
          if augArgO is Some augArgP then
          (** apply with argument **)
          let augArg := subst_app augArgP [tRel (#|args| - S j)] in
          (let ctor_type := 
          it_mkProd_or_LetIn paramlist (
          it_mkProd_or_LetIn (rev args) (
            tProd nAnon augArg
            (lift0 1 tb')
          )) in
          (** name constructor **)
          (na^(string_of_nat j), 
          ctor_type, 
          #|fst (decompose_prod_context ctor_type)| - #|paramlist|)
          :: acc)
          else acc
        ) args [])
    ).
Defined.

(** removed the modpath in front of the identifier **)
Definition tsl_ident' id := tsl_ident(fst(lastPart id)).

(** registeres the exists parametricity translations as translation instance **)
Instance existparam : Translation :=
  {| tsl_id := tsl_ident' ;
     tsl_tm := fun ΣE t => ret (paramTermTrans (snd ΣE) t);
     (** Implement and Implement Existing cannot be used with this translation **)
     tsl_ty := None ;
     tsl_ind := fun ΣE mp kn mind => 
     ret (tsl_mind_body false (snd ΣE) mp kn mind) |}.


(** code similar to param_unary => TODO: unify both code snippets **)


(** stores translation of definitions **)
(** global context is not important => always use empty_ext [] **)
(** better would be the translated global_reference but 
  this is not accessible from the outside **)
Class existtranslated (ref:global_reference) := 
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
          opt <- tmInferInstance None (existtranslated ref);;
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
Definition ConstructExistsTable {A} (t:A) : TemplateMonad tsl_context :=
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
Definition persistentExistsTranslate {A} (t:A) : TemplateMonad tsl_context :=
  tc <- ConstructExistsTable t;; (** get table **)
  id <- getIdentComplete t;;
  idname <- getIdent t;;
  tmMsg ("Complete Identifier: "^id);;
  tmMsg ("Short Identifier: "^idname);;
  tc' <- (@Translate existparam) tc id;; (** translate new definition **)

  gr <- tmLookup t;;
  (** extend table **)
      nameString <- tmEval lazy (append idname "_tableLookup");;
      newName <- tmFreshName nameString;;
      tmDefinition newName (
        {|
            content := snd tc';
        |} : existtranslated gr
      );;
  (** save new table for the translation definition t **)
  tmExistingInstance (VarRef newName);;
  tmReturn tc'
  .

Definition persistentTranslate {A} (t:A) : TemplateMonad tsl_context :=
  persistentExistsTranslate t.