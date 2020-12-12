(**  **)

(*** param_other: ∀∃ and ∃∀ translation expressed by ∃∃ and ∀∀ ***)

From MetaCoq.Template Require Import utils All.
From MetaCoq.Translations Require Import translation_utils param_unary param_exists.
From MetaCoq.Template Require Import Pretty.

Local Infix "<=" := Nat.leb.

(** get a term pointing to a constant from a global reference **)
Definition refToTerm (g:global_reference) : term :=
    match g with
    | VarRef id => tVar id
    | ConstRef kn => tConst kn []
    | IndRef ind => tInd ind []
    | ConstructRef ind n => tConstruct ind n []
    end.

Definition getDefTerm (na:ident) : TemplateMonad term :=
    gr <- tmLocate1 na;;
    tmEval lazy (refToTerm gr).

(** split a list into two parts, xs=ys++zs /\ |ys|=n **)
(** used to split parameter and indices **)
Fixpoint splitList {X} n (xs:list X) :=
  match n,xs with
  | O,xs => ([],xs)
  | S m,x::xs => 
  let (ys1,ys2) := splitList m xs in
  (x::ys1,ys2)
  | _,_ => ([],xs)
  end.

Definition idEnv (n:nat) := n.

(** apply in front **)
Definition mkAppsInner t xs :=
  match t with
  | tApp tb ys => tApp tb (xs++ys)
  | _ => mkApps t xs
  end.

(** returns the translated inductive applied with dummy arguments except for one predicate **)
(** the first return value is where all predicates are instantaited with dummy and the list **)
(** has in each element exactly one predicate which is not instantiated by dummy **)
Fixpoint dummyApply (tb:term) (ctx:context) (paramExtCount indCount:nat) (dummy:term) : term*list term :=
  match ctx with
  | ((mkdecl na body ty) as x)::xs =>
  (** test if the type should be augmented (simplified) **)
  let augmented := if augment ty is Some _ then true else false in
  (** augment remaining params **)
  let (allFalse, termList) := dummyApply tb xs (paramExtCount-(if augmented then 2 else 1)) indCount dummy in
  (** reference to type argument **)
  let argRelNum := indCount + paramExtCount-1 in
  let argRel := tRel argRelNum in
  if augmented then
  (** instantiate with dummy **)
    let dummyExtend t := mkAppsInner t [argRel;subst_app dummy [argRel]] in
    (dummyExtend allFalse, (** extend all dummy **)
      (mkAppsInner allFalse [argRel;tRel (argRelNum-1)]) (** extend with new predicate instantiation **)
      ::(map dummyExtend termList)) (** extend others with dummy **)
  else
    let simpleExtend t := mkAppsInner t [argRel] in
    (** only add normal argument if not augmentable **)
    (simpleExtend allFalse,map simpleExtend termList)
  | _ => (mkAppsInner tb (makeRels indCount),[])
  (** apply all indices in the base case **)
  end.

(** pointwise combination with a connector function **)
Fixpoint combineTerms base (xs:list term) (connF:term->term->term) :=
  match xs with
  | [] => base
  | [x] => x
  | x::xs => connF x (combineTerms base xs connF)
  end.

(** tranform a binary Coq function to a binary MetaCoq function **)
Definition termToComb (conn:term) (t1 t2:term) : term :=
  tApp conn [t1;t2].

(** general parametricity combination from basic translations **)
(** na: name transformation **)
(** refTrans: transformation of inductive type **)
(** dummy: instantiation for predicates not under focus **)
(** conn: connective for singular instantiated terms **)
Definition otherParam {A} (t:A) (na:ident->ident) (refTrans:term) (dummy:term) (conn:term) (base:term) :=
    id <- getIdent t;;
    q <- tmQuote t;;
    match q with
    | tInd (mkInd ker n) inst =>
      mind <- tmQuoteInductive ker;;
      match nth_error mind.(ind_bodies) n with
      | Some indb => 
          let ty := indb.(ind_type) in
          (** retrieve arguments from type information **)
          let (args,tb) := decompose_prod_context ty in
          (** split into parameters and indices by count of mutual inductive type **)
          let (params,indices) := splitList mind.(ind_npars) args in
          (** transform parameters with function from exists (is pruned unary parametricity) **)
          let (params',env) := transformParams idEnv params in
          (** apply with singular predicate **)
          (** S indices for instance of inductive type **)
          let (allDummy,uniP) := dummyApply refTrans params #|params'| (S #|indices|) dummy in
          let dummyAppTerm := 
            it_mkLambda_or_LetIn (rev params') 
            (it_mkLambda_or_LetIn (rev indices) 
            (tLambda nAnon (** instance of ind type **)
            (** lifted params (env lifting for transformation), lifted over indices **)
              (mkApps (lift0 #|indices| (applyEnv env (tApp q (makeRels mind.(ind_npars))))) (makeRels #|indices|))
              (** combined using conn **)
            (combineTerms base uniP (termToComb conn)))
            )
          in
          print_nf dummyAppTerm;;
          tmMkDefinition (na id) dummyAppTerm
      | None => tmFail ""
      end
    | _ => tmFail ""
    end.

Definition tsl_ident_allall id := id^"ᴬᴬ".
Definition tsl_ident_existsexists id := id^"ᴱᴱ".
Definition tsl_ident_allexists id := id^"ᴬᴱ".
Definition tsl_ident_existsall id := id^"ᴱᴬ".

MetaCoq Quote Definition dummyTrue := (fun (X:Type) (x:X) => True). (* simplified *)
MetaCoq Quote Definition dummyFalse := (fun (X:Type) (x:X) => False). (* simplified *)

(** ∃∀ = V ∀∀ with ⊤ for predicates **)
Definition existsAllParam {A} (t:A) := 
    id <- getIdent t;;
    na <- tmEval lazy (tsl_ident_unparam id);;
    tm <- getDefTerm na;;
  otherParam t tsl_ident_existsall tm dummyTrue <% sum %> <% False %>.
(** ∀∃ = Λ ∃∃ with ⊥ for predicates **)
Definition allExistsParam {A} (t:A) := 
    id <- getIdent t;;
    na <- tmEval lazy (tsl_ident_exists id);;
    tm <- getDefTerm na;;
  otherParam t tsl_ident_allexists tm dummyFalse <% prod %> <% True %>.
