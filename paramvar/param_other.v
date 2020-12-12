(**  **)

(*** ∀∃ and ∃∀ translation expressed by ∃∃ and ∀∀ ***)

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


(** return all false, exactly one non-dummy, lift env **)
(* Fixpoint transformParams (env:Env) (E:tsl_table) (dummy: term) (params:context) : list term*list (list term)*Env:=
  match params with 
  | nil => (nil,nil,env)
  | (mkdecl name _ type as decl)::xs =>
  (fun '(allDummy,xs,env2) =>
  (** add new argument in front **)
    let addF := cons (tRel) in
    (addF allDummy, map addF xs, env2)
  )
(if augment (applyEnv env type) is Some tL then 
    let (allDummy,xs,env2) := transformParams (EnvLift0 (EnvUp env) 1) E xs in
    let addDummyF :=
        (* cons (vass (name_map tsl_ident name) (t')) *)
        cons (vass (name_map tsl_ident name) (tApp dummy [tRel]))
    in
    let t' := subst_app tL [tRel 0] in
    let addF :=
        (* cons (vass (name_map tsl_ident name) (t')) *)
        cons (vass (name_map tsl_ident name) (tRel ))
    in
    (addDummyF allDummy, (addF allDummy)::(map addDummyF xs),env2)
else
    transformParams (EnvUp env) E xs
)
  end.

(** auxiliary function to test parameter transform on ∀ terms **)
Definition paramTermTrans E (t:term) :=
  let (ctx,tb) := decompose_prod_context t in
  let (ctx',env) := transformParams (fun n => n) E ctx in
  it_mkProd_or_LetIn (rev ctx') tb. *)




  (* use more general database and table construction *)

Fixpoint splitList {X} n (xs:list X) :=
  match n,xs with
  | O,xs => ([],xs)
  | S m,x::xs => 
  let (ys1,ys2) := splitList m xs in
  (x::ys1,ys2)
  | _,_ => ([],xs)
  end.

(* Compute (decompose_prod_context (tProd (nNamed "A") (tRel 0) (tProd (nNamed "B") (tRel 0) (tRel 0)))). *)
Definition idEnv (n:nat) := n.

Definition mkAppsInner t xs :=
  match t with
  | tApp tb ys => tApp tb (xs++ys)
  | _ => mkApps t xs
  end.

Fixpoint dummyApply (tb:term) (ctx:context) (paramExtCount indCount:nat) (dummy:term) : term :=
  match ctx with
  | ((mkdecl na body ty) as x)::xs =>
  if augment ty is Some _ then
  (* if eq_decl x y then
    mkApp (dummyApply tb xs paramCount indCount dummy) (tRel (indCount + #|ctxExt|))
  else *)
    mkAppsInner (dummyApply tb xs (paramExtCount-2) indCount dummy) 
        [tRel (indCount + paramExtCount-1);
        (* mkApp dummy (tRel (indCount + paramExtCount-1))] *)
        subst_app dummy [tRel (indCount + paramExtCount-1)]]
  else
    mkAppsInner (dummyApply tb xs (paramExtCount-1) indCount dummy) [tRel (indCount + paramExtCount-1)]
  | _ => mkAppsInner tb (makeRels indCount)
  (* | _ => tb *)
  end.

Definition otherParam {A} (t:A) (na:ident->ident) (refTrans:term) (dummy:term) (conn:term) :=
    id <- getIdent t;;
    q <- tmQuote t;;
    match q with
    | tInd (mkInd ker n) inst =>
      mind <- tmQuoteInductive ker;;
      match nth_error mind.(ind_bodies) n with
      | Some indb => 
          let ty := indb.(ind_type) in
          let (args,tb) := decompose_prod_context ty in
          let (params,indices) := splitList mind.(ind_npars) args in
          let (params',env) := transformParams idEnv params in
          let dummyAppTerm := 
            it_mkLambda_or_LetIn (rev params') 
            (it_mkLambda_or_LetIn (rev indices) 
            (dummyApply refTrans params #|params'| #|indices| dummy))
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
MetaCoq Quote Definition dummyFalse := (fun (X:Type) (x:X) => True). (* simplified *)

Definition existsAllParam {A} (t:A) := 
    id <- getIdent t;;
    na <- tmEval lazy (tsl_ident_unparam id);;
    tm <- getDefTerm na;;
  otherParam t tsl_ident_existsall tm dummyTrue <% sum %>.
Definition allExistsParam {A} (t:A) := 
    id <- getIdent t;;
    na <- tmEval lazy (tsl_ident_exists id);;
    tm <- getDefTerm na;;
  otherParam t tsl_ident_allexists tm dummyFalse <% prod %>.

(* Unset Strict Unquote Universe Mode. *)

(* MetaCoq Unquote Definition test :=
(
(tLambda (nNamed "A")
   (<% Type %>)
   (tLambda (nNamed "Aᴱ")
      (tProd nAnon (tRel 0)
         (<% Type %>))
      (tApp
         (tInd
            {|
            inductive_mind := (MPfile ["param_other"], "listᴱ");
            inductive_ind := 0 |} [])
         [tRel 2;
         tLambda (nNamed "x") (tRel 2) (tInd
                    {|
                    inductive_mind := (MPfile ["Logic"; "Init"; "Coq"],
                                      "True");
                    inductive_ind := 0 |} [])]
      )))).
         tApp
           (tLambda (nNamed "X")
              (<% Type %>)
              (tLambda (nNamed "x") (tRel 0)
                 (tInd
                    {|
                    inductive_mind := (MPfile ["Logic"; "Init"; "Coq"],
                                      "True");
                    inductive_ind := 0 |} []))) [tRel 1]])))

). *)

(* MetaCoq Run (persistentExistsTranslate list).

(* MetaCoq Run (tmQuote (
  fun (X:Type) (Px:X->Type) => listᴱ X (fun (_:X) => True)
) >>= print_nf). *)

MetaCoq Run (allExistsParam list).
Print listᴬᴱ.

Inductive PNT (n:nat) (X:Type) (d:nat) : Type.
MetaCoq Run (persistentExistsTranslate PNT).
MetaCoq Run (allExistsParam PNT).
Print PNTᴬᴱ.

(* Inductive IT (X:Type) : nat -> Type -> Type:= C : IT X 0 nat.
MetaCoq Run (persistentExistsTranslate IT). *)


Inductive IT (X:Type) : Type -> Type:=.
MetaCoq Run (persistentExistsTranslate IT).
MetaCoq Run (allExistsParam IT).
Print ITᴬᴱ. *)

MetaCoq Run (persistentExistsTranslate prod).
MetaCoq Run (allExistsParam prod).
Print prodᴬᴱ.

(* Print VectorDef.t.

MetaCoq Run (persistentExistsTranslate VectorDef.t).
MetaCoq Run (allExistsParam list). *)
