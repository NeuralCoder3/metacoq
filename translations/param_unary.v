(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils All.
From MetaCoq.Translations Require Import translation_utils.

Local Infix "<=" := Nat.leb.

Definition default_term := tVar "constant_not_found".
Definition debug_term msg:= tVar ("debug: " ^ msg).

(* lifts everything after n *)
(* morally identity *)
Fixpoint tsl_rec0 (n : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if n <= k then tRel (2*k-n+1) else t
  | tEvar k ts => tEvar k (map (tsl_rec0 n) ts)
  | tCast t c a => tCast (tsl_rec0 n t) c (tsl_rec0 n a)
  | tProd na A B => tProd na (tsl_rec0 n A) (tsl_rec0 (n+1) B)
  | tLambda na A t => tLambda na (tsl_rec0 n A) (tsl_rec0 (n+1) t)
  | tLetIn na t A u => tLetIn na (tsl_rec0 n t) (tsl_rec0 n A) (tsl_rec0 (n+1) u)
  | tApp t lu => tApp (tsl_rec0 n t) (map (tsl_rec0 n) lu)
  | tCase ik t u br => tCase ik (tsl_rec0 n t) (tsl_rec0 n u)
                            (map (fun x => (fst x, tsl_rec0 n (snd x))) br)
  | tProj p t => tProj p (tsl_rec0 n t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

Print lift0.

Fixpoint tsl_rec1 (E : tsl_table) (t : term) : term :=
  let debug case symbol :=
      debug_term ("tsl_rec1: " ^ case ^ " " ^ symbol ^ " not found") in
  match t with
  | tLambda na A t =>
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    tLambda na A0 (tLambda (tsl_name tsl_ident na)
                           (subst_app (lift0 1 A1) [tRel 0])
                           (tsl_rec1 E t))
  | t => let t1 :=
  match t with
  | tRel k => tRel (2 * k)
  | tSort s => tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))
  (* | tSort s => tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) <% Type %>) *)

  | tProd na A B =>
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    let B0 := tsl_rec0 1 B in
    let B1 := tsl_rec1 E B in
    let ΠAB0 := tProd na A0 B0 in
    tLambda (nNamed "f") ΠAB0
      (tProd na (lift0 1 A0)
             (tProd (tsl_name tsl_ident na)
                    (subst_app (lift0 2 A1) [tRel 0])
                    (subst_app (lift 1 2 B1)
                               [tApp (tRel 2) [tRel 1]])))
  | tApp t us =>
    let us' := concat (map (fun v => [tsl_rec0 0 v; tsl_rec1 E v]) us) in
    mkApps (tsl_rec1 E t) us'

  | tLetIn na t A u =>
    let t0 := tsl_rec0 0 t in
    let t1 := tsl_rec1 E t in
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    let u0 := tsl_rec0 0 u in
    let u1 := tsl_rec1 E u in
    tLetIn na t0 A0 (tLetIn (tsl_name tsl_ident na) (lift0 1 t1)
                            (subst_app (lift0 1 A1) [tRel 0]) u1)

  | tCast t c A => let t0 := tsl_rec0 0 t in
                  let t1 := tsl_rec1 E t in
                  let A0 := tsl_rec0 0 A in
                  let A1 := tsl_rec1 E A in
                  tCast t1 c (mkApps A1 [tCast t0 c A0]) (* apply_subst ? *)

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
  | tCase ik t u brs as case =>
    let brs' := List.map (on_snd (lift0 1)) brs in
    let case1 := tCase ik (lift0 1 t) (tRel 0) brs' in
    match lookup_tsl_table E (IndRef (fst ik)) with
    (* | Some (tInd i _univ) =>
      tCase (i, (snd ik) * 2)%nat
            (tsl_rec1_app (Some (tsl_rec0 0 case1)) E t)
            (tsl_rec1 E u)
            (map (on_snd (tsl_rec1 E)) brs) *)
    | _ => debug "tCase" (match (fst ik) with mkInd s _ => string_of_kername s end)
    end
  | tProj _ _ => todo "tsl"
  | tFix _ _ | tCoFix _ _ => todo "tsl"
  | tVar _ | tEvar _ _ => todo "tsl"
  | tLambda _ _ _ => tVar "impossible"
  end in
  t1
  end.
  (* match app with Some t' => mkApp t1 (t' {3 := tRel 1} {2 := tRel 0})
               | None => t1 end
  end. *)
(* Definition tsl_rec1 := tsl_rec1_app None. *)

MetaCoq Run (tmQuote nat >>= tmPrint).
MetaCoq Run (tmQuoteInductive (MPfile ["Datatypes"; "Init"; "Coq"], "nat") >>= tmPrint).

Inductive E (X:Type) (h: list X) := .
MetaCoq Run (tmQuote E >>= tmPrint).
MetaCoq Run (tmQuoteInductive (MPfile ["param_unary"], "E") >>= tmPrint).


Definition plist :=
[{|
	           decl_name := nNamed "h";
               decl_body := None;
               decl_type := tApp
                              (tInd
                                 {|
                                 inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"; "Init"; "Coq"],
                                                 "list");
                                 inductive_ind := 0 |} []) [
                              tRel 0] |};
              {|
              decl_name := nNamed "X";
              decl_body := None;
              decl_type := tSort
                             (Universe.from_kernel_repr
                                (Level.Level "param_unary.1122", false) []) |}].

Print context_decl.
Check vass.

Fixpoint remove_lambda (t : term) : term :=
  match t with
  | tLambda _ _ B => remove_lambda B
  | _ => t
  end.

Fixpoint decompose_prod_context (t : term) : context * term :=
  match t with
  | tProd n A B => let (Cs, B) := decompose_prod_context B in
                  (vass n A :: Cs, B)
  | _ => ([], t)
  end.

Compute (
let paramType := it_mkProd_or_LetIn plist <% Type %> in (* does Type always work *)
    let transformRel := tsl_rec1 [] paramType in
    let prods := fst(decompose_prod_context (remove_lambda transformRel)) in
    tl(rev prods)
    (* transformRel *)
  ).
Compute (
let paramType := it_mkProd_or_LetIn [] <% Type %> in (* does Type always work *)
    let transformRel := tsl_rec1 [] paramType in
    let prods := fst(decompose_prod_context (remove_lambda transformRel)) in
    tl(rev prods)
    (* rev prods *)
    (* transformRel *)
  ).


MetaCoq Run (tmQuote le>>= tmPrint).
From MetaCoq.Template Require Import Pretty.
(* print_term *)
MetaCoq Run (tmQuoteInductive (MPfile ["Peano"; "Init"; "Coq"], "le") >>= tmPrint).

Definition transformParams (E:tsl_table) (params:context) : context :=
    (let paramType := it_mkProd_or_LetIn params <% Type %> in (* does Type always work *)
    let transformRel := tsl_rec1 E paramType in
    let prods := fst(decompose_prod_context (remove_lambda transformRel)) in
    tl (rev prods)).

Definition tsl_mind_body (E : tsl_table) (mp : modpath) (kn : kername)
           (mind : mutual_inductive_body) : tsl_table * list mutual_inductive_body.
  set(
    paramlist := transformParams E mind.(ind_params)
    (* (let paramType := it_mkProd_or_LetIn mind.(ind_params) <% Type %> in (* does Type always work *)
    let transformRel := tsl_rec1 E paramType in
    let prods := fst(decompose_prod_context (remove_lambda transformRel)) in
    tl (rev prods)) *)
  ).
  refine (_, [{| ind_npars := #|paramlist|;
                 ind_params := paramlist;
  (* refine (_, [{| ind_npars := 2*mind.(ind_npars);
                 ind_params := mind.(ind_params) ++ mind.(ind_params); *)
                 ind_bodies := _;
                 ind_universes := mind.(ind_universes);
                 ind_variance := mind.(ind_variance)|}]).
  - refine (let kn' : kername := (mp, tsl_ident kn.2) in
            fold_left_i (fun E i ind => _ :: _ ++ E) mind.(ind_bodies) []).
    + (* ind *)
      exact (IndRef (mkInd kn i), tInd (mkInd kn' i) []).
    + (* ctors *)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd kn i) k, tConstruct (mkInd kn' i) k []).
  - exact mind.(ind_finite).
  - refine (mapi _ mind.(ind_bodies)).
    intros i ind.
    refine {| ind_name := tsl_ident ind.(ind_name);
              ind_type := _;
              ind_kelim := ind.(ind_kelim);
              ind_ctors := _;
              ind_projs := [] |}. (* UGLY HACK!!! todo *)
    + (* arity  *)
      refine (let ar := subst_app (tsl_rec1 E ind.(ind_type))
                                  [tInd (mkInd kn i) []] in
              ar).
    + (* constructors *)
    refine(
      mapi 
      (
        fun k '((name,typ,nargs)) => 
        (tsl_ident name,
        subst_app 
          (fold_left_i 
            (fun t0 i u  => t0 {S i := u}) 
            (rev (mapi (fun i _ => tInd (mkInd kn i) [])
                              mind.(ind_bodies)))
            (tsl_rec1 E typ))
         [tConstruct (mkInd kn i) k []],
        (2*nargs)%nat) (* todo counting *)
        (* ,#|transformParams (fst(collect_prods nargs (type)))|) *)
      )
      ind.(ind_ctors)
    ).
      (* refine (mapi _ ind.(ind_ctors)).
      intros k ((name, typ), nargs).
      refine (tsl_ident name, _, 2 * nargs)%nat.
      refine (subst_app _ [tConstruct (mkInd kn i) k []]).
      refine (fold_left_i (fun t0 i u  => t0 {S i := u}) _ (tsl_rec1 E typ)).
      (* [I_n-1; ... I_0] *)
      refine (rev (mapi (fun i _ => tInd (mkInd kn i) [])
                              mind.(ind_bodies))). *)
Defined.

(* Unset Strict Unquote Universe Mode. *)
MetaCoq Run (typ <- tmQuote (forall A, A -> A) ;;
                     typ' <- tmEval all (tsl_rec1 [] typ) ;;
                     tm <- tmQuote (fun A (x : A) => x) ;;
                     tm' <- tmEval all (tsl_rec1 [] tm) ;;
                     tmUnquote (tApp typ' [tm]) >>= tmDebug).

Print Translation.
Print tsl_context.
Print tsl_table.
Print Translate.

Print string.
Print Ascii.ascii.
(* Search Ascii.ascii. *)

Definition dot : Ascii.ascii.
set(s:=".").
assert (s=".")by trivial.
destruct s;[discriminate H|assumption].
Defined.

(* last part after dot *)
Search "eq" Ascii.ascii.
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

  
Definition tsl_ident' id := tsl_ident(fst(lastPart id)).

Instance param : Translation :=
  {| tsl_id := tsl_ident' ;
     tsl_tm := fun ΣE t => ret (tsl_rec1 (snd ΣE) t) ;
     (* Implement and Implement Existing cannot be used with this translation *)
     tsl_ty := None ;
     tsl_ind := fun ΣE mp kn mind => 
     ret (tsl_mind_body (snd ΣE) mp kn mind) |}.


Check tsl_ind.
Check tsl_mind_body.
Print tsl_ident.

(* MetaCoq Run (if true then tmPrint "A" else tmPrint "B").
MetaCoq Run (monad_iter (fun _ => tmPrint "0";;if true then tmPrint "A" else tmPrint "B") [1;2;3]). *)


(* global context not important => use empty_ext [] *)
(* better would be the translated global_reference but 
this is not accessible from the outside *)
Class translated (ref:global_reference) := 
{
  (* content : term  *) (* enough for constant *)
  content : tsl_table (* needed for inductive *)
  (* for constants [(ref,contentTerm)] *)
}.

Check tmInferInstance.
Print option_instance.
Print monomorph_globref_term.

Check @content.
MetaCoq Run (tmQuoteRec nat >>= tmPrint).

Definition checkTranslation (ΣE:tsl_context) (ref:global_reference) : TemplateMonad tsl_context :=
      match lookup_tsl_table (snd ΣE) ref with
      | Some _ => ret ΣE
      | None => 
          opt <- tmInferInstance None (translated ref);;
          match opt with
          | my_Some x => 
            let Σ' := fst ΣE in
            (* for constants *)
            (* let E' := (ConstRef kn, @content _ x) :: (snd ΣE) in *)
            let E' := (@content _ x)  ++ (snd ΣE) in
            Σ' <- tmEval lazy Σ' ;;
            E' <- tmEval lazy E' ;;
            ret (Σ', E')
          | my_None => ret ΣE
          end
      end.

(* for additional creation use TranslateRec with constructed table as seed *)
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

  Check Translate.
  Print program.
  Print tmLocate1.
  Check tmUnquote. (* term -> unquoted *)
  (* Check tConst. *)

Check mkInd.
Check inductive_mind.

Print kername.

(* this should in an ideal implementation be all in one *)
Definition getIdent {A} (t:A)  : TemplateMonad string :=
  q <- tmQuote t;;
  tmReturn match q with
  (* | tInd (mkInd (_,id) _) _
  | tConst (_,id) _
  | tConstruct (mkInd (_,id) _) _ _ => id *)
  (* needs modpath *)
  | tInd (mkInd kername _) _
  | tConst kername _
  | tConstruct (mkInd kername _) _ _ => 
    snd kername
  | _ => ""
  end.

Definition getIdentComplete {A} (t:A)  : TemplateMonad string :=
  q <- tmQuote t;;
  tmReturn match q with
  (* | tInd (mkInd (_,id) _) _
  | tConst (_,id) _
  | tConstruct (mkInd (_,id) _) _ _ => id *)
  (* needs modpath *)
  | tInd (mkInd kername _) _
  | tConst kername _
  | tConstruct (mkInd kername _) _ _ => 
    string_of_kername kername
  | _ => ""
  end.

  (* Check inductive_mind. *)
  (* Search kername. *)

  (* Search modpath.
  Check MPfile. *)

  MetaCoq Run (
    let t := VectorDef.t in
    q <- tmQuote t;;
    tmPrint q;;
    id <- getIdent t;;
    print_nf id
    (* gr <- tmLocate1 "nat";; *)
    (* tmUnquote gr *)
    (* tmPrint gr *)
    ).

    (* needs global reference (see locate in Translate) *)
    Check tmExistingInstance.
    Print global_reference.
    Check tmDefinition.
    Check tmFreshName.

    Print TemplateMonad.


Definition persistentTranslate {A} (t:A) : TemplateMonad tsl_context :=
  (* let tc := emptyTC in *)
  tc <- ConstructTable t;;
  id <- getIdentComplete t;; (* does not work for local things *)
  idname <- getIdent t;;
  print_nf idname;;
  print_nf id;;
  tc' <- Translate tc id;;

  gr <- tmLocate1 id;; (* is like translate, but mayb own function using t? *)
  (* extend table *)
  (* TODO: too large only needs new part *)
      nameString <- tmEval lazy (append idname "_tableLookup");;
      newName <- tmFreshName nameString;; (* T_inst *)
      tmDefinition newName (
        {|
            content := snd tc';
        |} : translated gr
      );;

  tmExistingInstance (VarRef newName);;
  (* print_nf tc';; *)
  tmReturn tc'
  (* ret tc *)
  .


Definition f := Type -> Type.

(* MetaCoq Run (tmLocate1 "param_unary.f" >>= tmPrint). *)

(* Print kername.
Print modpath.
Search kername.
MetaCoq Run (tmQuote VectorDef.t >>= tmPrint). 
MetaCoq Run (tmQuote f >>= tmPrint).  *)

(* MetaCoq Run (TC <- Translate emptyTC "param_unary.f" ;;
                tmDefinition "list_TC" TC ). *)
MetaCoq Run (persistentTranslate f).
Print fᵗ.
(* fun f : Type -> Type => forall H : Type, (H -> Type) -> f H -> Type *)



Fail Print natᵗ.
(* Compute ltac:(lindebugger(persistentTranslate nat)). *)
MetaCoq Run (persistentTranslate nat).
Print natᵗ.
MetaCoq Run (persistentTranslate nat).
Print natᵗ0.

MetaCoq Run (persistentTranslate VectorDef.t).
Print tᵗ.


(* Compute ltac:(debugger (persistentTranslate sigT)). *)
MetaCoq Run (persistentTranslate sigT).
Print sigTᵗ.





MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
Print natᵗ.
MetaCoq Run (TC <- Translate emptyTC "list" ;;
                tmDefinition "list_TC" TC ).
Print listᵗ.
Check Translate.
Print tsl_context.
Print emptyTC.
Definition nat_TC' := (empty_ext [], snd nat_TC).
Print tsl_table.
Print nat_TC.
Print add_global_decl.
Print global_decl.

MetaCoq Run (TC <- Translate nat_TC "VectorDef.t" ;;(* needs nat *)
                tmDefinition "vec_TC" TC ).
Print vec_TC.

Check tmInferInstance.
Print option_instance.
Check tmQuoteRec.
Print program.
Print global_decl.
Print ConstantDecl.
Print lookup_tsl_table.


MetaCoq Run (TC <- Translate nat_TC "VectorDef.t" ;;(* needs nat *)
                tmDefinition "vec_TC2" TC ).
Print tᵗ.
MetaCoq Run (TC <- Translate nat_TC "Fin.t" ;;(* needs nat *)
                tmDefinition "fin_TC" TC ).
Print tᵗ0.


Inductive rose := node (xs:list rose).
(* MetaCoq Run (TC <- Translate list_TC "rose" ;;
                tmDefinition "rose_TC" TC ). *)

Unset Strict Unquote Universe Mode. 
Definition roseTMC :=
{|
ind_finite := Finite;
ind_npars := 0;
ind_params := [];
ind_bodies := [{|
	           ind_name := "roseᵗ";
               ind_type := tProd nAnon
                             (tInd
                                {|
                                inductive_mind := (
                                                 MPfile ["param_unary"],
                                                 "rose");
                                inductive_ind := 0 |} [])
                                <% Type %>;
                             (* (tSort
                                {|
                                Universe.t_set := {|
                                                 UnivExprSet.this := [UnivExpr.npe
                                                 (NoPropLevel.lSet, false)];
                                                 UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                 (UnivExpr.npe
                                                 (NoPropLevel.lSet, false)) |};
                                Universe.t_ne := eq_refl |}); *)
               ind_kelim := InType;
               ind_ctors := [("nodeᵗ",
                             tProd (nNamed "xs")
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"; "Init"; "Coq"],
                                                 "list");
                                     inductive_ind := 0 |} [])
                                  [tInd
                                     {|
                                     inductive_mind := (
                                                 MPfile ["param_unary"],
                                                 "rose");
                                     inductive_ind := 0 |} []])
                               (tProd (nNamed "xsᵗ")
                                  (tApp
                                     (tInd
                                        {|
                                        inductive_mind := (
                                                 MPfile ["param_unary"],
                                                 "listᵗ");
                                        inductive_ind := 0 |} [])
                                     [tInd
                                        {|
                                        inductive_mind := (
                                                 MPfile ["param_unary"],
                                                 "rose");
                                        inductive_ind := 0 |} []; 
                                     tRel 1; tRel 0])
                                  (tApp (tRel 2)
                                     [tApp
                                        (tConstruct
                                           {|
                                           inductive_mind := (
                                                 MPfile ["param_unary"],
                                                 "rose");
                                           inductive_ind := 0 |} 0 [])
                                        [tRel 1]])), 2)];
               ind_projs := [] |}];
ind_universes := Monomorphic_ctx
                   ({|
                    LevelSet.this := [];
                    LevelSet.is_ok := LevelSet.Raw.empty_ok |},
                   {|
                   ConstraintSet.this := [(Level.lSet, ConstraintType.Le,
                                          Level.Level "Coq.Init.Datatypes.54")];
                   ConstraintSet.is_ok := ConstraintSet.Raw.add_ok (s:=[])
                                            (Level.lSet, ConstraintType.Le,
                                            Level.Level
                                              "Coq.Init.Datatypes.54")
                                            ConstraintSet.Raw.empty_ok |});
ind_variance := None |}.

Compute (mind_body_to_entry roseTMC).
MetaCoq Run (tmMkInductive' roseTMC).
Print tmMkInductive'.


Definition T := forall A, A -> A.
MetaCoq Run (Translate emptyTC "T").


Definition tm := ((fun A (x:A) => x) (Type -> Type) (fun x => x)).
MetaCoq Run (Translate emptyTC "tm").

MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                     tmDefinition "nat_TC" TC ).

MetaCoq Run (TC <- Translate nat_TC "bool" ;;
                     tmDefinition "bool_TC" TC ).
Import Init.Nat.
MetaCoq Run (Translate bool_TC "pred").

