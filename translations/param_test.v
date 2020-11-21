Load param_unary.


Definition f := Type -> Type.
MetaCoq Run (persistentTranslate f).
Print fᵗ.
(* fun f : Type -> Type => forall H : Type, (H -> Type) -> f H -> Type *)

(* Inductive natᵗ : (fun X : Set => X -> Set) nat :=
	Oᵗ : natᵗ 0
  | Sᵗ : (fun f : nat -> nat => forall H : nat, natᵗ H -> natᵗ (f H)) S. *)

MetaCoq Run (persistentTranslate nat).
Print natᵗ.
MetaCoq Run (persistentTranslate nat).
Print natᵗ0.

MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
MetaCoq Run (TC <- Translate nat_TC "VectorDef.t" ;;(* needs nat *)
                tmDefinition "vec_TC" TC ).
MetaCoq Run (persistentTranslate VectorDef.t).
Print tᵗ.

Print sig.
MetaCoq Run (persistentTranslate sigT).
Print sigTᵗ.

(* translation of sorts *)
Definition type := Type.
MetaCoq Run (Translate emptyTC "type").
Print typeᵗ.
Check (natᵗ:typeᵗ nat).







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



(* Fail Print natᵗ. *)
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
