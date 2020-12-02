Load param_unary.

Definition f := Type -> Type.
MetaCoq Run (persistentTranslate f).
Print fᵗ.
(* fun f : Type -> Type => forall H : Type, (H -> Type) -> f H -> Type *)

MetaCoq Run (persistentTranslate nat).
Print natᵗ.
MetaCoq Run (persistentTranslate nat).
Print natᵗ0.
(* Inductive natᵗ : (fun X : Set => X -> Set) nat :=
	Oᵗ : natᵗ 0
  | Sᵗ : (fun f : nat -> nat => forall H : nat, natᵗ H -> natᵗ (f H)) S. *)

MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
MetaCoq Run (TC <- Translate nat_TC "VectorDef.t" ;;(* needs nat *)
                tmDefinition "vec_TC" TC ).
MetaCoq Run (persistentTranslate VectorDef.t).
Print VectorDef.t.
Print tᵗ.
Print tᵗ0.
Fail Print tᵗ1.

MetaCoq Run (persistentTranslate_prune VectorDef.t true).
Print tᵗ0.
Print tᵗ1.

Print sig.
MetaCoq Run (persistentTranslate sigT).
Print sigTᵗ.

Print list.
MetaCoq Run (persistentTranslate list).
Print listᵗ.

Inductive G X := C (f:nat -> X).
MetaCoq Run (persistentTranslate G).
Print Gᵗ.

Print All2.
(* universe error *)
Fail MetaCoq Run (persistentTranslate All2).

(* translation of sorts *)
Definition type := Type.
MetaCoq Run (Translate emptyTC "type").
Print typeᵗ.
Check (natᵗ:typeᵗ nat).

Fail Print tᵗ2.
MetaCoq Run (persistentTranslate Fin.t).
Print tᵗ2.
Fail Print tᵗ3.
MetaCoq Run (TC <- Translate nat_TC "Fin.t" ;;(* needs nat *)
                tmDefinition "fin_TC" TC ).
Print tᵗ3.

MetaCoq Run (TC <- Translate emptyTC "list" ;;
                tmDefinition "list_TC" TC ).
Inductive rose := node (xs:list rose).
Fail MetaCoq Run (TC <- Translate list_TC "rose" ;;
                tmDefinition "rose_TC" TC ).



