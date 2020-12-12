(** **)

(*** param_test: tests for unary parametricity translation ***)

Load param_unary.

Definition f := Type -> Type.
MetaCoq Run (persistentTranslate f).
Print fᵗ.
(** fun f : Type -> Type => forall H : Type, (H -> Type) -> f H -> Type **)

MetaCoq Run (persistentTranslate nat).
Print natᵗ.
MetaCoq Run (persistentTranslate nat).
Print natᵗ0. (** makeFresh testing **)
(** Inductive natᵗ : (fun X : Set => X -> Set) nat :=
	Oᵗ : natᵗ 0
  | Sᵗ : (fun f : nat -> nat => forall H : nat, natᵗ H -> natᵗ (f H)) S. 
  **)

MetaCoq Run (TC <- Translate emptyTC "nat" ;;
                tmDefinition "nat_TC" TC ).
MetaCoq Run (TC <- Translate nat_TC "VectorDef.t" ;;(** needs nat **)
                tmDefinition "vec_TC" TC ).
MetaCoq Run (persistentTranslate VectorDef.t).
Print VectorDef.t.
Print tᵗ.
Print tᵗ0.
Fail Print tᵗ1.

(** persistent finds the correct translations **)
MetaCoq Run (persistentTranslate_prune VectorDef.t true).
Print tᵗ0.
Print tᵗ1.

Print sig.
MetaCoq Run (persistentTranslate sigT).
Print sigTᵗ.
(**
Inductive
sigTᵗ (A : Type) (Aᵗ P : A -> Type) (Pᵗ : forall H : A, Aᵗ H -> P H -> Type)
  : (∑ y, P y) -> Type :=
	existTᵗ : forall (x : A) (xᵗ : Aᵗ x) (H : P x),
              Pᵗ x xᵗ H -> sigTᵗ A Aᵗ P Pᵗ (x; H)

sigTᵗ is a predicate on sigT proofs:
take a type A and predicates At on A
take a predicate for the element P
and a predicate on Pt proofs of P:
  on related elements on H (here on elements satisfying At)
  the proofs have to fulfill Pt
**)

Print list.
MetaCoq Run (persistentTranslate list).
Print listᵗ.

(**

Inductive listᵗ (A : Type) (Aᵗ : A -> Type) : list A -> Type :=
	nilᵗ2 : listᵗ A Aᵗ []
  | consᵗ2 : forall H : A,
             Aᵗ H ->
             forall H0 : list A, listᵗ A Aᵗ H0 -> listᵗ A Aᵗ (H :: H0)

a predicate on lists
every element in the list fulfills At
**)

Inductive G X := C (f:nat -> X).
MetaCoq Run (persistentTranslate G).
Print Gᵗ.

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

Inductive List (X:Set) : Set := nil | cons (x:X) (xs:List X).
Inductive rose : Set := node (xs:List rose).

MetaCoq Run (persistentTranslate List).
MetaCoq Run (persistentTranslate rose).
Print roseᵗ.
(**

Inductive roseᵗ : rose -> Set :=
	nodeᵗ : forall xs : List rose, Listᵗ rose roseᵗ xs -> roseᵗ (node xs)

**)