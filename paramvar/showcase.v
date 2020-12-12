(**  **)

(*** showcase: showcase of feature of the translation ***)
From MetaCoq.Translations Require Import param_all.
Unset Strict Unquote Universe Mode.




MetaCoq Run Derive Translations for nat.
(** Derived natᵗ=natᴬᴬ, natᴬᴱ, natᴱᴬ, and natᴱ=natᴱᴱ. **)
Print natᵗ. (** natᴬᴬ **) (** True **)
Print natᴬᴱ. (** True **)
Print natᴱᴬ. (** False **)
Print natᴱ. (** natᴱᴱ **) (** False **)
(**
Inductive natᵗ : nat -> Set :=
	Oᵗ : natᵗ 0 | Sᵗ : forall H : nat, natᵗ H -> natᵗ (S H)

natᴬᴱ = fun _ : nat => True
	 : nat -> Prop

natᴱᴬ = fun _ : nat => False
	 : nat -> Prop

Inductive natᴱ : nat -> Set :=  Sᴱ0 : forall H : nat, natᴱ H -> natᴱ (S H)
**)








MetaCoq Run Derive Translations for list.
(** Derived listᵗ=listᴬᴬ, listᴬᴱ, listᴱᴬ, and listᴱ=listᴱᴱ. **)
Print listᵗ. (** listᴬᴬ **) (** for all a:A holds A^t **)
Print listᴬᴱ. (** =listEE **)
Print listᴱᴬ. (** =liftAA **)
Print listᴱ. (** listᴱᴱ **) (** at least one element fulfills the predicate **)
(**
Inductive listᵗ (A : Type) (Aᵗ : A -> Type) : list A -> Type :=
	nilᵗ : listᵗ A Aᵗ nil
  | consᵗ : forall H : A,
            Aᵗ H -> forall H0 : list A, listᵗ A Aᵗ H0 -> listᵗ A Aᵗ (H :: H0)

listᴬᴱ = 
fun (A : Type) (Aᴱ : A -> Type) (H : list A) => listᴱ A Aᴱ H
	 : forall A : Type, (A -> Type) -> list A -> Type

listᴱᴬ = 
fun (A : Type) (Aᴱ : A -> Type) (H : list A) => listᵗ A Aᴱ H
	 : forall A : Type, (A -> Type) -> list A -> Type

Inductive listᴱ (A : Type) (Aᴱ : A -> Type) : list A -> Type :=
	consᴱ0 : forall (H : A) (H0 : list A), Aᴱ H -> listᴱ A Aᴱ (H :: H0)
  | consᴱ1 : forall (H : A) (H0 : list A),
             listᴱ A Aᴱ H0 -> listᴱ A Aᴱ (H :: H0)
**)


Open Scope type.
Definition iffT (A:Type) (B:Type) := (A->B) * (B->A).
Notation "A <-> B" := (iffT A B) : type_scope.

Inductive In {X} (x:X) : list X -> Type :=
| inB xs: In x (x::xs)
| inS y xs: In x xs -> In x (y::xs).

(** exists <-> one element in the list exists satifying P **)
Goal forall (X:Type) (P:X->Type) (xs:list X), listᴱᴱ X P xs <-> {x & In x xs * P x}.
Proof.
    split;intros H.
    - induction H as [|? ? ? (?&?&?)].
      + exists a;split;[apply inB|assumption].
      + exists x;split;[now apply inS|assumption].
    - destruct H as (?&H&?). induction H.
      + constructor 1;assumption.
      + now constructor 2.
Qed.

(** forall <-> all elements in the list fulfill P **)
Goal forall (X:Type) (P:X->Type) (xs:list X), listᴬᴬ X P xs <-> forall x, In x xs -> P x.
Proof.
    split;intros H.
    - induction H as [|? ? ? ? IH];[easy|].
      intros x G. inversion G;subst;[assumption|].
      now apply IH.
    - induction xs.
      + constructor.
      + constructor.
        * apply H; constructor.
        * now apply IHxs;intros;apply H;constructor.
Qed.









MetaCoq Run Derive Translations for prod.
(** Derived prodᵗ=prodᴬᴬ, prodᴬᴱ, prodᴱᴬ, and prodᴱ=prodᴱᴱ. **)
Print prodᵗ. (** prodᴬᴬ **) (** each element fullfills its predicate **)
Print prodᴬᴱ.
Print prodᴱᴬ.
Print prodᴱ. (** prodᴱᴱ **) (** one of the elements fulfills its predicate **)
(**
Inductive
prodᵗ (A : Type) (Aᵗ : A -> Type) (B : Type) (Bᵗ : B -> Type)
  : A * B -> Type :=
	pairᵗ : forall H : A,
            Aᵗ H -> forall H0 : B, Bᵗ H0 -> prodᵗ A Aᵗ B Bᵗ (H, H0)

prodᴬᴱ = 
fun (A : Type) (Aᴱ : A -> Type) (B : Type) (Bᴱ : B -> Type) (H : A * B) =>
(prodᴱ A Aᴱ B (fun _ : B => False) H * prodᴱ A (fun _ : A => False) B Bᴱ H)%type
	 : forall A : Type,
       (A -> Type) -> forall B : Type, (B -> Type) -> A * B -> Type

prodᴱᴬ = 
fun (A : Type) (Aᴱ : A -> Type) (B : Type) (Bᴱ : B -> Type) (H : A * B) =>
(prodᵗ A Aᴱ B (fun _ : B => True) H + prodᵗ A (fun _ : A => True) B Bᴱ H)%type
	 : forall A : Type,
       (A -> Type) -> forall B : Type, (B -> Type) -> A * B -> Type

Inductive
prodᴱ (A : Type) (Aᴱ : A -> Type) (B : Type) (Bᴱ : B -> Type)
  : A * B -> Type :=
	pairᴱ0 : forall (H : A) (H0 : B), Aᴱ H -> prodᴱ A Aᴱ B Bᴱ (H, H0)
  | pairᴱ1 : forall (H : A) (H0 : B), Bᴱ H0 -> prodᴱ A Aᴱ B Bᴱ (H, H0)
**)


Goal forall X Y Px Py x y, prodᴬᴬ X Px Y Py (x,y) <-> (Px x * Py y).
Proof.
    split;inversion_clear 1.
    - split;assumption.
    - constructor;assumption.
Qed.

Goal forall X Y Px Py x y, prodᴱᴱ X Px Y Py (x,y) <-> (Px x + Py y).
Proof.
    split;inversion_clear 1.
    - now left.
    - now right.
    - now constructor 1.
    - now constructor 2.
Qed.




Inductive List (X:Set) : Set := Nil | Cons (x:X) (xs:List X).
MetaCoq Run Derive ∃∃ for List.
Inductive rose (X:Type) : Set := tree (h:List (rose X)).
MetaCoq Run Derive ∃∃ for rose.
Print roseᴱ.
(**
Inductive roseᴱ (X : Type) (Xᴱ : X -> Type) : rose X -> Set :=
	treeᴱ0 : forall h : List (rose X),
             Listᴱ (rose X) (roseᴱ X Xᴱ) h -> roseᴱ X Xᴱ (tree X h)
**)


(** more tests for the new ∃∃ in param_exists_test.v **)