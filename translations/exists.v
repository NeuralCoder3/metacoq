Require Import List.

Print list.
(* Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A. *)

(* forall *)

Print Forall.
(* Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
	Forall_nil : Forall P nil
  | Forall_cons : forall (x : A) (l : list A),
                  P x -> Forall P l -> Forall P (x :: l). *)

(* Inductive listᵗ (A : Type) (Aᵗ : A -> Type) : list A -> Type :=
  | nilᵗ : listᵗ A Aᵗ []
  | consᵗ : forall H : A,
             Aᵗ H ->
             forall H0 : list A, listᵗ A Aᵗ H0 -> listᵗ A Aᵗ (H :: H0). *)




(* exists *)

Inductive mem {A:Type} (x:A): list A -> Prop :=
| memO xs: mem x (x::xs)
| memS y xs: mem x xs -> mem x (y::xs).

Print Exists.
(* Inductive Exists (A : Type) (P : A -> Prop) : list A -> Prop :=
	Exists_cons_hd : forall (x : A) (l : list A), P x -> Exists P (x :: l)
  | Exists_cons_tl : forall (x : A) (l : list A),
                     Exists P l -> Exists P (x :: l) *)

(* Exists construction
for all elements of type argument A: Constructor that this new element satisfies P
for all constructors with recursion: Constructor that exists is transported
*)

Inductive rose := 
| tree (xs:list rose).

Inductive subrose : rose -> rose -> Prop :=
| sub_tree_xs xs x: Exists (fun y => x=y) xs -> subrose x (tree xs).

(* 
Subterm has exactly one constructor for each recursive occurence
  take recursive instance from arguments

for nested occurence it has to use exists sub
  generate new element and link it by exists equality (trivial form)
*)

Import ListNotations.
Definition leaf := tree [].
Definition rose3 := tree [leaf; tree [leaf;leaf]; leaf].

Example subLeaf: subrose leaf rose3.
Proof.
  constructor.
  now constructor.
Qed.

Example secondSub: subrose (tree [leaf;leaf]) rose3.
Proof.
  constructor.
  constructor 2.
  now constructor 1.
Qed.



(* simple (non-nested) examples *)
Print prod.
Inductive subProd :=. (* no recursion *)

Print list.
Inductive subList {A:Type} : list A -> list A -> Prop :=
| sub_cons_xs x xs: subList xs (cons x xs).

Inductive binTree := 
| Leaf
| Node (l r:binTree).

Inductive subBinTree : binTree -> binTree -> Prop :=
| sub_Node_l l r: subBinTree l (Node l r)
| sub_Node_r l r: subBinTree r (Node l r).
