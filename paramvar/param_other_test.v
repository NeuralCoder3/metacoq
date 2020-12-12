(**  **)

(*** param_other_test: tests for ∀∃ and ∃∀ ***)
Load param_other.

MetaCoq Run (persistentExistsTranslate prod).
MetaCoq Run (allExistsParam prod).
Print prodᴬᴱ.
(**
prodᴬᴱ = 
fun (A : Type) (Aᴱ : A -> Type) (B : Type) (Bᴱ : B -> Type) (H : A × B) =>
prodᴱ A Aᴱ B (fun _ : B => False) H × prodᴱ A (fun _ : A => False) B Bᴱ H
	 : forall A : Type,
       (A -> Type) -> forall B : Type, (B -> Type) -> A × B -> Type
**)

MetaCoq Run (persistentTranslate_prune prod true).
MetaCoq Run (existsAllParam prod).
Print prodᴱᴬ.
(**
prodᴱᴬ = 
fun (A : Type) (Aᴱ : A -> Type) (B : Type) (Bᴱ : B -> Type) (H : A × B) =>
(prodᵗ A Aᴱ B (fun _ : B => True) H + prodᵗ A (fun _ : A => True) B Bᴱ H)%type
	 : forall A : Type,
       (A -> Type) -> forall B : Type, (B -> Type) -> A × B -> Type
**)

MetaCoq Run (persistentExistsTranslate list).
MetaCoq Run (allExistsParam list).
Print listᴬᴱ.
(**
listᴬᴱ = 
fun (A : Type) (Aᴱ : A -> Type) (H : list A) => listᴱ A Aᴱ H
	 : forall A : Type, (A -> Type) -> list A -> Type
**)

Inductive PNT (n:nat) (X:Type) (d:nat) : Type.
MetaCoq Run (persistentExistsTranslate PNT).
MetaCoq Run (allExistsParam PNT).
Print PNTᴬᴱ.
(**
ITᴬᴱ = 
fun (X : Type) (Xᴱ : X -> Type) (H : Type) (H0 : IT X H) => ITᴱ X Xᴱ H H0
	 : forall X : Type, (X -> Type) -> forall H : Type, IT X H -> Prop
**)


Inductive IT (X:Type) : Type -> Type:=.
MetaCoq Run (persistentExistsTranslate IT).
MetaCoq Run (allExistsParam IT).
Print ITᴬᴱ.
(**
ITᴬᴱ = 
fun (X : Type) (Xᴱ : X -> Type) (H : Type) (H0 : IT X H) => ITᴱ X Xᴱ H H0
	 : forall X : Type, (X -> Type) -> forall H : Type, IT X H -> Prop
**)
