(**  **)

(*** param_exists_test: tests for ∃∃ translation ***)

Inductive augTest : Type := Aug (n:nat) (b:bool).
Inductive Prod1 (X:Type) := Con (x1 x2:X).
Inductive Prod (X Y:Type) := pair (x:X) (y:Y).
Inductive List (X:Set) : Set := nilL | consL (x:X) (xs:List X).
Inductive Complex (X Y:Type) := AC (x:X) | BC (x:X) (y1 y2:Y) | CC (y:Y) (c:Complex X Y).

Inductive G (X:Set) := GI (f:nat -> X).
Inductive R (X:Set) := T (xs:List X).
Inductive F (FT:nat -> Type) := FI (x:FT 0).
Inductive Ind (X:Type) : nat -> Type := IndC : Ind X 0.
Inductive Ind2 (X:Type) : nat -> Type := IndC2 (x:X) : Ind2 X 0.
Inductive IndT (X:Type) : forall (Y:Type), Type := IndTC (x:X): IndT X nat.
Inductive TA (X:Type) : Type := TAC  (x:X) (Y:Type) (y:Y) : TA X.
Inductive TA2 (X:Type) : Type := TA2C  (Y:Type) (y:Y) : TA2 X.

Load param_exists.
Definition printInductive {X} (t:X) :=
  q <- tmQuote t;;
  match q with 
  | tApp (tInd (mkInd ker _) _) _
  | tInd (mkInd ker _) _ => 
    qInd <- tmQuoteInductive ker;;
    print_nf qInd
  | _ => tmFail "No inductive type found"
  end.

MetaCoq Run (persistentTranslate augTest).
Print augTestᴱ.
MetaCoq Run (persistentTranslate nat).
Print natᴱ.
MetaCoq Run (persistentTranslate Prod1).
Print Prod1ᴱ.
MetaCoq Run (persistentTranslate Prod).
Print Prodᴱ.
MetaCoq Run (persistentTranslate List).
Print Listᴱ.
MetaCoq Run (persistentTranslate Complex).
Print Complexᴱ.

MetaCoq Run (persistentTranslate G).
Print Gᴱ.
MetaCoq Run (persistentTranslate R).
Print Rᴱ.
MetaCoq Run (persistentTranslate F).
Print Fᴱ.
MetaCoq Run (persistentTranslate Ind).
Print Indᴱ.
MetaCoq Run (persistentTranslate Ind2).
Print Ind2ᴱ.
MetaCoq Run (persistentTranslate IndT).
Print IndTᴱ.
MetaCoq Run (persistentTranslate TA).
Print TAᴱ.
MetaCoq Run (persistentTranslate TA2).
Print TA2ᴱ.

(**

Inductive augTestᴱ : augTest -> Set :=  
Inductive natᴱ : nat -> Set :=  Sᴱ0 : forall H : nat, natᴱ H -> natᴱ (S H)

Inductive Prod1ᴱ (X : Type) (Xᴱ : X -> Type) : Prod1 X -> Type :=
	Conᴱ0 : forall x1 x2 : X, Xᴱ x1 -> Prod1ᴱ X Xᴱ (Con X x1 x2)
  | Conᴱ1 : forall x1 x2 : X, Xᴱ x2 -> Prod1ᴱ X Xᴱ (Con X x1 x2)

Inductive
Prodᴱ (X : Type) (Xᴱ : X -> Type) (Y : Type) (Yᴱ : Y -> Type)
  : Prod X Y -> Type :=
	pairᴱ0 : forall (x : X) (y : Y), Xᴱ x -> Prodᴱ X Xᴱ Y Yᴱ (pair X Y x y)
  | pairᴱ1 : forall (x : X) (y : Y), Yᴱ y -> Prodᴱ X Xᴱ Y Yᴱ (pair X Y x y)

Inductive Listᴱ (X : Set) (Xᴱ : X -> Set) : List X -> Set :=
	consLᴱ0 : forall (x : X) (xs : List X), Xᴱ x -> Listᴱ X Xᴱ (consL X x xs)
  | consLᴱ1 : forall (x : X) (xs : List X),
              Listᴱ X Xᴱ xs -> Listᴱ X Xᴱ (consL X x xs)

Inductive
Complexᴱ (X : Type) (Xᴱ : X -> Type) (Y : Type) (Yᴱ : Y -> Type)
  : Complex X Y -> Type :=
	ACᴱ0 : forall x : X, Xᴱ x -> Complexᴱ X Xᴱ Y Yᴱ (AC X Y x)
  | BCᴱ0 : forall (x : X) (y1 y2 : Y),
           Xᴱ x -> Complexᴱ X Xᴱ Y Yᴱ (BC X Y x y1 y2)
  | BCᴱ1 : forall (x : X) (y1 y2 : Y),
           Yᴱ y1 -> Complexᴱ X Xᴱ Y Yᴱ (BC X Y x y1 y2)
  | BCᴱ2 : forall (x : X) (y1 y2 : Y),
           Yᴱ y2 -> Complexᴱ X Xᴱ Y Yᴱ (BC X Y x y1 y2)
  | CCᴱ0 : forall (y : Y) (c : Complex X Y),
           Yᴱ y -> Complexᴱ X Xᴱ Y Yᴱ (CC X Y y c)
  | CCᴱ1 : forall (y : Y) (c : Complex X Y),
           Complexᴱ X Xᴱ Y Yᴱ c -> Complexᴱ X Xᴱ Y Yᴱ (CC X Y y c)

Inductive Gᴱ (X : Set) (Xᴱ : X -> Set) : G X -> Set :=
	GIᴱ0 : forall f : nat -> X, (∑ H : nat, Xᴱ (f H)) -> Gᴱ X Xᴱ (GI X f)

Inductive Rᴱ (X : Set) (Xᴱ : X -> Set) : R X -> Set :=
	Tᴱ0 : forall xs : List X, Listᴱ X Xᴱ xs -> Rᴱ X Xᴱ (T X xs)

Inductive
Fᴱ (FT : nat -> Type) (FTᴱ : forall H : nat, FT H -> Type) : F FT -> Type :=
	FIᴱ0 : forall x : FT 0, FTᴱ 0 x -> Fᴱ FT FTᴱ (FI FT x)

Inductive
Indᴱ (X : Type) (Xᴱ : X -> Type) : forall H : nat, Ind X H -> Prop :=
  
Inductive
Ind2ᴱ (X : Type) (Xᴱ : X -> Type) : forall H : nat, Ind2 X H -> Type :=
	IndC2ᴱ0 : forall x : X, Xᴱ x -> Ind2ᴱ X Xᴱ 0 (IndC2 X x)

Inductive
IndTᴱ (X : Type) (Xᴱ : X -> Type) : forall Y : Type, IndT X Y -> Type :=
	IndTCᴱ0 : forall x : X, Xᴱ x -> IndTᴱ X Xᴱ nat (IndTC X x)

Inductive TAᴱ (X : Type) (Xᴱ : X -> Type) : TA X -> Type :=
	TACᴱ0 : forall (x : X) (Y : Type) (y : Y), Xᴱ x -> TAᴱ X Xᴱ (TAC X x Y y)

Inductive TA2ᴱ (X : Type) (Xᴱ : X -> Type) : TA2 X -> Type :=  
**)


(** manual translations for comparison **)
Inductive Ft (FT:nat -> Type) (FTT:forall n:nat, FT n -> Type) : F FT -> Type := FIt (x:FT 0): FTT 0 x -> Ft FT FTT (FI FT x).
Inductive natt : nat -> Type := 
| O : natt O
| S n: natt (S n).
Inductive Prod1' (X:Type) (X':X->Type) := Con' (x1 x2:X).
Inductive Prod1t (X:Type) (X':X->Type) : Prod1 X -> Type := Cont (x1 x2:X): Prod1t X X' (Con X x1 x2).
Inductive Prodt X (Xt:X->Type) Y (Yt:Y->Type) : Prod X Y -> Type := pairt (x:X) (y:Y): Prodt X Xt Y Yt (pair X Y x y).
Inductive Listt (X:Set) (Xt:X->Set) : List X -> Set := 
| nilLt : Listt X Xt (nilL X) 
| consLt (x:X) (xs:List X) : Listt X Xt (consL X x xs).

