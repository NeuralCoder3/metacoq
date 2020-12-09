Inductive augTest : Type := Aug (n:nat) (b:bool).
Inductive Prod1 (X:Type) := Con (x1 x2:X).
Inductive Prod (X Y:Type) := pair (x:X) (y:Y).
Inductive List (X:Type) := nilL | consL (x:X) (xs:List X).
Inductive Complex (X Y:Type) := AC (x:X) | BC (x:X) (y1 y2:Y) | CC (y:Y) (c:Complex X Y).

Inductive G (X:Type) := GI (f:nat -> X).
Inductive R (X:Type) := T (xs:List X).
Inductive F (FT:nat -> Type) := FI (x:FT 0).
Inductive Ind (X:Type) : nat -> Type := IndC : Ind X 0.
Inductive Ind2 (X:Type) : nat -> Type := IndC2 (x:X) : Ind2 X 0.
Inductive IndT (X:Type) : forall (Y:Type), Type := IndTC (x:X): IndT X nat.
Inductive TA (X:Type) : Type := TAC  (x:X) (Y:Type) (y:Y) : TA X.
Inductive TA2 (X:Type) : Type := TA2C  (Y:Type) (y:Y) : TA2 X.
(* indices *)

(* Set Universe Polymorphism.
Unset Strict Universe Declaration.
Unset Strict Unquote Universe Mode. *)
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

(* temp for quick test *)
MetaCoq Run (persistentTranslate augTest).
Print EXaugTest.
MetaCoq Run (persistentTranslate nat).
Print EXnat.
MetaCoq Run (persistentTranslate (Prod1)).
Print EXProd1.
MetaCoq Run (persistentTranslate (Prod)).
Print EXProd.
MetaCoq Run (persistentTranslate (List)).
Print EXList.
MetaCoq Run (persistentTranslate (Complex)).
Print EXComplex.

(* Unset Strict Universe Declaration. *)

Inductive Gt (X:Type) (Xt:X->Type) : G X -> Type := 
  GIt0 (f:nat -> X): @sigT nat (fun (n:nat) => Xt (f n)) -> Gt X Xt (GI X f).
MetaCoq Run (printInductive Gt).
Fail MetaCoq Run (persistentTranslate G). (* correct but universe unquoting error *)
Fail Print EXG. 

Inductive Rt (X:Type) (Xt:X->Type) : R X -> Type := Tt (xs:List X): EXList X Xt xs -> Rt X Xt (T X xs).
MetaCoq Run (printInductive Rt).
Fail MetaCoq Run (persistentTranslate R). (* correct but universe error *)
Fail Print EXR.

Inductive Ft (FT:nat -> Type) (FTT:forall n:nat, FT n -> Type) : F FT -> Type := FIt (x:FT 0): FTT 0 x -> Ft FT FTT (FI FT x).
MetaCoq Run (printInductive Ft).
MetaCoq Run (persistentTranslate F).
Print EXF.

MetaCoq Run (persistentTranslate Ind).
Print EXInd.
MetaCoq Run (persistentTranslate Ind2).
Print EXInd2.
MetaCoq Run (persistentTranslate TA).
Print EXTA.
MetaCoq Run (persistentTranslate TA2).
Print EXTA2.
MetaCoq Run (persistentTranslate IndT).
Print EXIndT.




MetaCoq Run (printInductive nat).
MetaCoq Run (printInductive list).

(* Definition test := forall (X:Type) (Y:Type), Type. *)
Definition test := forall (X:Type) (x1:X) (Y:Type) (y1:Y) (x2:X) (y2:Y), Type.
(* Definition test := forall (X:nat) (Y:bool), Type. *)
MetaCoq Run (persistentTranslate (test)).
Print EXtest.

Inductive natt : nat -> Type := 
| O : natt O
| S n: natt (S n).

MetaCoq Run (printInductive natt).
MetaCoq Run (persistentTranslate nat).
Print EXnat.

Inductive Prod1' (X:Type) (X':X->Type) := Con' (x1 x2:X).
Inductive Prod1t (X:Type) (X':X->Type) : Prod1 X -> Type := Cont (x1 x2:X): Prod1t X X' (Con X x1 x2).

MetaCoq Run (printInductive Prod1).
MetaCoq Run (printInductive Prod1').
MetaCoq Run (printInductive Prod1t).
MetaCoq Run (persistentTranslate (Prod1)).
Print EXProd1.

Inductive Prodt X (Xt:X->Type) Y (Yt:Y->Type) : Prod X Y -> Type := pairt (x:X) (y:Y): Prodt X Xt Y Yt (pair X Y x y).
MetaCoq Run (printInductive Prodt).
MetaCoq Run (persistentTranslate (Prod)).
Print EXProd.


Inductive Listt (X:Type) (Xt:X->Type) : List X -> Type := 
| nilLt : Listt X Xt (nilL X) 
| consLt (x:X) (xs:List X) : Listt X Xt (consL X x xs).
MetaCoq Run (printInductive Listt).
MetaCoq Run (persistentTranslate (List)).
Print EXList.


MetaCoq Run (persistentTranslate (Complex)).
Print EXComplex.

MetaCoq Run (persistentTranslate G).
Print EXG.
MetaCoq Run (persistentTranslate R).
Print EXR.
MetaCoq Run (persistentTranslate F).
Print EXF.
MetaCoq Run (persistentTranslate Ind).
Print EXInd.
MetaCoq Run (persistentTranslate IndT).
Print EXIndT.
