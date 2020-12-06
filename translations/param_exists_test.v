Inductive Prod1 (X:Type) := Con (x1 x2:X).
Inductive Prod (X Y:Type) := pair (x:X) (y:Y).
Inductive List (X:Type) := nil | cons (x:X) (xs:List X).
Inductive Complex (X Y:Type) := AC (x:X) | BC (x:X) (y1 y2:Y) | CC (y:Y) (c:Complex X Y).
Inductive G (X:Type) := GI (f:nat -> X).
Inductive R (X:Type) := T (xs:List X).
Inductive F (F:nat -> Type) := FI (x:F 0).

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

MetaCoq Run (printInductive nat).
MetaCoq Run (printInductive list).

(* Definition test := forall (X:Type) (Y:Type), Type. *)
Definition test := forall (X:Type) (x1:X) (Y:Type) (y1:Y) (x2:X) (y2:Y), Type.
(* Definition test := forall (X:nat) (Y:bool), Type. *)
MetaCoq Run (persistentTranslate (test)).
Print testᵗ.


Inductive Prod1' (X:Type) (X':X->Type) := Con' (x1 x2:X).
Inductive Prod1t (X:Type) (X':X->Type) : Prod1 X -> Type := Cont (x1 x2:X): Prod1t X X' (Con X x1 x2).

MetaCoq Run (printInductive Prod1).
MetaCoq Run (printInductive Prod1').
MetaCoq Run (printInductive Prod1t).
MetaCoq Run (persistentTranslate (Prod1)).
Print Prod1ᵗ.