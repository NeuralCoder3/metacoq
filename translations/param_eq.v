
Load param_unary.

(* lemmas about env vs lift *)

(* Goal forall t E, tsl_rec1 E t = tsl_rec1_org E t.
Proof.
  unfold tsl_rec1, tsl_rec1_org.
  (* generalize tsl_rec1' Env Envt *)
  intros t; induction t eqn: H using term_forall_list_ind;cbn;eauto;intros.
  (* all: cbn in *. *)
    - admit. (* Naming *)
    - admit. (* Naming *)
    - admit. (* Naming *)
  - admit. (* cast *)
  - admit. (* prod *)
  - admit. (* lambda *)
  - admit. (* letin *)
  - admit. (* app *)
    - admit. (* case *)
Abort. *)

(* Goal forall r n k E, EnvUp (EnvLift E n k) r = EnvLift E n (S k) r.
Proof.
  induction r;cbn;intros.
  - unfold EnvLift.
  induction t using term_forall_list_ind;cbn;
  try rewrite IHt1;try rewrite IHt2;try easy;intros n0 k E.

Goal forall t n k E, tsl_rec0_2 (EnvLift E n k) t = lift n k (tsl_rec0_2 E t).
Proof.
  induction t using term_forall_list_ind;cbn;
  try rewrite IHt1;try rewrite IHt2;try easy;intros n0 k E.
  - admit.
  - f_equal.
    + apply IHt1.
    + apply IHt2. *)

(* Goal forall t, tsl_rec0_2 (fun n => n) t = t.
Proof.
  induction t using term_forall_list_ind;cbn;
  try rewrite IHt1;try rewrite IHt2;try easy.
  - admit.
  - now rewrite IHt1, IHt2. *)

  (* Compute(EnvUp (EnvLift (fun n => n) 2 0) 1).
  Compute(EnvLift (EnvUp (fun n => n)) 2 1 1). *)

(* Goal forall n E, (forall n, E n >= n) -> EnvUp (EnvLift E 2 0) n = EnvLift (EnvUp E) 2 1 n.
Proof.
intros n E H.
  induction n;trivial;cbn.
  unfold EnvLift, EnvUp.
  assert(1<=E n) as -> by lia.
*)

(* theoretic statement needs many lemmas and strengthening
Goal forall t E, tsl_rec1 E t = tsl_rec1_org E t.
Proof.
  intros t;
  induction t using term_forall_list_ind;cbn;
  try rewrite IHt1;try rewrite IHt2;try easy. *)