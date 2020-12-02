
Load param_unary.

Definition applyEnv := tsl_rec0_2.

Lemma envUpLift x n k (E:Env): EnvUp (EnvLift E n k) x = EnvLift (EnvUp E) n (S k) x.
Proof.
    destruct x;intros;[easy|].
    unfold EnvLift; cbn.
    destruct leb;lia.
Qed.

Lemma envUpEq E E': 
    (forall x, E x = E' x) ->
    forall y, EnvUp E y = EnvUp E' y.
Proof.
    intros H [];cbn;trivial.
    now rewrite H.
Qed.
(* Lemma envUpEq E E' t: 
applyEnv E t = applyEnv E' t ->
applyEnv (EnvUp E) t = applyEnv (EnvUp E') t.
Proof.
    intro H;induction t using term_forall_list_ind;cbn;eauto.
    - destruct n;cbn;[trivial|].
    cbn in H. *)

Lemma applyEnvCongr E E' t: (forall x, E x = E' x) -> applyEnv E t = applyEnv E' t.
Proof.
    intros H;induction t using term_forall_list_ind in E, E', H |- *;cbn;eauto.
    (* all: try rewrite IHt;
        try rewrite IHt1;
        try rewrite IHt2;eauto. *)
    - f_equal. induction H0;trivial;cbn.
      f_equal;[now apply H0|]. apply IHForall.
     (* now rewrite H0, IHForall. *)
    - f_equal;[apply IHt1|apply IHt2];assumption.
    - f_equal;[now apply IHt1|].
      now apply IHt2, envUpEq.
    - f_equal;[now apply IHt1|].
      now apply IHt2, envUpEq.
    - f_equal;[now apply IHt1|now apply IHt2|].
      now apply IHt3, envUpEq.
    - f_equal. 
      1: now apply IHt.
      induction H0;trivial;cbn.
      f_equal;[now apply H0|]. apply IHForall.
    - f_equal;[apply IHt1|apply IHt2|];try assumption.
      induction X;trivial;cbn.
      f_equal;trivial. destruct x;now f_equal.
    - f_equal. now apply IHt.
Qed.

Goal forall t n k E, applyEnv (EnvLift E n k) t = lift n k (applyEnv E t).
(* Goal forall t n k E, applyEnv (EnvLift E n k) t = (applyEnv E (lift n k t)). *)
Proof.
    intros t.
    induction t using term_forall_list_ind;intros;eauto;cbn.
    9-10: admit. (* fix *)
    all: try rewrite IHt;
        try rewrite IHt1;
        try rewrite IHt2;eauto.
    - f_equal. induction H;trivial;cbn.
      now f_equal.
    - f_equal. erewrite applyEnvCongr. 
    2: intros x;now rewrite envUpLift.
    now rewrite IHt2.
    - f_equal. erewrite applyEnvCongr. 
    2: intros x;now rewrite envUpLift.
    now rewrite IHt2.
    - f_equal. erewrite applyEnvCongr. 
    2: intros x;now rewrite envUpLift.
    now rewrite IHt3.
    - f_equal. induction H;trivial;cbn.
    now f_equal.
    - f_equal. induction X;cbn;trivial.
    destruct x;unfold on_snd;cbn;do 2 (f_equal;trivial).
Admitted.

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