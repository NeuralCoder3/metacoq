(**  **)

(*** param_eq: Lemmas to connect unary parametricity versions ***)

From MetaCoq.Template Require Import utils All.
From MetaCoq.Translations Require Import translation_utils.
From MetaCoq.Template Require Import Pretty.
From MetaCoq.Translations Require Import param_unary.

Definition applyEnv := tsl_rec0_2.

(** connection between up and lifting **)
(** up is going under binders **)
Lemma envUpLift x n k (E:Env): EnvUp (EnvLift E n k) x = EnvLift (EnvUp E) n (S k) x.
Proof.
    destruct x;intros;[easy|].
    unfold EnvLift; cbn.
    destruct leb;lia.
Qed.

(** congruence under EnvUp **)
Lemma envUpEq E E': 
    (forall x, E x = E' x) ->
    forall y, EnvUp E y = EnvUp E' y.
Proof.
    intros H [];cbn;trivial.
    now rewrite H.
Qed.

(** congruence under applyEnv **)
Lemma applyEnvCongr E E' t: (forall x, E x = E' x) -> applyEnv E t = applyEnv E' t.
Proof.
    intros H;induction t using term_forall_list_ind in E, E', H |- *;cbn;eauto.
    - f_equal. induction H0;trivial;cbn.
      f_equal;[now apply H0|]. apply IHForall.
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

(** connection of liftings **)
Goal forall t n k E, applyEnv (EnvLift E n k) t = lift n k (applyEnv E t).
Proof.
    intros t.
    induction t using term_forall_list_ind;intros;eauto;cbn.
    9-10: admit. (* fix, cofix *)
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

(** more lemmas needed to connect apply with lift **)
(** then the lifting and be connected to general environments **)
(** these lemmas are needed to connect the new parametricity translation **)