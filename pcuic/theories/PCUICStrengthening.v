(* Distributed under the terms of the MIT license.   *)

From Coq Require Import List Arith Lia ssrbool CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.

From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICEquality PCUICTyping
     PCUICReduction PCUICPosition PCUICAstUtils PCUICLiftSubst PCUICUnivSubst
     PCUICWeakening.

Local Open Scope string_scope.
Import ListNotations. Open Scope list_scope.
Set Asymmetric Patterns.

Set Default Goal Selector "!".


From Equations Require Import Equations Relation.

Derive Signature for red1.
Derive Signature for OnOne2.

Lemma app_mkApps u v t l :
  isApp t = false -> tApp u v = mkApps t l ->
  ∑ l', (l = l' ++ [v])%list × u = mkApps t l'.
Proof.
  intros h e. induction l in u, v, t, e, h |- * using list_rect_rev.
  - cbn in e. subst. cbn in h. discriminate.
  - rewrite <- mkApps_nested in e. cbn in e.
    exists l. inversion e. subst. auto.
Qed.

Lemma red1_tApp_inv Σ Γ t u v (H : red1 Σ Γ (tApp t u) v)
  : (∑ w, red1 Σ Γ t w × v = tApp w u) + (∑ w, red1 Σ Γ u w × v = tApp t w).
Proof.
  depelim H.
  - admit.
  - left. apply app_mkApps in H; cbnr.
    destruct H as [l [H1 H2]]; subst.
    exists (mkApps fn l). split.
    + eapply red_fix; tea. admit. (* wrong *)
    + now rewrite <- mkApps_nested.
  - left; eexists; split; tea. reflexivity.
  - right; eexists; split; tea. reflexivity.
Abort.


Lemma not_isLambda_mkApps u l :
  ~~ isLambda u -> ~~ isLambda (mkApps u l).
Proof.
  induction l in u |- *; cbn; auto.
Qed.

Lemma tLambda_mkApps_not_isLambda na A t u l :
  ~~ isLambda u -> tLambda na A t <> mkApps u l.
Proof.
  intros H e. eapply not_isLambda_mkApps in H.
  rewrite <- e in H; auto.
Qed.

Lemma tLambda_mkApps_tFix na A t mfix idx args :
  tLambda na A t <> mkApps (tFix mfix idx) args.
Proof.
  now apply tLambda_mkApps_not_isLambda.
Qed.

Lemma tRel_mkApps_tFix n mfix idx args :
  tRel n <> mkApps (tFix mfix idx) args.
Proof.
  induction args using rev_ind; cbn.
  - inversion 1.
  - rewrite <- mkApps_nested; cbn. inversion 1.
Qed.

(* Lemma tVar_mkApps_tFix n mfix idx args : *)
(*   tVar n <> mkApps (tFix mfix idx) args. *)
(* Proof. *)
(*   induction args using rev_ind; cbn. *)
(*   - inversion 1. *)
(*   - rewrite <- mkApps_nested; cbn. inversion 1. *)
(* Qed. *)

(* TODO MOVE *)
Fixpoint isFixApp t : bool :=
  match t with
  | tApp f u => isFixApp f
  | tFix mfix idx => true
  | _ => false
  end.

(* TODO MOVE *)
Lemma isFixApp_mkApps :
  forall t l,
    isFixApp (mkApps t l) = isFixApp t.
Proof.
  intros t l. induction l in t |- *.
  - cbn. reflexivity.
  - cbn. rewrite IHl. reflexivity.
Qed.

(* Lemma lift_tLambda_inv n k M na A t (H : lift n k M = tLambda na A t) *)
(*   : ∑ A' t', M = tLambda na A' t' /\ A = lift n k A' /\ t = lift n (S k) t'. *)
(* Proof. *)
(*   induction M; cbn in *; try now inversion H. *)
(*   - invs H. repeat eexists. *)
(* Defined. *)

Lemma lift_Apps_Ind_inv n k M ind u args
      (H : lift n k M = mkApps (tInd ind u) args)
  : ∑ args', M = mkApps (tInd ind u) args'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    exists []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1. destruct H1 as [args' [H1 H2]]; subst.
    exists (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split.
Qed.

Lemma lift_Apps_Construct_inv n k M ind c u args
      (H : lift n k M = mkApps (tConstruct ind c u) args)
  : ∑ args', M = mkApps (tConstruct ind c u) args'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    exists []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1. destruct H1 as [args' [H1 H2]]; subst.
    exists (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split.
Qed.

Lemma lift_Apps_Fix_inv n k M mfix idx args
      (H : lift n k M = mkApps (tFix mfix idx) args)
  : ∑ mfix' args', M = mkApps (tFix mfix' idx) args'
             /\ mfix = map (map_def (lift n k) (lift n (#|mfix'| + k))) mfix'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    invs H. eexists _, []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    exists mfix', (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split; tas.
Qed.

Lemma lift_Apps_CoFix_inv n k M mfix idx args
      (H : lift n k M = mkApps (tCoFix mfix idx) args)
  : ∑ mfix' args', M = mkApps (tCoFix mfix' idx) args'
             /\ mfix = map (map_def (lift n k) (lift n (#|mfix'| + k))) mfix'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    invs H. eexists _, []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    exists mfix', (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split; tas.
Qed.
    

(* todo replace in liftsubst *)
Lemma isLambda_lift n k (bod : term) :
  isLambda (lift n k bod) = isLambda bod.
Proof. destruct bod; cbnr. Qed.

(* todo replace in weakening *)
Lemma lift_unfold_fix n k mfix idx :
  unfold_fix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx
  = option_map (on_snd (lift n k)) (unfold_fix mfix idx).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx); cbnr.
  rewrite isLambda_lift.
  destruct isLambda; cbnr. f_equal. unfold on_snd; cbn. f_equal.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite fix_subst_length. f_equal.
  unfold fix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.

Lemma lift_unfold_cofix n k mfix idx :
  unfold_cofix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx
  = option_map (on_snd (lift n k)) (unfold_cofix mfix idx).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx); cbnr.
  f_equal. unfold on_snd; cbn. f_equal.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite cofix_subst_length. f_equal.
  unfold cofix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.

(* todo replace in weakening *)
Lemma lift_is_constructor args narg n k :
  is_constructor narg args = is_constructor narg (map (lift n k) args).
Proof.
  unfold is_constructor. rewrite nth_error_map.
  destruct nth_error; cbnr.
  unfold isConstruct_app. destruct decompose_app eqn:Heq.
  eapply decompose_app_lift in Heq as ->; cbn.
  destruct t0; cbnr.
Qed.

(* Lemma nth_error_lift_context Γ Γ' Γ'' n : *)
(*   nth_error (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') *)
(*             (if #|Γ'| <=? n then #|Γ''| + n else n) *)
(*   = nth_error (Γ ,,, lift_context #|Γ''| 0 Γ') n. *)
(* Proof. *)
(*   destruct (leb_spec_Set #|Γ'| n). *)
(*   - rewrite !nth_error_app_context_ge; rewrite ?lift_context_length; try lia. *)
(*     f_equal; lia. *)
(*   - rewrite !nth_error_app_context_lt; rewrite ?lift_context_length; try lia. *)
(*     reflexivity. *)
(* Qed. *)



Lemma red1_strengthening {cf:checker_flags} Σ Γ Γ' Γ'' M N' :
  wf Σ ->
  red1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) N'
  -> ∑ N, red1 Σ (Γ ,,, Γ') M N × N' = lift #|Γ''| #|Γ'| N.
Proof.
  intros HΣ H; dependent induction H using red1_ind_all.
  - destruct M; cbn in H; try discriminate.
    destruct M1; invs H.
    eexists. split.
    { constructor. }
    now rewrite distr_lift_subst10.
  - destruct M; invs H.
    eexists. split.
    { constructor. }
    now rewrite distr_lift_subst10.
  - destruct M; invs H0.
    rewrite <- app_context_assoc in H.
    destruct (leb_spec_Set #|Γ'| n).
    + rewrite nth_error_app_context_ge in H;
        rewrite app_context_length, lift_context_length in *; [|lia].
      eexists. split.
      { constructor. rewrite nth_error_app_context_ge; tas.
        etransitivity; tea. do 2 f_equal. lia. }
      rewrite simpl_lift; try lia.
      f_equal. lia.
    + rewrite nth_error_app_context_lt in H;
        rewrite ?app_context_length, ?lift_context_length in *; [|lia].
      rewrite nth_error_app_context_lt in H;
        rewrite ?app_context_length, ?lift_context_length in *; [|lia].
      rewrite nth_error_lift_context_eq in H.
      case_eq (nth_error Γ' n); [|intro HH; rewrite HH in H; discriminate].
      intros [na [bd|] ty] HH; rewrite HH in H; [|discriminate].
      eexists. split.
      { constructor. rewrite nth_error_app_context_lt; [|lia].
        rewrite HH. reflexivity. }
      clear HH. invs H.
      rewrite permute_lift; [|lia]. f_equal; lia.
  - destruct M; invs H.
    apply lift_Apps_Construct_inv in H3.
    destruct H3 as [args' [H1 H2]]; subst.
    eexists. split.
    { constructor. }
    symmetry; apply lift_iota_red.
  - apply lift_Apps_Fix_inv in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_fix in H.
    destruct (unfold_fix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    invs H. rewrite <- lift_is_constructor in H0.
    eexists; split.
    { econstructor; tea. }
    symmetry; apply lift_mkApps.
  - destruct M; invs H0.
    apply lift_Apps_CoFix_inv in H4.
    destruct H4 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_cofix in H.
    destruct (unfold_cofix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    invs H. eexists; split.
    { econstructor; tea. }
    cbn. f_equal. symmetry; apply lift_mkApps.
  - destruct M; invs H0.
    apply lift_Apps_CoFix_inv in H3.
    destruct H3 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_cofix in H.
    destruct (unfold_cofix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    invs H. eexists; split.
    { econstructor; tea. }
    cbn. f_equal. symmetry; apply lift_mkApps.
  - destruct M; invs H1.
    eexists; split.
    { econstructor; tea. }
    rewrite lift_subst_instance_constr.
    f_equal. destruct decl as []; cbn in *; subst.
    eapply lift_declared_constant in H; tas.
    apply (f_equal cst_body) in H; cbn in *.
    apply some_inj in H; eassumption.
  - destruct M; invs H0.
    apply lift_Apps_Construct_inv in H3.
    destruct H3 as [args' [H1 H2]]; subst.
    rewrite nth_error_map in H.
    destruct (nth_error args' (pars + narg)) eqn:X; invs H.
    eexists; split.
    { econstructor; tea. }
    reflexivity.

  - destruct M0; invs H0.
    edestruct IHred1 as [M1' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 10; eassumption. }
    cbn; congruence.
  - destruct M0; invs H0.
    edestruct (IHred1 Γ0 (Γ' ,, vass na M0_1)) as [M2' [H1 H2]];
      tas; try reflexivity.
    { rewrite lift_context_snoc. rewrite app_context_cons; f_equal.
      now rewrite Nat.add_0_r. }
    eexists. split.
    { constructor 11; eassumption. }
    cbn in *; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M1' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 12; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 13; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct (IHred1 Γ0 (Γ' ,, vdef na M1 M2)) as [M3' [H1 H2]];
      tas; try reflexivity.
    { rewrite lift_context_snoc. rewrite app_context_cons; f_equal.
      now rewrite Nat.add_0_r. }
    eexists. split.
    { constructor 14; eassumption. }
    cbn in *; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M1' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 15; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 16; eassumption. }
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ brs,
                OnOne2 (on_Trel_eq (red1 Σ (Γ0 ,,, Γ')) snd fst) brs0 brs
                × brs' = map (on_snd (lift #|Γ''| #|Γ'|)) brs). {
      clear -X HΣ.
      dependent induction X.
      + destruct brs0 as [|[brs0 brs0'] brs1]; invs H.
        destruct p as [[H1 H2] H3].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        exists ((brs0, N) :: brs1). split.
        { constructor; split; tas; reflexivity. }
        destruct hd'; cbn in *; unfold on_snd; cbn. congruence.
      + destruct brs0 as [|[brs0 brs0'] brs1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn. congruence. }
    destruct XX as [brs [Hb1 Hb2]].
    eexists. split.
    { constructor 17; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 18; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 19; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 20; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 21; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct (IHred1 Γ0 (Γ' ,, vass na M3)) as [M2' [H1 H2]];
      tas; try reflexivity.
    { rewrite lift_context_snoc. rewrite app_context_cons; f_equal.
      now rewrite Nat.add_0_r. }
    eexists. split.
    { constructor 22; eassumption. }
    cbn in *; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l,
                OnOne2 (red1 Σ (Γ0 ,,, Γ')) l0 l
                × l' = map (lift #|Γ''| #|Γ'|) l). {
      clear -X HΣ.
      dependent induction X.
      + destruct l0 as [|l0 l1]; invs H.
        destruct p as [H1 H2].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        exists (N :: l1). split.
        { constructor; assumption. }
        cbn; congruence.
      + destruct l0 as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 23; eassumption. }
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l,
                OnOne2 (fun x y => red1 Σ (Γ0 ,,, Γ') (dtype x) (dtype y)
                  × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix l
                × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                                       (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      set (k := #|mfix|) in *; clearbody k.
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        destruct l0 as [na ty bd arg]; cbn in *.
        exists ({| dname := na; dtype := N; dbody := bd; rarg := arg |} :: l1). split.
        { constructor; cbn; now split. }
        cbn; f_equal. unfold map_def; destruct hd'; cbn in *. congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 24; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l, OnOne2 (fun x y =>
     red1 Σ (Γ0 ,,, Γ' ,,, fix_context mfix) (dbody x) (dbody y)
     × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix l
     × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                            (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      rewrite lift_fix_context in X.
      pose proof (lift_context_app #|Γ''| 0 Γ' (fix_context mfix)) as e.
      rewrite Nat.add_0_r in e.
      rewrite <- app_context_assoc, <- e in X; clear e.
      (* pose proof (fix_context_length mfix) as Hctx. *)
      rewrite <- (fix_context_length mfix) in *.
      set (ctx := fix_context mfix) in *; clearbody ctx.
      (* set (k := #|mfix|) in *; clearbody k. *)
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        destruct l0 as [na ty bd arg]; simpl in *.
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        { f_equal. f_equal.
          now rewrite app_context_length. }
        exists ({| dname := na; dtype := ty; dbody := N; rarg := arg |} :: l1). split.
        { constructor; simpl; split; try reflexivity.
          now rewrite app_context_assoc in HN1. }
        cbn; f_equal. unfold map_def; destruct hd'; simpl in *.
          rewrite app_context_length in HN2; simpl in HN2.
          congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 25; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l,
                OnOne2 (fun x y => red1 Σ (Γ0 ,,, Γ') (dtype x) (dtype y)
                  × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix l
                × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                                       (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      set (k := #|mfix|) in *; clearbody k.
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        destruct l0 as [na ty bd arg]; cbn in *.
        exists ({| dname := na; dtype := N; dbody := bd; rarg := arg |} :: l1). split.
        { constructor; cbn; now split. }
        cbn; f_equal. unfold map_def; destruct hd'; cbn in *. congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 26; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l, OnOne2 (fun x y =>
     red1 Σ (Γ0 ,,, Γ' ,,, fix_context mfix) (dbody x) (dbody y)
     × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix l
     × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                            (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      rewrite lift_fix_context in X.
      pose proof (lift_context_app #|Γ''| 0 Γ' (fix_context mfix)) as e.
      rewrite Nat.add_0_r in e.
      rewrite <- app_context_assoc, <- e in X; clear e.
      (* pose proof (fix_context_length mfix) as Hctx. *)
      rewrite <- (fix_context_length mfix) in *.
      set (ctx := fix_context mfix) in *; clearbody ctx.
      (* set (k := #|mfix|) in *; clearbody k. *)
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        destruct l0 as [na ty bd arg]; simpl in *.
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        { f_equal. f_equal.
          now rewrite app_context_length. }
        exists ({| dname := na; dtype := ty; dbody := N; rarg := arg |} :: l1). split.
        { constructor; simpl; split; try reflexivity.
          now rewrite app_context_assoc in HN1. }
        cbn; f_equal. unfold map_def; destruct hd'; simpl in *.
          rewrite app_context_length in HN2; simpl in HN2.
          congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 27; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
Qed.

(* todo remove map_inj of PCUICReduction *)
Lemma map_inj' A B (f : A -> B) l l' :
  All2 (fun x y => f x = f y -> x = y) l l' ->
  map f l = map f l' ->
  l = l'.
Proof.
  induction 1.
  - reflexivity.
  - cbn. injection 1; intros. forward r; tas. forward IHX; tas. congruence.
Qed.

Lemma map_inj'' A B (f : A -> B) l l' :
  All (fun x => forall y, f x = f y -> x = y) l ->
  map f l = map f l' ->
  l = l'.
Proof.
  induction 1 in l' |- *.
  - destruct l'; try discriminate. reflexivity.
  - destruct l'; try discriminate. cbn. injection 1; intros.
    erewrite p; tea. now erewrite IHX.
Qed.

Lemma lift_inj n k t u : lift n k t = lift n k u -> t = u.
Proof.
  revert k u.
  induction t using PCUICInduction.term_forall_list_ind; cbn;
    intros k uu H; destruct uu; try discriminate; tas; cbn in H; invs H.
  - f_equal.
    destruct (leb_spec_Set k n0); destruct (leb_spec_Set k n1); lia.
  - apply map_inj'' in H2.
    + congruence.
    + eapply All_impl; eauto.
  - now erewrite IHt1, IHt2.
  - now erewrite IHt1, IHt2.
  - now erewrite IHt1, IHt2, IHt3.
  - now erewrite IHt1, IHt2.
  - erewrite IHt1, IHt2; tea. f_equal.
    apply map_inj'' in H4; tas.
    eapply All_impl; tea. intros [] ? [] H; cbn in *.
    injection H; intros; subst. f_equal; eauto.
  - now erewrite IHt.
  - f_equal. assert (e: #|m| = #|mfix|). {
      apply (f_equal (@length _)) in H1.
      now rewrite !map_length in H1. }
    rewrite e in H1; clear e.
    apply map_inj'' in H1; tas.
    eapply All_impl; tea. intros [] [] [] H; cbn in *.
    injection H; intros; subst. f_equal; eauto.
  - f_equal. assert (e: #|m| = #|mfix|). {
      apply (f_equal (@length _)) in H1.
      now rewrite !map_length in H1. }
    rewrite e in H1; clear e.
    apply map_inj'' in H1; tas.
    eapply All_impl; tea. intros [] [] [] H; cbn in *.
    injection H; intros; subst. f_equal; eauto.
Qed.


Lemma pouet {cf:checker_flags} {Σ Γ Γ' Γ''}
      (wfΓ : wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'))
  : All_local_env_over typing
       (fun Σ0 Γ0 (_ : wf_local Σ0 Γ0) t T (_ : Σ0;;; Γ0 |- t : T) =>
          forall Γ'0 t0, Γ0 = Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'0 ->
                    t = lift #|Γ''| #|Γ'0| t0 ->
          ∑ A, Σ0;;; Γ ,,, Γ'0 |- t0 : A × T = lift #|Γ''| #|Γ'0| A)
       Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') wfΓ
    -> wf_local Σ (Γ ,,, Γ').
Proof.
  intro X. dependent induction X.
  - invs H. destruct Γ'; [|rewrite lift_context_snoc0 in H1; discriminate].
    cbn in wfΓ. clear -wfΓ. now apply wf_local_app in wfΓ.
  - invs H.
    destruct Γ'; [|rewrite lift_context_snoc0 in H1].
    + cbn in wfΓ. clear -wfΓ. now apply wf_local_app in wfΓ.
    + injection H1. intros ?H ?H Hc ?H; subst.
      destruct c as [na [bo|] ty]; [discriminate|].
      simpl. constructor.
      * now eapply IHX.
      * cbn in p.  clear -p.
        edestruct p as [A [H1 H2]]; try reflexivity.
        { now rewrite Nat.add_0_r. }
        destruct A; invs H2.
        eexists; eassumption.
  - invs H.
    destruct Γ'; [|rewrite lift_context_snoc0 in H1].
    + cbn in wfΓ. clear -wfΓ. now apply wf_local_app in wfΓ.
    + injection H1. intros ?H ?H Hc ?H; subst.
      destruct c as [na [bo|] ty]; [|discriminate].
      simpl. constructor.
      * now eapply IHX.
      * cbn in p0.  clear -p0.
        edestruct p0 as [A [H1 H2]]; try reflexivity.
        { now rewrite Nat.add_0_r. }
        destruct A; invs H2.
        eexists; eassumption.
      * apply some_inj in Hc. cbn in p. clear -p Hc.
        edestruct p as [A [H1 H2]]; try reflexivity.
        { rewrite Nat.add_0_r in Hc; now symmetry. }
        rewrite Nat.add_0_r in H2. cbn.
        apply lift_inj in H2; now subst.
Qed.


Lemma strengthening {cf:checker_flags} {Σ Γ Γ' Γ'' t A1} :
  wf Σ.1 ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| t : A1 ->
  ∑ A, A1 = lift #|Γ''| #|Γ'| A × Σ;;; Γ ,,, Γ' |- t : A.
Proof.
  intros HΣ H.
  simple refine (let X := typing_ind_env
    (fun Σ Γ1 t1 A1 => forall Γ' t, Γ1 = Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'
                          -> t1 = lift #|Γ''| #|Γ'| t
                          -> ∑ A, Σ;;; Γ ,,, Γ' |- t : A × A1 = lift #|Γ''| #|Γ'| A)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ in _).
  1-14: cbn; clear; intros.
  - destruct t; invs H1.
    destruct (leb_spec_Set #|Γ'| n0).
    + rewrite nth_error_app_context_ge in H;
        rewrite lift_context_length in *; [|lia].
      eexists. split.
      * econstructor.
        { now apply pouet in X. }
        rewrite nth_error_app_context_ge; tas.
        rewrite nth_error_app_context_ge in H; [|lia].
        etransitivity; tea. f_equal. lia.
      * rewrite simpl_lift; try lia. f_equal; lia.
    + rewrite nth_error_app_context_lt in H;
        [|rewrite lift_context_length; lia].
      rewrite nth_error_lift_context_eq in H.
      destruct (nth_error Γ' n0) eqn: Hdecl; [|discriminate].
      apply some_inj in H; subst.
      eexists. split.
      * econstructor.
        { now apply pouet in X. }
        rewrite nth_error_app_context_lt; tea.
      * rewrite Nat.add_0_r. clear Hdecl. destruct c as [na bo ty]; cbn.
        clear -l. rewrite permute_lift; try lia.
        f_equal; lia.
  - destruct t; invs H1.
    eexists; split.
    + econstructor; tea.
      now apply pouet in X.
    + reflexivity.
  - destruct t0; invs H0.
    edestruct X1 as [x1 [Hx1 Hx1']]; try reflexivity.
    destruct x1; invs Hx1'.
    edestruct (X3 (Γ' ,, vass na t0_1)) as [x2 [Hx2 Hx2']]; try reflexivity.
    { now rewrite lift_context_snoc, Nat.add_0_r. }
    destruct x2; invs Hx2'.
    eexists; split.
    + econstructor; tea.
    + reflexivity.
  - destruct t0; invs H0.
    edestruct X1 as [x1 [Hx1 Hx1']]; try reflexivity.
    destruct x1; invs Hx1'.
    edestruct (X3 (Γ' ,, vass na t0_1)) as [x2 [Hx2 Hx2']]; try reflexivity.
    { now rewrite lift_context_snoc, Nat.add_0_r. }
    subst.
    eexists; split.
    + econstructor; tea.
    + reflexivity.
  - destruct t; invs H0.
    edestruct X1 as [x1 [Hx1 Hx1']]; try reflexivity.
    destruct x1; invs Hx1'.
    edestruct X3 as [x3 [Hx3 Hx3']]; try reflexivity.
    apply lift_inj in Hx3'; subst.
    edestruct (X5 (Γ' ,, vdef na t1 x3)) as [x2 [Hx2 Hx2']]; try reflexivity.
    { now rewrite lift_context_snoc, Nat.add_0_r. }
    subst.
    eexists; split.
    + econstructor; tea.
    + reflexivity.
  - destruct t0; invs H0.
    edestruct X1 as [x1 [Hx1 Hx1']]; try reflexivity.
    destruct x1; invs Hx1'.
    edestruct X3 as [x2 [Hx2 Hx2']]; try reflexivity.
    apply lift_inj in Hx2'; subst.
    eexists; split.
    + econstructor; tea.
    + symmetry; apply distr_lift_subst.
  - destruct t; invs H2.
    eexists; split.
    + econstructor; tea.
      now apply pouet in X0.
    + rewrite lift_subst_instance_constr.
      eapply lift_declared_constant in H; tas.
      exact (f_equal ((subst_instance_constr ui) ∘ cst_type) H).
  - destruct t; invs H1.
    eexists; split.
    + econstructor; tea.
      now apply pouet in X0.
    + rewrite lift_subst_instance_constr.
      eapply lift_declared_inductive in isdecl; tas.
      rewrite (f_equal ((subst_instance_constr ui) ∘ ind_type) (eq_sym isdecl)).
      destruct idecl; reflexivity.
  - destruct t; invs H1.
    eexists; split.
    + econstructor; tea.
      now apply pouet in X0.
    + eapply lift_declared_constructor in isdecl; tas.
      symmetry; eassumption.
  - admit. (* case *)
  - destruct t; invs H1.
    edestruct X2 as [x1 [Hx1 Hx1']]; try reflexivity.
    symmetry in Hx1'; apply lift_Apps_Ind_inv in Hx1'.
    destruct Hx1' as [args' [H1 H2]]; subst.
    rewrite map_length in H.
    eexists; split.
    + econstructor; tea.
    + rewrite distr_lift_subst. cbn. 
      rewrite map_rev. f_equal.
      rewrite lift_subst_instance_constr. f_equal.
      eapply lift_declared_projection in isdecl; tea.
      rewrite <- isdecl at 1. cbn. rewrite List.rev_length, H.
      reflexivity.
  - admit. (* fix *)
  - admit. (* cofix *)
  - edestruct X1 as [x1 [Hx1 Hx1']]; tea. subst.
    eexists; split.
    + econstructor; tea.  all: admit.
    + admit.
  - clearbody X. eapply X in H; tas; clear X.
    + destruct H as [_ H]. edestruct H as [A [H1 H2]]; try reflexivity.
      eexists; split; eassumption.
    + now apply typing_wf_local in H.
Admitted.
