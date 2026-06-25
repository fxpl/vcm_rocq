From Vcm Require Import Common.
From Vcm Require Import SharedMemory.
From Vcm Require Import Log.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import LoggingSharedMemory.
From Vcm Require Import LoggingSharedMemoryFacts.
From Vcm Require Import Linear.
From Vcm Require Import LoggingLinear.
From Vcm Require Import LoggingLinearFacts.
From Vcm Require Import LinearEquivLemmas.
From Vcm Require Import LogFacts.

Import Log.
Import LogFacts.

Definition matching_threads (TSh : SharedMemory.threads) (TL : Linear.threads) :=
  forall t ts e,
    binds TSh t (ts, e) <-> exists d c, binds TL t (ts, e, d, c).

Lemma matching_threads_same_domain :
  forall TSh TL,
    matching_threads TSh TL ->
    dom TSh = dom TL.
Proof.
  introv Hmatch.
  simpls. unfolds SharedMemory.threads, Linear.threads.
  repeat rewrite dom_eq_set_of_binds.
  apply set_st_eq.
  intros t. splits.
  + introv ((st & e) & Hbinds).
    apply Hmatch in Hbinds as (d & c & Hbinds').
    exists*.
  + introv ((((st & e) & d ) & c) & Hbinds).
    exists (st, e). apply* Hmatch.
Qed.

Lemma matching_threads_update_same :
  forall TSh TL t ts e d c,
    matching_threads TSh TL ->
    matching_threads TSh[t := (ts, e)] TL[t := (ts, e, d, c)].
Proof.
  introv Hmatch.
  introv. splits; introv Hbinds.
  - destruct (classic (t = t0)).
    + subst.
      forwards Heq: binds_update_same_inv Hbinds.
      inverts Heq.
      exists. apply binds_update_same.
    + forwards~ Hbinds': binds_update_neq_inv Hbinds.
      apply Hmatch in Hbinds' as (d' & c' & Hbinds'').
      exists. apply* binds_update_neq.
  - destruct Hbinds as (d' & c' & Hbinds).
    destruct (classic (t = t0)).
    + subst.
      forwards Heq: binds_update_same_inv Hbinds.
      inverts Heq. apply binds_update_same.
    + forwards~ Hbinds': binds_update_neq_inv Hbinds.
      apply~ binds_update_neq.
      apply* Hmatch.
Qed.

Hint Resolve matching_threads_update_same : vcm.

Lemma matching_threads_global_commit :
  forall TSh TL TL' t g g' G G',
    matching_threads TSh TL ->
    t \indom TSh ->
    global_commit t g g' TL G = (TL', G') ->
    matching_threads TSh TL'.
Proof.
  introv Hmatch Hdom Hcommit.
  asserts Hdom': (t \indom TL).
  {
    forwards Heq: matching_threads_same_domain Hmatch.
    rewrite* <- Heq.
  }
  unfolds global_commit.
  introv. splits; introv Hbinds.
  - destruct (classic (t = t0)).
    + subst.
      apply Hmatch in Hbinds as (d & c & Hbinds).
      forwards Hread: read_of_binds Hbinds.
      replace (TL[t0]) with (ts, e, d, c) in Hcommit.
      inverts Hcommit. exists.
      apply binds_update_same.
    + apply Hmatch in Hbinds as (d & c & Hbinds).
      destruct (TL[t]) as [[[ts' e'] d'] c'].
      inverts Hcommit.
      exists.
      apply* binds_update_neq.
  - apply Hmatch.
    forwards* Hbinds': binds_of_indom_read Hdom'.
    destruct (TL[t]) as [[[ts' e'] d'] c'].
    inverts Hcommit.
    destruct Hbinds as (d & c & Hbinds).
    destruct (classic (t = t0)).
    + subst.
      forwards Heq: binds_update_same_inv Hbinds.
      inverts Heq.
      exists*.
    + forwards~ Hbinds'': binds_update_neq_inv Hbinds.
      exists*.
Qed.

Hint Resolve matching_threads_global_commit : vcm.

Lemma matching_threads_push_thread :
  forall TSh TL TL' t t' g g' G G',
    matching_threads TSh TL ->
    t \indom TSh ->
    t' \indom TSh ->
    t <> t' ->
    push_thread t t' g g' TL G = (TL', G') ->
    matching_threads TSh TL'.
Proof.
  introv Hmatch HdomSh HdomSh' Hneq Hpush.
  asserts HdomL: (t \indom TL).
  {
    forwards Heq: matching_threads_same_domain Hmatch.
    rewrite* <- Heq.
  }
  asserts HdomL': (t' \indom TL).
  {
    forwards Heq: matching_threads_same_domain Hmatch.
    rewrite* <- Heq.
  }
  unfolds push_thread, global_commit.
  introv. splits; introv Hbinds.
  - destruct (classic (t = t0)).
    + subst.
      apply Hmatch in Hbinds as (d' & c & Hbinds).
      forwards Hread: read_of_binds Hbinds.
      destruct (TL[t0]) as [[[ts' e'] d''] c'].
      inverts Hread.
      rewrite~ read_update_neq in Hpush.
      destruct (TL[t']) as [[[ts' e'] d''] c'].
      inverts Hpush.
      exists. apply~ binds_update_neq.
      apply* binds_update_same.
    + apply Hmatch in Hbinds as (d & c & Hbinds).
      forwards* Hbinds': binds_of_indom_read HdomL.
      destruct (TL[t]) as [[[ts' e'] d'] c'].
      rewrite~ read_update_neq in Hpush.
      forwards* Hbinds'': binds_of_indom_read HdomL'.
      destruct (TL[t']) as [[[ts'' e''] d''] c''].
      inverts Hpush.
      destruct (classic (t0 = t')).
      * subst.
        forwards~ Heq: binds_inj Hbinds Hbinds''.
        inverts Heq.
        exists.
        apply* binds_update_same.
      * exists.
        do 2 apply* binds_update_neq.
  - apply Hmatch.
    forwards* Hbinds': binds_of_indom_read HdomL.
    destruct (TL[t]) as [[[ts' e'] d'] c'].
    rewrite~ read_update_neq in Hpush.
    forwards* Hbinds'': binds_of_indom_read HdomL'.
    destruct (TL[t']) as [[[ts'' e''] d''] c''].
    inverts Hpush.
    destruct Hbinds as (d & c & Hbinds).
    destruct (classic (t' = t0)).
    + subst.
      forwards Heq: binds_update_same_inv Hbinds.
      inverts Heq.
      exists*.
    + forwards~ Hbinds''': binds_update_neq_inv Hbinds.
      destruct (classic (t = t0)).
      * subst.
        forwards Heq: binds_update_same_inv Hbinds'''.
        inverts Heq.
        exists*.
      * forwards~ Hbinds'''': binds_update_neq_inv Hbinds'''.
        exists*.
Qed.

Hint Resolve matching_threads_push_thread : vcm.

(* Completeness: every SharedMemory step is matched by a Linear step, and the
   resulting configurations still have the same expressions and locks. *)
Theorem linear_complete :
  forall log log' cfgSh cfgL cfgSh',
    wf_log log ->
    wf_cfg cfgL ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingLinear.describes log cfgL ->
    match cfgSh, cfgL with
    | (TSh, _, LSh), (TL, _, _, LL) => matching_threads TSh TL /\ LSh = LL
    end ->
    conflict_free log' ->
    LoggingSharedMemory.step (cfgSh, log) (cfgSh', log') ->
    exists cfgL',
      LoggingLinear.step (cfgL, log) (cfgL', log') /\
        match cfgSh', cfgL' with
        | (TSh', _, LSh'), (TL', _, _, LL') => matching_threads TSh' TL' /\ LSh' = LL'
        end.
Proof.
  introv Hwf HwfL HdescSh HdescL Hmatch Hcf Hstep.
  destruct cfgL as (((T & G) & g) & L).
  destruct HwfL as (HwfG & Htotal & Hgdom & Hmax & Hcorr).
  inverts Hstep;
    destruct Hmatch as (Hsame & ->);
    match goal with
    | H: binds ?T ?t (?ts', ?e) |- _ =>
        assert (Ht := H);
        apply Hsame in H as (d & c & Hbinds)
    end.
  - (* StepStart *)
    exists. splits; [ constructors* | simpls*].
  - (* StepEnd *)
    forwards (g' & Hfresh): exists_commit_fresh HwfG.
    asserts (T' & G' & Heq): (exists T' G', global_commit t g g' T G = (T', G')).
    {
      unfolds global_commit.
      forwards Hread: read_of_binds Hbinds.
      replace T[t] with (state_running, te_ret r, d, c).
      exists. reflexivity.
    }
    asserts Hcf': (lin_conflict_free d c g G).
    {
      admit. (* When replaying a conflict_free log, the resulting
      deltas will all be mergable with the latest global commit
      (and they will be disjoint, which we may need for proving
      this) *)
    }
    asserts* Hdom: (t \indom T0).
    exists. splits; [ constructors* | simpls*].
  - (* StepRead *)
    (* TODO: Cases on global vs. local read. Connect to play_log
    and see whether x is bound in D[t]. Having the log be
    conflict_free means that a local read is indeed the latest
    write and that is_latest_value gets the latest write *)
    admit.
  - (* StepWrite *)
    exists. splits; [ constructors* | simpls*].
  - (* StepSpawn *)
    forwards (g' & Hfresh): exists_commit_fresh HwfG.
    asserts Hndom: (t' \notindom T).
    {
      forwards Hdom: matching_threads_same_domain Hsame.
      rewrite* <- Hdom.
    }
    asserts Hcf': (lin_conflict_free d c g G).
    {
      admit.
    }
    asserts (T' & G' & Heq): (exists T' G', push_thread t t' g g' (T[t := (state_running, te_exp (K t'), d, c)][t' := (state_new, te_exp e', empty, 0)]) G = (T', G')).
    {
      exists. unfolds push_thread, global_commit.
      rewrite~ read_update_neq.
      rewrite read_update_same.
      rewrite~ read_update_neq.
      rewrite read_update_same.
      reflexivity.
    }
    asserts* Hdom: (t \indom T0[t:=(state_running, te_exp (K t'))][t':=(
      state_new, te_exp e')]).
    {
      rew_dom. rew_set. autos.
    }
    asserts* Hdom': (t' \indom T0[t:=(state_running, te_exp (K t'))][t':=(
      state_new, te_exp e')]).
    {
      rew_dom. rew_set. autos.
    }
    asserts* Hneq: (t <> t').
    exists. splits; [ constructors* | simpls*].
  - (* StepJoin *)
    apply Hsame in H4 as (d' & c' & Hbinds').
    asserts Hempty: (d = \{}).
    {
      destruct HdescSh as (_ & _ & Hend & _).
      asserts Hmem: (mem (event_end t') log).
      { apply* Hend. }
      destruct HdescL as (_ & _ & Hend' & _).
      apply Hend' in Hmem as (e' & d'' & Hbinds''').
      forwards~ Heq: binds_inj Hbinds Hbinds'''.
      inverts* Heq.
    }
    subst.
    asserts Hcf': (lin_conflict_free d' c' g G).
    {
      admit.
    }
    exists. splits; [ constructors* | simpls*].
  - (* StepLock *)
    asserts Hcf': (lin_conflict_free d c g G).
    {
      admit.
    }
    exists. splits; [ constructors* | simpls*].
  - forwards (g' & Hfresh): exists_commit_fresh HwfG.
    asserts (T' & G' & Heq): (exists T' G', global_commit t g g' T G = (T', G')).
    {
      unfolds global_commit.
      forwards Hread: read_of_binds Hbinds.
      replace T[t] with (state_running, te_exp e, d, c).
      exists. reflexivity.
    }
    asserts Hcf': (lin_conflict_free d c g G).
    {
      admit.
    }
    asserts* Hdom: (t \indom T0).
    exists. splits; [ constructors* | simpls*].
Admitted.

Theorem linear_sound :
  forall log log' cfgSh cfgL cfgL',
    wf_log log ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingLinear.describes log cfgL ->
    match cfgSh, cfgL with
    | (TSh, _, LSh), (TL, _, _, LL) => matching_threads TSh TL /\ LSh = LL
    end ->
    conflict_free log' ->
    LoggingLinear.step (cfgL, log) (cfgL', log') ->
    exists cfgSh',
      LoggingSharedMemory.step (cfgSh, log) (cfgSh', log') /\
        match cfgSh', cfgL' with
        | (TSh', _, LSh'), (TL', _, _, LL') => matching_threads TSh' TL' /\ LSh' = LL'
        end.
Proof.
  introv Hwf HdescSh HdescL Hmatch Hcf Hstep.
  destruct cfgSh as ((Tsh & Hp) & Lsh).
  inverts Hstep;
    destruct Hmatch as (Hsame & ->);
    try
    match goal with
    | H: binds ?T ?t (?ts, ?e, ?d, ?c) |- _ =>
        asserts Hex: (exists d c, binds T t (ts, e, d, c));
        [exists d; exists c; exact H|];
        apply Hsame in Hex as Hbinds; clear Hex
    end.
  + (* StepStart *)
    exists. split; [ constructors* | simpls*].
  + (* StepEnd *)
    asserts* Hdom: (t \indom Tsh).
    eexists. split; [ constructors* | simpls*].
  + (* StepReadLocal *)
    exists. splits.
    * constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescL as (_ & _ & _ & Hstart & _ & _ & (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC) & _).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      apply Hwrite.
      forwards Hcf': conflict_free_last_inv Hcf.
      forwards* Hbinds'': HdomD t.
      exists t.
      applys* conflict_free_last_local_write Hcf' Hplay Hbinds''.
    * simpls*.
  + (* StepReadGlobal *)
    exists. split.
    * constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescL as (_ & _ & _ & Hrun & _ & _ & (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC) & _).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      forwards* Heq: binds_inj Hbinds'.
      inverts Heq.
      asserts* ->: (c = TC[t]).
      apply Hwrite.
      asserts Hwfr: (wf_log (log & event_read t x v)).
      {
        lets [_ Hback]: Hrun t.
        forwards (Hms & Hmne): Hback.
        { exists*. }
        applys wf_log_read_last Hms Hmne Hwf.
      }
      asserts* Hdom: (t \indom T).
      forwards~ Hdom': HdomTC Hdom.
      applys* conflict_free_last_global_write Hcf Hwfr Hplay.
    * simpls*.
  + (* StepWrite *)
    eexists. split; [ constructors* | simpls*].
  + (* StepSpawn *)
    exists. split.
    * constructors*.
      forwards~ Heq: matching_threads_same_domain Hsame.
      rewrite* Heq.
    * asserts* Hdom: (t \indom Tsh[t:=(state_running, te_exp (K t'))][t':=(
      state_new, te_exp e')]).
    {
      rew_dom. rew_set. autos.
    }
    asserts* Hdom': (t' \indom Tsh[t:=(state_running, te_exp (K t'))][t':=(
      state_new, te_exp e')]).
    {
      rew_dom. rew_set. autos.
    }
    asserts* Hneq: (t <> t').
    simpls*.
  + (* StepJoin *)
    asserts* Hex: (exists d c, binds T t' (state_terminated, te_ret r, d, c)).
    apply Hsame in Hex.
    exists. split; [ constructors* | simpls*].
  + (* StepLock *)
    exists. split; [ constructors* | simpls*].
  + (* StepRelease *)
    asserts* Hdom: (t \indom Tsh).
    exists. split; [ constructors* | simpls*].
Qed.

Theorem linear_equiv :
  forall log log' cfgSh cfgL,
    wf_log log ->
    wf_cfg cfgL ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingLinear.describes log cfgL ->
    match cfgSh, cfgL with
    | (TSh, _, LSh), (TL, _, _, LL) => matching_threads TSh TL /\ LSh = LL
    end ->
    conflict_free log' ->
      (exists cfgSh', LoggingSharedMemory.step (cfgSh, log) (cfgSh', log')) <->
      (exists cfgL', LoggingLinear.step (cfgL, log) (cfgL', log')).
Proof.
  introv Hwf Hwfc HdescSh HdescL Hmatch Hcf.
  split.
  - introv (cfgSh' & Hstep).
    forwards* (cfgL' & Hstep' & _): linear_complete.
  - introv (cfgL' & Hstep).
    forwards* (cfgSh' & Hstep' & _): linear_sound.
Qed.
