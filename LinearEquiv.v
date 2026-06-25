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
    global_commit t g g' TL G = (TL', G') ->
    matching_threads TSh TL'.
Proof.
Admitted.

Hint Resolve matching_threads_global_commit : vcm.

Lemma matching_threads_push_thread :
  forall TSh TL TL' t g g' d G G',
    matching_threads TSh TL ->
    push_thread t g g' d TL G = (TL', G') ->
    matching_threads TSh TL'.
Proof.
Admitted.

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
      admit.
    }
    exists. splits; [ constructors* | simpls*].
  - (* StepRead *)
    (* TODO: Cases on global vs. local read *)
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
    admit.
Admitted.

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
  (* TODO: rework this equivalence for the graph-based Linear model: the logging
     [step] no longer has [pull]/[push] sub-relations or timestamps, and the
     config now carries the commit graph and global head [(T, G, g, L)].  The
     statement already targets the new definitions; the proof is left for the
     follow-up that also fleshes out [LoggingLinear.describes]'s graph conjuncts. *)
Admitted.
