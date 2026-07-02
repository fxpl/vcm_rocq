From Vcm Require Import Common.
From Vcm Require Import SharedMemory.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.
From Vcm Require Import LoggingSharedMemory.
From Vcm Require Import LoggingSharedMemoryFacts.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Branching.
From Vcm Require Import LoggingBranching.
From Vcm Require Import LoggingBranchingFacts.
From Vcm Require Import BranchingEquivLemmas.

Import Log.
Import LogFacts.

(* A SharedMemory thread map and a Branching thread map "match" when they bind
   every thread to the same (state, expression). The Branching side additionally
   carries a staging area [d] and commit pointer [c], but those are invisible to
   the relation. *)
Definition matching_threads (TSh : SharedMemory.threads) (TB : Branching.threads) :=
  forall t st e,
    binds TSh t (st, e) <-> exists d c, binds TB t (st, e, d, c).

(* Likewise for locks: same lock-state, the Branching side additionally carries a
   commit pointer. *)
Definition matching_locks (LSh : SharedMemory.locks) (LB : Branching.locks) :=
  forall l ls,
    binds LSh l ls <-> exists c, binds LB l (ls, c).

Lemma matching_threads_same_domain :
  forall TSh TB,
    matching_threads TSh TB ->
    dom TSh = dom TB.
Proof.
  introv Hmatch.
  simpls. unfolds SharedMemory.threads, Branching.threads.
  repeat rewrite dom_eq_set_of_binds.
  apply set_st_eq.
  intros t. splits.
  + introv ((st & e) & Hbinds).
    apply Hmatch in Hbinds as (d & c & Hbinds').
    exists*.
  + introv ((((st & e) & d ) & c) & Hbinds).
    exists (st, e). apply* Hmatch.
Qed.

Lemma matching_locks_same_domain :
  forall LSh LB,
    matching_locks LSh LB ->
    dom LSh = dom LB.
Proof.
  introv Hmatch.
  simpls. unfolds SharedMemory.locks, Branching.locks.
  repeat rewrite dom_eq_set_of_binds.
  apply set_st_eq.
  intros l. splits.
  + introv (ls & Hbinds).
    apply Hmatch in Hbinds as (c & Hbinds').
    exists*.
  + introv ((ls & c) & Hbinds).
    exists ls. apply* Hmatch.
Qed.

(* Changing only the staging area/commit pointer of an existing thread is
   invisible to [matching_threads]. This is the workhorse behind every
   commit-graph operation. *)
Lemma matching_threads_internal_update :
  forall TSh (T : Branching.threads) t st e d c dn cn,
    matching_threads TSh T ->
    binds T t (st, e, d, c) ->
    matching_threads TSh (T[t := (st, e, dn, cn)]).
Proof.
  introv Hm Hb. intros t0 sx ex. split.
  - intro Hbsh. apply Hm in Hbsh as (d0 & c0 & Hb0).
    destruct (classic (t0 = t)) as [-> | Hne].
    + forwards~ Heq: binds_inj Hb0 Hb. inverts Heq.
      exists*. apply binds_update_same.
    + exists. applys* binds_update_neq.
  - intros (d0 & c0 & Hb0). apply Hm. destruct (classic (t0 = t)) as [-> | Hne].
    + forwards Heq: binds_update_same_inv Hb0. inverts Heq.
      exists*.
    + forwards Hb0': binds_update_neq_inv Hb0 Hne. exists*.
Qed.

Lemma matching_locks_internal_update :
  forall LSh (L : Branching.locks) l ls c cn,
    matching_locks LSh L ->
    binds L l (ls, c) ->
    matching_locks LSh (L[l := (ls, cn)]).
Proof.
  introv Hm Hb. intros l0 lx. split.
  - intro Hbsh. apply Hm in Hbsh as (c0 & Hb0).
    destruct (classic (l0 = l)) as [-> | Hne].
    + forwards~ Heq: binds_inj Hb0 Hb. inverts Heq.
      exists. apply binds_update_same.
    + exists*. applys binds_update_neq Hne Hb0.
  - intros (c0 & Hb0). apply Hm. destruct (classic (l0 = l)) as [-> | Hne].
    + forwards Heq: binds_update_same_inv Hb0. inverts Heq.
      exists*.
    + forwards Hb0': binds_update_neq_inv Hb0 Hne. exists*.
Qed.

(* Updating one thread's (state, expression) on both sides preserves the match:
   the Branching side may additionally change [d]/[c]. *)
Lemma matching_threads_update_same :
  forall TSh TB t st e d c,
    matching_threads TSh TB ->
    matching_threads TSh[t := (st, e)] TB[t := (st, e, d, c)].
Proof.
  introv Hmatch.
  introv. splits; introv Hbinds.
  - destruct (classic (t = t0)).
    + subst. forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      exists. apply binds_update_same.
    + forwards~ Hbinds': binds_update_neq_inv Hbinds.
      apply Hmatch in Hbinds' as (d' & c' & Hbinds'').
      exists. apply* binds_update_neq.
  - destruct Hbinds as (d' & c' & Hbinds).
    destruct (classic (t = t0)).
    + subst. forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      apply binds_update_same.
    + forwards~ Hbinds': binds_update_neq_inv Hbinds.
      apply~ binds_update_neq. apply* Hmatch.
Qed.

Hint Resolve matching_threads_update_same : vcm.

(* Likewise for one lock. *)
Lemma matching_locks_update_same :
  forall LSh LB l ls c,
    matching_locks LSh LB ->
    matching_locks LSh[l := ls] LB[l := (ls, c)].
Proof.
  introv Hmatch.
  introv. splits; introv Hbinds.
  - destruct (classic (l = l0)).
    + subst. forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      exists. apply binds_update_same.
    + forwards~ Hbinds': binds_update_neq_inv Hbinds.
      apply Hmatch in Hbinds' as (c' & Hbinds'').
      exists. apply* binds_update_neq.
  - destruct Hbinds as (c' & Hbinds).
    destruct (classic (l = l0)).
    + subst. forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      apply binds_update_same.
    + forwards~ Hbinds': binds_update_neq_inv Hbinds.
      apply~ binds_update_neq. apply* Hmatch.
Qed.

Hint Resolve matching_locks_update_same : vcm.

(* The commit-graph operations only touch [d]/[c] of an existing (running)
   thread, so they leave the SharedMemory side untouched: [matching_threads TSh _]
   is preserved with [TSh] fixed. This is the "trick" that avoids the heavier
   [threads_agree] projection -- it threads the match straight through. *)
Lemma matching_threads_do_commit :
  forall TSh t hn T G T' G' e d c,
    matching_threads TSh T ->
    binds T t (state_running, e, d, c) ->
    do_commit t hn T G = (T', G') ->
    matching_threads TSh T'.
Proof.
  introv Hm Hb Heq. unfold do_commit in Heq.
  destruct (T[t]) as [[[s e0] d0] c0] eqn:HTt. inverts Heq.
  lets Hin: (indom_of_binds Hb).
  forwards* Hbt: binds_of_indom_read Hin HTt.
  forwards* Heq2: binds_inj Hb Hbt. inverts Heq2.
  applys matching_threads_internal_update Hm Hb.
Qed.

Hint Resolve matching_threads_do_commit : vcm.

Lemma matching_threads_do_merge :
  forall TSh t h hn T G T' G' st e d c,
    matching_threads TSh T ->
    binds T t (st, e, d, c) ->
    do_merge t h hn T G = (T', G') ->
    matching_threads TSh T'.
Proof.
  introv Hm Hb Heq. unfold do_merge in Heq.
  destruct (T[t]) as [[[s e0] d0] c0] eqn:HTt. inverts Heq.
  lets Hin: (indom_of_binds Hb).
  forwards* Hbt: binds_of_indom_read Hin HTt.
  forwards* Heq2: binds_inj Hb Hbt. inverts Heq2.
  applys matching_threads_internal_update Hm Hb.
Qed.

Lemma matching_threads_pull_thread :
  forall TSh t t' hn T G T' G' st e d c,
    matching_threads TSh T ->
    binds T t (st, e, d, c) ->
    pull_thread t t' hn T G = (T', G') ->
    matching_threads TSh T'.
Proof.
  introv Hm Hb Heq. unfold pull_thread in Heq.
  destruct (T[t']) as [[[ts' e'] d'] c'].
  applys matching_threads_do_merge Hm Hb Heq.
Qed.

Hint Resolve matching_threads_pull_thread : vcm.

Lemma matching_threads_pull_lock :
  forall TSh t l hn T G L T' G' st e d c,
    matching_threads TSh T ->
    binds T t (st, e, d, c) ->
    pull_lock t l hn T G L = (T', G') ->
    matching_threads TSh T'.
Proof.
  introv Hm Hb Heq. unfold pull_lock in Heq.
  destruct (lock_read L l) as [ls c'].
  applys matching_threads_do_merge Hm Hb Heq.
Qed.

Hint Resolve matching_threads_pull_lock : vcm.

Lemma matching_threads_push_thread :
  forall TSh t t' hn T G T' G' e d c st' e' d' c',
    matching_threads TSh T ->
    binds T t (state_running, e, d, c) ->
    binds T t' (st', e', d', c') ->
    push_thread t t' hn T G = (T', G') ->
    matching_threads TSh T'.
Proof.
  introv Hm Hbt Hbt' Heq. unfold push_thread in Heq.
  destruct (do_commit t hn T G) as (T'' & G'') eqn:HC.
  forwards Hm'': matching_threads_do_commit Hm Hbt HC.
  asserts HbSh: (binds TSh t' (st', e')). { apply (Hm t' st' e'). exists d' c'. exact Hbt'. }
  forwards (d2 & c2 & Hbt''): (proj1 (Hm'' t' st' e') HbSh).
  destruct (T''[t']) as [[[ts2 e2] d3] c3] eqn:HT'. inverts Heq.
  lets Hin'': (indom_of_binds Hbt'').
  forwards Hbt2: binds_of_indom_read Hin'' HT'.
  forwards~ Heq2: binds_inj Hbt'' Hbt2. inverts Heq2.
  applys matching_threads_internal_update Hm'' Hbt''.
Qed.

Hint Resolve matching_threads_push_thread : vcm.

Lemma matching_threads_push_lock :
  forall TSh t l hn T G L T' G' L'' e d c,
    matching_threads TSh T ->
    binds T t (state_running, e, d, c) ->
    push_lock t l hn T G L = (T', G', L'') ->
    matching_threads TSh T'.
Proof.
  introv Hm Hb Heq. unfold push_lock in Heq.
  destruct (do_commit t hn T G) as (T'' & G'') eqn:HC.
  destruct (L[l]) as [ls0 c0]. inverts Heq.
  applys matching_threads_do_commit Hm Hb HC.
Qed.

Hint Resolve matching_threads_push_lock : vcm.

Lemma matching_locks_push_lock :
  forall LSh t l hn T G L T' G' L'' ls c,
    matching_locks LSh L ->
    binds L l (ls, c) ->
    push_lock t l hn T G L = (T', G', L'') ->
    matching_locks LSh L''.
Proof.
  introv Hm Hb Heq. unfold push_lock in Heq.
  destruct (do_commit t hn T G) as (T'' & G'').
  destruct (L[l]) as [ls0 c0] eqn:HL. inverts Heq.
  lets Hin: (indom_of_binds Hb).
  forwards* Hbl0: binds_of_indom_read Hin HL.
  forwards* Heq2: binds_inj Hb Hbl0. inverts Heq2.
  applys matching_locks_internal_update Hm Hb.
Qed.

Hint Resolve matching_locks_push_lock : vcm.

(* [matching_locks] is not an independent assumption: a lock's state is fully
   determined by its touch-filter in the log, so two configurations describing the
   same log necessarily agree on locks.  (The thread expressions, by contrast, are
   only existentially constrained by [describes], so [matching_threads] genuinely
   has to be assumed.) *)
Lemma matching_locks_describes :
  forall log cfgSh cfgB,
    LoggingSharedMemory.describes log cfgSh ->
    LoggingBranching.describes log cfgB ->
    match cfgSh, cfgB with
    | (_, _, LSh), (_, _, LB) => matching_locks LSh LB
    end.
Proof.
  introv HdescSh HdescB.
  destruct cfgSh as ((TSh & HSh) & LSh). destruct cfgB as ((TB & G) & LB).
  destruct HdescSh as (_ & _ & _ & _ & HShlocked & HShfree & _).
  destruct HdescB as (_ & _ & _ & _ & HBlocked & HBfree & _).
  intros l ls. destruct ls as [ | t].
  - (* ls_free: the filter ends in an [event_unlock] on both sides *)
    split.
    + introv Hb. apply (HBfree l). apply (HShfree l). exact Hb.
    + introv (c & Hb). apply (HShfree l). apply (HBfree l). exists* c.
  - (* ls_held t: the filter ends in [event_lock t l] on both sides *)
    split.
    + introv Hb. apply (HBlocked t l). apply (HShlocked t l). exact Hb.
    + introv (c & Hb). apply (HShlocked t l). apply (HBlocked t l). exists* c.
Qed.

(* Completeness: every SharedMemory step is matched by a Branching step, and the
   resulting configurations still match on threads. *)
Theorem branching_complete :
  forall log log' cfgSh cfgB cfgSh',
    wf_log log ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingBranching.describes log cfgB ->
    match cfgSh, cfgB with
    | (TSh, _, _), (TB, _, _) => matching_threads TSh TB
    end ->
    conflict_free log' ->
    LoggingSharedMemory.step (cfgSh, log) (cfgSh', log') ->
    exists cfgB',
      LoggingBranching.step (cfgB, log) (cfgB', log') /\
      match cfgSh', cfgB' with
      | (TSh', _, _), (TB', _, _) => matching_threads TSh' TB'
      end.
Proof.
  introv Hwf HdescSh HdescB Hthr Hcf Hstep.
  destruct cfgB as [(T & G) L].
  forwards HwfB: describes_wf_cfg HdescB.
  destruct HwfB as (HwfG & HwfRoot & _ & Hlockcommits).
  forwards Hlck: matching_locks_describes HdescSh HdescB.
  inverts Hstep;
    match goal with
    | H: binds ?T ?t (?ts', ?e) |- _ =>
        assert (Ht := H);
        apply Hthr in H as (d & c & Hbinds)
    end.
  + (* StepStart *)
    exists. splits; [ constructors* | simpls*].
  + (* StepEnd *)
    forwards (c' & Hfresh): exists_commit_fresh HwfG.
    asserts (T' & G' & Hcommit): (exists T' G', do_commit t c' T G = (T', G')).
    {
      exists. unfolds do_commit.
      forwards Hread: read_of_binds Hbinds.
      replace T[t] with (state_running, te_ret r, d, c).
      reflexivity.
    }
    exists. splits; [ constructors* | simpls*].
  + (* StepRead *)
    destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
    apply Hwrite in H6 as (t' & log'0 & Hfilter).
    destruct HdescB as (_ & _ & _ & Hrun & _ & _ &
      (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC)).
    lets Htin: (indom_of_binds Hbinds).
    forwards (ts0 & e0 & Hbd): Hdelta Htin.
    forwards* Heqdt: binds_inj Hbinds Hbd. inverts Heqdt.
    forwards Hcflog: conflict_free_last_inv Hcf.
    destruct (classic (x \indom (D[t]))) as [Hin | Hnin].
    * (* local (uncommitted) read: [x] is in [t]'s delta *)
      asserts Hdt: (t \indom D). { applys HdomD Htin. }
      asserts Hbdi: (binds (D[t]) x (D[t][x])).
      { applys binds_of_indom_read Hin; (reflexivity || typeclass). }
      forwards (log'' & Hfilt2): conflict_free_last_local_write Hcflog Hplay Hdt Hbdi.
      rewrite Hfilter in Hfilt2.
      forwards (_ & Heqw): last_eq_last_inv Hfilt2. inverts Heqw.
      exists. split; [ applys StepReadLocal Hbinds; [ eassumption | exact Hbdi ] | simpls* ].
    * (* global (committed) read: [x] is visible as the latest committed value *)
      lets [_ Hback]: Hrun t. forwards (Hms & Hmne): Hback. { do 3 eexists. exact Hbinds. }
      asserts Hwfr: (wf_log (log & event_read t x v)). { applys wf_log_read_last Hms Hmne Hwf. }
      forwards Hlv: last_global_write_latest_value Hcf Hwfr Hplay Hnin Hfilter.
      exists. split; [ applys StepReadGlobal Hbinds; [ eassumption | exact Hnin | exact Hlv ] | simpls* ].
  + (* StepWrite *)
    exists. splits; [ constructors* | simpls*].
  + (* StepSpawn *)
    forwards (c' & Hfresh): exists_commit_fresh HwfG.
    forwards Heq: matching_threads_same_domain Hthr.
    rewrite Heq in H6.
    asserts* Hneq: (t <> t').
    asserts (T' & G' & Hpush): (exists T' G', push_thread t t' c' T[t:=(state_running, K t', d, c)][t':=(state_new, te_exp e', \{}, 0)] G = (T', G')).
    {
      exists. unfolds push_thread, do_commit.
      rewrite~ read_update_neq.
      rewrite read_update_same.
      rewrite~ read_update_neq.
      rewrite read_update_same.
      reflexivity.
    }
    asserts HbiTt': (binds (T[t:=(state_running, K t', d, c)][t':=(state_new, te_exp e', \{}, 0)]) t' (state_new, te_exp e', \{}, 0)).
    { apply binds_update_same. }
    asserts HbiTt: (binds (T[t:=(state_running, K t', d, c)][t':=(state_new, te_exp e', \{}, 0)]) t (state_running, K t', d, c)).
    { applys binds_update_neq Hneq. apply binds_update_same. }
    clears HdescB HdescSh. (* Implication in describes tanks proof search*)
    exists. splits; [ constructors* | simpls*].
  + (* StepJoin *)
    forwards (c'' & Hfresh): exists_commit_fresh HwfG.
    apply Hthr in H4 as (d' & c' & Hbinds').
    asserts (T' & G' & Hpull & Hbinds''): (exists T' G', pull_thread t t' c'' T G = (T', G') /\
                                                         binds T' t (state_running, te_exp e, d', c'')).
    {
      exists. unfolds pull_thread, do_merge.
      forwards Hread: read_of_binds Hbinds.
      replace T[t'] with (state_terminated, te_ret r, d, c).
      forwards Hread': read_of_binds Hbinds'.
      replace T[t] with (state_running, te_exp e, d', c').
      splits.
      - reflexivity.
      - apply binds_update_same.
    }
    asserts Hempty: (d = \{}).
    {
      destruct HdescSh as (_ & _ & Hend & _).
      asserts Hmem: (mem (event_end t') log).
      { apply* Hend. }
      destruct HdescB as (_ & _ & Hend' & _).
      apply Hend' in Hmem as (e' & d'' & Hbinds''').
      forwards~ Heq: binds_inj Hbinds Hbinds'''.
      inverts* Heq.
    }
    substs.
    asserts Hmerge: (conflict_free_merge d' c' c G).
    {
      destruct HdescB as (_ & _ & _ & _ & _ & _ &
        (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC)).
      forwards Hcflog: conflict_free_last_inv Hcf.
      lets HtT: (indom_of_binds Hbinds').
      forwards (ts0 & e0 & Hbdt): Hdelta HtT.
      forwards* Heqt: binds_inj Hbinds' Hbdt. inverts Heqt.
      lets Ht'T: (indom_of_binds Hbinds).
      forwards (ts1 & e1 & Hbdt'): Hdelta Ht'T.
      forwards* Heqt': binds_inj Hbinds Hbdt'. inverts Heqt'.
      forwards Hpgwf: play_log_graph_wf Hplay. destruct Hpgwf as (_ & HTCdom & _).
      applys conflict_free_merge_holds Hwf Hcflog Hplay;
        [ applys HdomD HtT | applys HdomTC HtT | applys HTCdom; applys HdomTC Ht'T ].
    }
    clears HdescSh HdescB.
    exists. splits; [ constructors* | simpls*].
  + (* StepLock *)
    forwards (c'' & Hfresh): exists_commit_fresh HwfG.
    asserts (c' & Hlockeq & Hc'indom): (exists c', lock_read L l0 = (ls_free, c') /\ graph_indom G c').
    {
      match goal with Hpre : SharedMemory.lock_read L0 l0 = ls_free |- _ => rename Hpre into Hread end.
      unfold SharedMemory.lock_read, read_default in Hread.
      destruct (classic (l0 \indom L0)) as [Hindom0|Hnotin0].
      - asserts Hb0: (binds L0 l0 ls_free).
        { applys binds_of_indom_read Hindom0. case_if* in Hread. }
        apply Hlck in Hb0 as (c' & Hlock).
        exists c'. split.
        + lets Hindom: (indom_of_binds Hlock).
          unfold lock_read, read_default. case_if*.
          rewrite~ (read_of_binds Hlock).
        + applys Hlockcommits Hlock.
      - asserts HnotinL: (l0 \notindom L).
        { forwards Heqd: matching_locks_same_domain Hlck. rewrite <- Heqd. exact Hnotin0. }
        exists root_commit. split.
        + unfold lock_read, read_default. case_if.
          -- false. applys HnotinL. exact C.
          -- reflexivity.
        + exact HwfRoot.
    }
    asserts Hmerge: (conflict_free_merge d c c' G).
    {
      destruct HdescB as (_ & _ & _ & _ & _ & _ &
        (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC)).
      forwards Hcflog: conflict_free_last_inv Hcf.
      lets HtT: (indom_of_binds Hbinds).
      forwards (ts0 & e0 & Hbdt): Hdelta HtT.
      forwards* Heqt: binds_inj Hbinds Hbdt. inverts Heqt.
      applys conflict_free_merge_holds Hwf Hcflog Hplay;
        [ applys HdomD HtT | applys HdomTC HtT | exact Hc'indom ].
    }
    asserts (T' & G' & Hpull & Hbinds''): (exists T' G', pull_lock t l0 c'' T G L = (T', G') /\
                                                           binds T' t (state_running, te_exp e, d, c'')).
    {
      exists. unfolds pull_lock, do_merge.
      rewrite Hlockeq.
      forwards Hread': read_of_binds Hbinds.
      replace T[t] with (state_running, te_exp e, d, c).
      splits.
      - reflexivity.
      - apply binds_update_same.
    }
    clears HdescSh HdescB.
    exists. splits; [ constructors* | simpls*].
  + (* StepRelease *)
    forwards (c'' & Hfresh): exists_commit_fresh HwfG.
    asserts (c' & HbindsL): (exists c', binds L l0 (ls_held t, c')).
    {
      asserts Hb0: (binds L0 l0 (ls_held t)).
      { match goal with Hpre : SharedMemory.lock_read L0 l0 = ls_held t |- _ => rename Hpre into Hread end.
        unfold SharedMemory.lock_read in Hread.
        destruct (classic (l0 \indom L0)) as [Hindom0|Hnotin0].
        - applys binds_of_indom_read Hindom0. rewrite (read_default_indom Hindom0) in Hread. exact Hread.
        - false. rewrite (read_default_notindom Hnotin0) in Hread. inverts Hread. }
      destruct HdescSh as (_ & _ & _ & _ & Hlock & _).
      apply Hlock in Hb0 as Hex.
      destruct HdescB as (_ & _ & _ & _ & Hlock' & _).
      apply* Hlock'.
    }
    asserts (T' & G' & L' & Hpush & Hbinds'): (exists T' G' L', push_lock t l0 c'' T G L = (T', G', L') /\ binds T' t (state_running, te_exp e, \{}, c'')).
    {
      exists. unfolds push_lock, do_commit.
      forwards Hread: read_of_binds Hbinds.
      replace T[t] with (state_running, te_exp e, d, c).
      forwards Hread': read_of_binds HbindsL.
      replace L[l0] with (ls_held t, c').
      splits.
      - reflexivity.
      - apply binds_update_same.
    }
    clears HdescSh HdescB.
    exists. splits; [ constructors* | simpls*].
Qed.

(* Soundness: every Branching step is matched by a SharedMemory step, with the
   resulting configurations again matching on threads and locks. *)
Theorem branching_sound :
  forall log log' cfgSh cfgB cfgB',
    wf_log log ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingBranching.describes log cfgB ->
    match cfgSh, cfgB with
    | (TSh, _, _), (TB, _, _) => matching_threads TSh TB
    end ->
    conflict_free log' ->
    LoggingBranching.step (cfgB, log) (cfgB', log') ->
    exists cfgSh',
      LoggingSharedMemory.step (cfgSh, log) (cfgSh', log') /\
      match cfgSh', cfgB' with
      | (TSh', _, _), (TB', _, _) => matching_threads TSh' TB'
      end.
Proof.
  introv Hwf HdescSh HdescB Hthr Hcf Hstep.
  destruct cfgSh as ((Tsh & Hp) & Lsh).
  forwards Hlck: matching_locks_describes HdescSh HdescB.
  inverts Hstep;
    try
    match goal with
    | H: binds ?T ?t (?ts, ?e, ?d, ?c) |- _ =>
        asserts Hex: (exists d c, binds T t (ts, e, d, c));
        [exists d; exists c; exact H|];
        apply Hthr in Hex as Hbinds; clear Hex
    end.
  + (* StepStart *)
    clears HdescSh HdescB.
    exists. split; [ constructors* | simpls*].
  + (* StepEnd *)
    clears HdescSh HdescB.
    exists. split; [ constructors* | simpls*].
  + (* StepReadLocal *)
    exists. split.
    { constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescB as (_ & _ & _ & Hstart & _ & _ & (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC)).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      apply Hwrite.
      forwards Hcf': conflict_free_last_inv Hcf.
      forwards* Hbinds'': HdomD t.
      forwards* Hex: conflict_free_last_local_write Hplay. }
    clears HdescSh HdescB.
    simpls*.
  + (* StepReadGlobal *)
    exists. split.
    {
      constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescB as (_ & _ & _ & Hrun & _ & _ & (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC)).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      forwards* Heq: binds_inj Hbinds'.
      inverts Heq.
      asserts* ->: (c = TC[t]).
      apply Hwrite.
      asserts Hwfr: (wf_log (log & event_read t x v)).
      {
        lets [_ Hback]: Hrun t.
        forwards* (Hms & Hmne): Hback.
        applys wf_log_read_last Hms Hmne Hwf.
      }
      asserts* Hdom: (t \indom T).
      forwards~ Hdom': HdomTC Hdom.
      forwards* Hex: conflict_free_last_global_write Hcf Hwfr Hplay.
    }
    clears HdescSh HdescB.
    simpls*.
  + (* StepWrite *)
    clears HdescSh HdescB.
    exists. split; [ constructors* | simpls*].
  + (* StepSpawn *)
    forwards Heq: matching_threads_same_domain Hthr.
    asserts* Hneq: (t <> t').
    asserts Hnd: (t' \notindom Tsh). { rewrite Heq. assumption. }
    match goal with
    | Hp : push_thread t t' ?hn ?iT G = (?TT, ?GG) |- _ =>
        asserts HbiTt: (binds iT t (state_running, K t', d, c));
        [ applys binds_update_neq; [ | apply binds_update_same ]; auto |];
        asserts HbiTt': (binds iT t' (state_new, te_exp e', \{}, 0));
        [ apply binds_update_same |]
    end.
    clears HdescSh HdescB.
    exists. split; [ constructors* | simpls*].
  + (* StepJoin *)
    asserts* Hex: (exists d c, binds T t' (state_terminated, te_ret r, d, c)).
    apply Hthr in Hex.
    clears HdescSh HdescB.
    exists. split; [ constructors* | simpls*].
  + (* StepLock: unified constructor -- a never-touched lock defaults to
       [(ls_free, root_commit)], matching [SharedMemory.lock_read]'s own
       default of [ls_free] *)
    exists. split.
    {
      constructors*.
      unfold SharedMemory.lock_read.
      destruct (classic (l0 \indom L)) as [Hindom|Hnotin].
      - asserts Hb: (binds L l0 (ls_free, c')).
        { applys binds_of_indom_read Hindom.
          transitivity (lock_read L l0).
          - symmetry. exact (read_default_indom Hindom).
          - exact H5. }
        asserts HbSh: (binds Lsh l0 ls_free).
        { apply Hlck. exists c'. exact Hb. }
        transitivity (Lsh[l0]).
        + exact (read_default_indom (indom_of_binds HbSh)).
        + exact (read_of_binds HbSh).
      - forwards Heqd: matching_locks_same_domain Hlck.
        asserts HnotinSh: (l0 \notindom Lsh). { rewrite Heqd. exact Hnotin. }
        exact (read_default_notindom HnotinSh).
    }
    clears HdescSh HdescB.
    simpls*.
  + (* StepRelease *)
    exists. split.
    {
      constructors*.
      unfold SharedMemory.lock_read.
      match goal with Hpre : binds L l0 (ls_held t, ?cc) |- _ =>
        asserts HbSh: (binds Lsh l0 (ls_held t));
        [ apply Hlck; exists cc; exact Hpre | ]
      end.
      transitivity (Lsh[l0]).
      + exact (read_default_indom (indom_of_binds HbSh)).
      + exact (read_of_binds HbSh).
    }
    clears HdescSh HdescB.
    simpls*.
Qed.

(* The original equivalence is the conjunction of the two directions. *)
Corollary branching_equiv :
  forall log log' cfgSh cfgB,
    wf_log log ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingBranching.describes log cfgB ->
    match cfgSh, cfgB with
    | (TSh, _, _), (TB, _, _) => matching_threads TSh TB
    end ->
    conflict_free log' ->
      (exists cfgSh', LoggingSharedMemory.step (cfgSh, log) (cfgSh', log')) <->
      (exists cfgB', LoggingBranching.step (cfgB, log) (cfgB', log')).
Proof.
  introv Hwf HdescSh HdescB Hmatch Hcf. split.
  - introv (cfgSh' & Hstep).
    forwards* (cfgB' & Hb & _): branching_complete.
  - introv (cfgB' & Hstep).
    forwards* (cfgSh' & Hb & _): branching_sound.
Qed.
