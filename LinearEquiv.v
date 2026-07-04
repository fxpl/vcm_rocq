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

(* Completeness: every SharedMemory step is matched by a Linear step, and the
   resulting configurations still have the same expressions and locks. *)
Theorem linear_complete :
  forall log log' cfgSh cfgL cfgSh',
    wf_log log ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingLinear.describes log cfgL ->
    match cfgSh, cfgL with
    | (TSh, _, LSh), (TL, _, LL) => matching_threads TSh TL /\ LSh = LL
    end ->
    conflict_free log' ->
    LoggingSharedMemory.step (cfgSh, log) (cfgSh', log') ->
    exists cfgL',
      LoggingLinear.step (cfgL, log) (cfgL', log') /\
        match cfgSh', cfgL' with
        | (TSh', _, LSh'), (TL', _, LL') => matching_threads TSh' TL' /\ LSh' = LL'
        end.
Proof.
  introv Hwf HdescSh HdescL Hmatch Hcf Hstep.
  destruct cfgL as ((T & G) & L).
  forwards HwfL: describes_wf_cfg HdescL.
  destruct HwfL as (HwfG & Htotal & Hhex & Hcorr).
  destruct Hhex as (g & Hhead).
  inverts Hstep;
    destruct Hmatch as (Hsame & ->);
    match goal with
    | H: binds ?T ?t (?ts', ?e) |- _ =>
        assert (Ht := H);
        apply Hsame in H as (d & c & Hbinds)
    end.
  - (* StepStart *)
    clears HdescSh HdescL.
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
      destruct HdescL as (_ & _ & _ & _ & _ & _ & (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
      forwards (_ & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hhead. subst g0.
      forwards Hcflog: conflict_free_last_inv Hcf.
      lets HtT: (indom_of_binds Hbinds).
      forwards (ts0 & e0 & Hbdt): Hdelta HtT.
      forwards* Heqt: binds_inj Hbinds Hbdt. inverts Heqt.
      forwards Hpgwf: play_log_graph_wf Hplay.
      destruct Hpgwf as (_ & HTCdom).
      applys* lin_conflict_free_holds.
    }
    asserts* Hdom: (t \indom T0).
    clears HdescSh HdescL.
    exists. splits; [ constructors* | simpls*].
  - (* StepRead *)
    destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
    apply Hwrite in H6 as (t' & log'0 & Hfilter).
    destruct HdescL as (_ & _ & _ & Hrun & _ & _ & (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
    forwards (_ & _ & Hhead0): play_log_head_wf Hplay.
    forwards Heqg0: is_global_head_unique HwfG Hhead0 Hhead. subst g0.
    lets Htin: (indom_of_binds Hbinds).
    forwards (ts0 & e0 & Hbd): Hdelta Htin.
    forwards* Heqdt: binds_inj Hbinds Hbd. inverts Heqdt.
    forwards Hcflog: conflict_free_last_inv Hcf.
    destruct (classic (x \in Volatiles)) as [Hxvol | Hnv].
    * (* volatile read: always a pull (fast-forward to [g]), regardless of
         [D[t]] -- a volatile variable is never pending in a delta *)
      asserts Hdt: (t \indom D). { applys HdomD Htin. }
      asserts HtTC: (t \indom TC). { applys HdomTC Htin. }
      asserts Hlcf: (lin_conflict_free (D[t]) (TC[t]) g G).
      { applys lin_conflict_free_holds Hwf Hcflog Hplay Hdt HtTC. }
      asserts Hexfilter: (exists tw log', LibList.filter (fun e => writes_variable x e) log = log' & event_write tw x v).
      { exists t' log'0. exact Hfilter. }
      forwards Hlv: is_latest_value_after_volatile_pull Hwf Hcflog Hplay Hxvol Hexfilter.
      exists. split;
        [ applys (>> StepReadVolatile Hbinds H5 Hxvol Hhead Hlcf Hlv)
        | simpls* ].
    * (* non-volatile read: local (in [D[t]]) or global *)
      destruct (classic (x \indom (D[t]))) as [Hin | Hnin].
      { (* local (uncommitted) read: [x] is in [t]'s delta *)
        asserts Hdt: (t \indom D). { applys HdomD Htin. }
        asserts Hbdi: (binds (D[t]) x (D[t][x])).
        { applys* binds_of_indom_read Hin. }
        forwards (log'' & Hfilt2): conflict_free_last_local_write Hcflog Hplay Hdt Hbdi.
        rewrite Hfilter in Hfilt2.
        forwards (_ & Heqw): last_eq_last_inv Hfilt2. inverts Heqw.
        exists. split; [ applys StepReadLocal Hbinds; [ eassumption | exact Hnv | exact Hbdi ] |].
        simpls*. }
      { (* global (committed) read: [x] is visible as the latest committed value *)
        lets [_ Hback]: Hrun t. forwards* (Hms & Hmne): Hback.
        asserts Hwfr: (wf_log (log & event_read t x v)). { applys wf_log_read_last Hms Hmne Hwf. }
        forwards Hlv: (>> last_global_write_latest_value Hnv Hcf Hwfr Hplay Hnin Hfilter).
        exists. split; [ applys StepReadGlobal Hbinds; [ eassumption | exact Hnv | exact Hnin | exact Hlv ] |].
        simpls*. }
  - (* StepWrite *)
    destruct HdescL as (_ & _ & _ & _ & _ & _ & (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
    forwards (_ & _ & Hhead0): play_log_head_wf Hplay.
    forwards Heqg0: is_global_head_unique HwfG Hhead0 Hhead. subst g0.
    lets Htin: (indom_of_binds Hbinds).
    forwards (ts0 & e0 & Hbd): Hdelta Htin.
    forwards* Heqdt: binds_inj Hbinds Hbd. inverts Heqdt.
    forwards Hcflog: conflict_free_last_inv Hcf.
    destruct (classic (x \in Volatiles)) as [Hxvol | Hnv].
    * (* volatile write: conflict-check then commit in one step (no
         [is_latest_value] obligation, unlike the read side -- purely
         mechanical, mirroring [StepEnd]'s [global_commit] handling above but
         on a diff pre-updated with [x := v]) *)
      asserts Hdt: (t \indom D). { applys HdomD Htin. }
      asserts HtTC: (t \indom TC). { applys HdomTC Htin. }
      asserts Hlcf: (lin_conflict_free (D[t]) (TC[t]) g G).
      { applys lin_conflict_free_holds Hwf Hcflog Hplay Hdt HtTC. }
      forwards (g' & Hfresh): exists_commit_fresh HwfG.
      asserts (T' & G' & Heq): (exists T' G', global_commit t g g'
          (T[t := (state_running, te_exp e, D[t][x := v], TC[t])]) G = (T', G')).
      { unfolds global_commit. rewrite read_update_same. exists. reflexivity. }
      asserts Hdom0: (t \indom (T0[t := (state_running, te_exp e)])).
      { applys indom_update_same. typeclass. }
      asserts Hmt1: (matching_threads (T0[t := (state_running, te_exp e)])
                       (T[t := (state_running, te_exp e, D[t][x := v], TC[t])])).
      { applys matching_threads_update_same Hsame. }
      asserts Hmt2: (matching_threads (T0[t := (state_running, te_exp e)]) T').
      { applys matching_threads_global_commit Hmt1 Hdom0 Heq. }
      asserts Hmt3: (matching_threads (T0[t := (state_running, te_exp e)][t := (state_running, K void)])
                       (T'[t := (state_running, K void, empty, g')])).
      { applys matching_threads_update_same Hmt2. }
      rewrite update_update in Hmt3.
      exists (T'[t := (state_running, K void, empty, g')], G', L).
      apply conj.
      { eapply StepWriteVolatile;
        [ exact Hbinds | exact H5 | exact Hxvol | exact Hhead | exact Hlcf | exact Hfresh | exact Heq ]. }
      { apply conj; [ exact Hmt3 | reflexivity ]. }
      typeclass.
    * (* non-volatile write: unconditional, as before *)
      exists. splits; [ applys StepWrite Hbinds; [ eassumption | exact Hnv ] | simpls* ].
  - (* StepSpawn *)
    forwards (g' & Hfresh): exists_commit_fresh HwfG.
    asserts Hndom: (t' \notindom T).
    {
      forwards Hdom: matching_threads_same_domain Hsame.
      rewrite* <- Hdom.
    }
    asserts Hcf': (lin_conflict_free d c g G).
    {
      destruct HdescL as (_ & _ & _ & _ & _ & _ & (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
      forwards (_ & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hhead. subst g0.
      forwards Hcflog: conflict_free_last_inv Hcf.
      lets HtT: (indom_of_binds Hbinds).
      forwards (ts0 & e0 & Hbdt): Hdelta HtT.
      forwards* Heqt: binds_inj Hbinds Hbdt. inverts Heqt.
      forwards Hpgwf: play_log_graph_wf Hplay.
      destruct Hpgwf as (_ & HTCdom).
      applys* lin_conflict_free_holds.
    }
    asserts (T' & G' & Heq): (exists T' G', global_commit t g g' T[t:=(state_running, K t', d, c)][t':=(
    state_new, te_exp e', \{}, g')] G = (T', G')).
    {
      asserts* Hneq: (t <> t').
      unfolds global_commit.
      rewrite~ read_update_neq.
      rewrite~ read_update_same.
      exists. reflexivity.
    }
    asserts* Hdom: (t \indom T0[t:=(state_running, K t')][t':=(
      state_new, te_exp e')]).
    {
      rew_dom. rew_set. autos.
    }
    asserts* Hdom': (t' \indom T0[t:=(state_running, K t')][t':=(
      state_new, te_exp e')]).
    {
      rew_dom. rew_set. autos.
    }
    asserts* Hneq: (t <> t').
    clears HdescSh HdescL.
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
      destruct HdescL as (_ & _ & _ & _ & _ & _ & (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
      forwards (_ & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hhead. subst g0.
      forwards Hcflog: conflict_free_last_inv Hcf.
      lets HtT: (indom_of_binds Hbinds').
      forwards (ts0 & e0 & Hbdt): Hdelta HtT.
      forwards* Heqt: binds_inj Hbinds' Hbdt. inverts Heqt.
      forwards Hpgwf: play_log_graph_wf Hplay.
      destruct Hpgwf as (_ & HTCdom).
      forwards*: lin_conflict_free_holds.
    }
    clears HdescSh HdescL.
    exists. splits; [ constructors* | simpls*].
  - (* StepLock *)
    asserts Hcf': (lin_conflict_free d c g G).
    {
      destruct HdescL as (_ & _ & _ & _ & _ & _ & (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
      forwards (_ & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hhead. subst g0.
      forwards Hcflog: conflict_free_last_inv Hcf.
      lets HtT: (indom_of_binds Hbinds).
      forwards (ts0 & e0 & Hbdt): Hdelta HtT.
      forwards* Heqt: binds_inj Hbinds Hbdt. inverts Heqt.
      forwards Hpgwf: play_log_graph_wf Hplay.
      destruct Hpgwf as (_ & HTCdom).
      applys* lin_conflict_free_holds.
    }
    clears HdescSh HdescL.
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
      destruct HdescL as (_ & _ & _ & _ & _ & _ & (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
      forwards (_ & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hhead. subst g0.
      forwards Hcflog: conflict_free_last_inv Hcf.
      lets HtT: (indom_of_binds Hbinds).
      forwards (ts0 & e0 & Hbdt): Hdelta HtT.
      forwards* Heqt: binds_inj Hbinds Hbdt. inverts Heqt.
      forwards Hpgwf: play_log_graph_wf Hplay.
      destruct Hpgwf as (_ & HTCdom).
      applys* lin_conflict_free_holds.
    }
    asserts* Hdom: (t \indom T0).
    clears HdescSh HdescL.
    exists. splits; [ constructors* | simpls*].
Qed.

Theorem linear_sound :
  forall log log' cfgSh cfgL cfgL',
    wf_log log ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingLinear.describes log cfgL ->
    match cfgSh, cfgL with
    | (TSh, _, LSh), (TL, _, LL) => matching_threads TSh TL /\ LSh = LL
    end ->
    conflict_free log' ->
    LoggingLinear.step (cfgL, log) (cfgL', log') ->
    exists cfgSh',
      LoggingSharedMemory.step (cfgSh, log) (cfgSh', log') /\
        match cfgSh', cfgL' with
        | (TSh', _, LSh'), (TL', _, LL') => matching_threads TSh' TL' /\ LSh' = LL'
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
    clears HdescSh HdescL.
    exists. split; [ constructors* | simpls*].
  + (* StepEnd *)
    asserts* Hdom: (t \indom Tsh).
    clears HdescSh HdescL.
    eexists. split; [ constructors* | simpls*].
  + (* StepReadLocal *)
    exists. splits.
    * constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescL as (_ & _ & _ & Hstart & _ & _ & (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      apply Hwrite.
      forwards Hcf': conflict_free_last_inv Hcf.
      forwards* Hbinds'': HdomD t.
      exists t.
      applys* conflict_free_last_local_write Hcf' Hplay Hbinds''.
    * clears HdescSh HdescL.
      simpls*.
  + (* StepReadGlobal *)
    exists. split.
    * constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescL as (_ & _ & _ & Hrun & _ & _ & (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
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
    * clears HdescSh HdescL.
      simpls*.
  + (* StepReadVolatile: the SharedMemory side has no volatile distinction, so
       this maps to a plain [SharedMemory.StepRead];
       [is_latest_value_after_volatile_pull_inv] recovers the "last write in
       the log" characterization [Hwrite] needs, from [is_latest_value]
       evaluated at the global head [g] (not at [t]'s own, possibly stale,
       commit -- there is no per-thread commit distinction to make here). *)
    exists. split.
    * constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescL as (_ & _ & _ & Hrun & _ & _ & (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
      match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
      forwards (HwfG0 & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG0 Hhead0 Hheadr. subst g0.
      apply Hwrite.
      forwards Hcf': conflict_free_last_inv Hcf.
      applys* is_latest_value_after_volatile_pull_inv Hwf Hcf' Hplay.
    * clears HdescSh HdescL.
      simpls*.
  + (* StepWrite *)
    clears HdescSh HdescL.
    eexists. split; [ constructors* | simpls*].
  + (* StepWriteVolatile: purely mechanical -- a [SharedMemory.StepWrite]
       always matches (no [is_latest_value] obligation on the write side).
       [matching_threads] needs the same explicit chain as [linear_complete]'s
       [StepWrite] case: [T'] comes from a [global_commit] on a pre-updated
       [T], so [simpl]/[auto]'s hint search can't bridge the double update
       without an explicit [update_update] rewrite. *)
    clears HdescSh HdescL.
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    asserts Hdom0: (t \indom (Tsh[t := (state_running, te_exp e)])).
    { applys indom_update_same. typeclass. }
    asserts Hmt1: (matching_threads (Tsh[t := (state_running, te_exp e)])
                     (T[t := (state_running, te_exp e, d[x := v], c)])).
    { applys matching_threads_update_same Hsame. }
    asserts Hmt2: (matching_threads (Tsh[t := (state_running, te_exp e)]) T').
    { applys matching_threads_global_commit Hmt1 Hdom0 Hgc. }
    asserts Hmt3: (matching_threads (Tsh[t := (state_running, te_exp e)][t := (state_running, K void)])
                     (T'[t := (state_running, K void, empty, g')])).
    { applys matching_threads_update_same Hmt2. }
    rewrite update_update in Hmt3.
    eexists. split.
    * constructors*.
    * simpl. split; [ exact Hmt3 | reflexivity ].
    * typeclass.
  + (* StepSpawn *)
    exists. split.
    * constructors*.
      forwards~ Heq: matching_threads_same_domain Hsame.
      rewrite* Heq.
    * asserts* Hdom: (t \indom Tsh[t:=(state_running, K t')][t':=(
      state_new, te_exp e')]).
    {
      rew_dom. rew_set. autos.
    }
    asserts* Hdom': (t' \indom Tsh[t:=(state_running, K t')][t':=(
      state_new, te_exp e')]).
    {
      rew_dom. rew_set. autos.
    }
    asserts* Hneq: (t <> t').
    clears HdescSh HdescL.
    simpls*.
  + (* StepJoin *)
    asserts* Hex: (exists d c, binds T t' (state_terminated, te_ret r, d, c)).
    apply Hsame in Hex.
    clears HdescSh HdescL.
    exists. split; [ constructors* | simpls*].
  + (* StepLock *)
    clears HdescSh HdescL.
    exists. split; [ constructors* | simpls*].
  + (* StepRelease *)
    asserts* Hdom: (t \indom Tsh).
    clears HdescSh HdescL.
    exists. split; [ constructors* | simpls*].
Qed.

Theorem linear_equiv :
  forall log log' cfgSh cfgL,
    wf_log log ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingLinear.describes log cfgL ->
    match cfgSh, cfgL with
    | (TSh, _, LSh), (TL, _, LL) => matching_threads TSh TL /\ LSh = LL
    end ->
    conflict_free log' ->
      (exists cfgSh', LoggingSharedMemory.step (cfgSh, log) (cfgSh', log')) <->
      (exists cfgL', LoggingLinear.step (cfgL, log) (cfgL', log')).
Proof.
  introv Hwf HdescSh HdescL Hmatch Hcf.
  split.
  - introv (cfgSh' & Hstep).
    forwards* (cfgL' & Hstep' & _): linear_complete.
  - introv (cfgL' & Hstep).
    forwards* (cfgSh' & Hstep' & _): linear_sound.
Qed.
