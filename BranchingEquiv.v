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

Import Log.
Import LogFacts.

(* TODO: This doesn't touch the heap or graph which leads to a
bunch of shelved goals. Is threads_agree and locks_agree the right
abstraction? *)
Definition same_expressions_and_locks (cfgSh : SharedMemory.cfg) (cfgB : Branching.cfg) :=
  match cfgSh, cfgB with
  | (TSh, _, LSh), (TB, _, LB) =>
      (forall t st e,
        binds TSh t (st, e) <-> exists d h, binds TB t (st, e, d, h)) /\
      (forall l ls, binds LSh l ls <-> exists h, binds LB l (ls, h))
  end.

Lemma same_expressions_same_domains :
  forall Tsh H Lsh TB G LB,
    same_expressions_and_locks (Tsh, H, Lsh) (TB, G, LB) ->
    dom Tsh = dom TB /\ dom Lsh = dom LB.
Proof.
  introv Hexp.
  simpls. unfolds SharedMemory.threads, Branching.threads,
          SharedMemory.locks, Branching.locks.
  repeat rewrite dom_eq_set_of_binds.
  splits.
  - apply set_st_eq.
    intros t. splits.
    + introv ((st & e) & Hbinds).
      apply Hexp in Hbinds as (d & h & Hbinds').
      exists*.
    + introv ((((st & e) & d ) & h) & Hbinds).
      exists (st, e). apply* Hexp.
  - apply set_st_eq.
    intros l. splits.
    + introv (ls & Hbinds).
      apply Hexp in Hbinds as (ls' & Hbinds').
      exists*.
    + introv ((ls & h) & Hbinds).
      exists ls. apply* Hexp.
Qed.

(* Updating one thread's (state, expression) on both sides preserves
   [same_expressions_and_locks]: the Branching side may additionally change the
   staging area [d] and commit [h], but those are invisible to the relation. *)
Lemma same_expr_thread_update :
  forall TSh H H' LSh TB G G' LB t st e d h,
    same_expressions_and_locks (TSh, H, LSh) (TB, G, LB) ->
    same_expressions_and_locks (TSh[t := (st, e)], H', LSh) (TB[t := (st, e, d, h)], G', LB).
Proof.
  introv Hsame. destruct Hsame as (Hthr & Hlck). simpl. split; [| exact Hlck].
  introv. split.
  - introv Hb. destruct (classic (t0 = t)) as [-> | Hne].
    + forwards Heq: binds_update_same_inv Hb.
      inverts Heq. exists d h. apply binds_update_same.
    + forwards Hb': binds_update_neq_inv Hb Hne.
      apply Hthr in Hb' as (d0 & h0 & Hb0).
      exists d0 h0. applys binds_update_neq Hne Hb0.
  - introv (d0 & h0 & Hb). destruct (classic (t0 = t)) as [-> | Hne].
    + forwards Heq: binds_update_same_inv Hb.
      inverts Heq. apply binds_update_same.
    + forwards Hb': binds_update_neq_inv Hb Hne.
      asserts Hex: (exists d1 h1, binds TB t0 (st0, e0, d1, h1)). { exists* d0 h0. }
      apply Hthr in Hex. applys binds_update_neq Hne Hex.
Qed.

(* Likewise, updating one lock on both sides preserves the relation. *)
Lemma same_expr_lock_update :
  forall TSh H H' LSh TB G G' LB l ls h,
    same_expressions_and_locks (TSh, H, LSh) (TB, G, LB) ->
    same_expressions_and_locks (TSh, H', LSh[l := ls]) (TB, G', LB[l := (ls, h)]).
Proof.
  introv Hsame. destruct Hsame as (Hthr & Hlck). simpl. split; [exact Hthr |].
  introv. split.
  - introv Hb. destruct (classic (l0 = l)) as [-> | Hne].
    + forwards Heq: binds_update_same_inv Hb.
      inverts Heq. exists h. apply binds_update_same.
    + forwards Hb': binds_update_neq_inv Hb Hne.
      apply Hlck in Hb' as (h0 & Hb0).
      exists h0. applys binds_update_neq Hne Hb0.
  - introv (h0 & Hb). destruct (classic (l0 = l)) as [-> | Hne].
    + forwards Heq: binds_update_same_inv Hb.
      inverts Heq. apply binds_update_same.
    + forwards Hb': binds_update_neq_inv Hb Hne.
      asserts Hex: (exists h1, binds LB l0 (ls0, h1)). { exists* h0. }
      apply Hlck in Hex. applys binds_update_neq Hne Hex.
Qed.

(* Two Branching thread maps "agree" when they bind every thread to the same
   (state, expression), ignoring the staging area and commit pointer. The
   commit-graph operations ([do_commit], [do_merge], ...) only touch [d]/[h], so
   they preserve this projection -- which is all [same_expressions_and_locks]
   cares about on the Branching side. *)
Definition threads_agree (T1 T2 : Branching.threads) : Prop :=
  forall t st e,
    (exists d h, binds T1 t (st, e, d, h)) <-> (exists d h, binds T2 t (st, e, d, h)).

Definition locks_agree (L1 L2 : Branching.locks) : Prop :=
  forall l ls,
    (exists h, binds L1 l (ls, h)) <-> (exists h, binds L2 l (ls, h)).

Lemma threads_agree_trans :
  forall T1 T2 T3, threads_agree T1 T2 -> threads_agree T2 T3 -> threads_agree T1 T3.
Proof.
  introv H1 H2. intros t st e. split; intro Hb.
  - apply H1 in Hb. apply H2 in Hb. exact Hb.
  - apply H2 in Hb. apply H1 in Hb. exact Hb.
Qed.

(* Updating a thread to a value with the same (state, expression) preserves the
   projection. *)
Lemma threads_agree_update :
  forall (T : Branching.threads) t st e d h dn hn,
    binds T t (st, e, d, h) ->
    threads_agree T (T[t := (st, e, dn, hn)]).
Proof.
  introv Hb. intros t0 sx ex. split.
  - intros (d0 & h0 & Hb0). destruct (classic (t0 = t)) as [-> | Hne].
    + forwards* Heq: binds_inj Hb0 Hb. inverts Heq.
      exists dn hn. apply binds_update_same.
    + exists d0 h0. applys binds_update_neq Hne Hb0.
  - intros (d0 & h0 & Hb0). destruct (classic (t0 = t)) as [-> | Hne].
    + forwards Heq: binds_update_same_inv Hb0. inverts Heq.
      exists d h. exact Hb.
    + forwards Hb0': binds_update_neq_inv Hb0 Hne. exists d0 h0. exact Hb0'.
Qed.

Lemma locks_agree_update :
  forall (L : Branching.locks) l ls h hn,
    binds L l (ls, h) ->
    locks_agree L (L[l := (ls, hn)]).
Proof.
  introv Hb. intros l0 ls0. split.
  - intros (h0 & Hb0). destruct (classic (l0 = l)) as [-> | Hne].
    + forwards* Heq: binds_inj Hb0 Hb. inverts Heq.
      exists hn. apply binds_update_same.
    + exists h0. applys binds_update_neq Hne Hb0.
  - intros (h0 & Hb0). destruct (classic (l0 = l)) as [-> | Hne].
    + forwards Heq: binds_update_same_inv Hb0. inverts Heq.
      exists h. exact Hb.
    + forwards Hb0': binds_update_neq_inv Hb0 Hne. exists h0. exact Hb0'.
Qed.

Lemma same_expr_threads_agree :
  forall TSh H H' LSh TB TB' G G' LB,
    same_expressions_and_locks (TSh, H, LSh) (TB, G, LB) ->
    threads_agree TB TB' ->
    same_expressions_and_locks (TSh, H', LSh) (TB', G', LB).
Proof.
  introv Hsame Hag. destruct Hsame as (Hthr & Hlck). simpl. split; [| exact Hlck].
  introv. split.
  - intro Hb. apply Hthr in Hb. apply Hag in Hb. exact Hb.
  - intro Hb. apply Hag in Hb. apply Hthr in Hb. exact Hb.
Qed.

Lemma same_expr_locks_agree :
  forall TSh H H' LSh TB G G' LB LB',
    same_expressions_and_locks (TSh, H, LSh) (TB, G, LB) ->
    locks_agree LB LB' ->
    same_expressions_and_locks (TSh, H', LSh) (TB, G', LB').
Proof.
  introv Hsame Hag. destruct Hsame as (Hthr & Hlck). simpl. split; [exact Hthr |].
  introv. split.
  - intro Hb. apply Hlck in Hb. apply Hag in Hb. exact Hb.
  - intro Hb. apply Hag in Hb. apply Hlck in Hb. exact Hb.
Qed.

(* The commit-graph operations preserve the (state, expression) projection. *)
Lemma do_commit_threads_agree :
  forall t hn T G T' G' e d h,
    binds T t (state_running, e, d, h) ->
    do_commit t hn T G = (T', G') ->
    threads_agree T T'.
Proof.
  introv Hb Heq. unfold do_commit in Heq.
  destruct (T[t]) as [[[s e0] d0] h0] eqn:HTt. inverts Heq.
  lets Hin: (indom_of_binds Hb).
  forwards* Hbt0: binds_of_indom_read Hin HTt.
  forwards* Heq2: binds_inj Hb Hbt0. inverts Heq2.
  applys threads_agree_update Hb.
Qed.

Lemma do_merge_threads_agree :
  forall t hsrc hn T G T' G' st e d h,
    binds T t (st, e, d, h) ->
    do_merge t hsrc hn T G = (T', G') ->
    threads_agree T T'.
Proof.
  introv Hb Heq. unfold do_merge in Heq.
  destruct (T[t]) as [[[s e0] d0] h0] eqn:HTt. inverts Heq.
  lets Hin: (indom_of_binds Hb).
  forwards* Hbt0: binds_of_indom_read Hin HTt.
  forwards* Heq2: binds_inj Hb Hbt0. inverts Heq2.
  applys threads_agree_update Hb.
Qed.

Lemma pull_thread_threads_agree :
  forall t t' hn T G T' G' st e d h,
    binds T t (st, e, d, h) ->
    pull_thread t t' hn T G = (T', G') ->
    threads_agree T T'.
Proof.
  introv Hb Heq. unfold pull_thread in Heq.
  destruct (T[t']) as [[[ts' e'] d'] h']. applys do_merge_threads_agree Hb Heq.
Qed.

Lemma pull_lock_threads_agree :
  forall t l hn T G L T' G' st e d h,
    binds T t (st, e, d, h) ->
    pull_lock t l hn T G L = (T', G') ->
    threads_agree T T'.
Proof.
  introv Hb Heq. unfold pull_lock in Heq.
  destruct (L[l]) as [ls h']. applys do_merge_threads_agree Hb Heq.
Qed.

Lemma push_lock_threads_agree :
  forall t l hn T G L T' G' L' e d h,
    binds T t (state_running, e, d, h) ->
    push_lock t l hn T G L = (T', G', L') ->
    threads_agree T T'.
Proof.
  introv Hb Heq. unfold push_lock in Heq.
  destruct (do_commit t hn T G) as (T'' & G'') eqn:HC.
  destruct (L[l]) as [ls0 h0]. inverts Heq.
  applys do_commit_threads_agree Hb HC.
Qed.

Lemma push_lock_locks_agree :
  forall t l hn T G L T' G' L' ls h,
    binds L l (ls, h) ->
    push_lock t l hn T G L = (T', G', L') ->
    locks_agree L L'.
Proof.
  introv Hb Heq. unfold push_lock in Heq.
  destruct (do_commit t hn T G) as (T'' & G'').
  destruct (L[l]) as [ls0 h0] eqn:HL. inverts Heq.
  lets Hin: (indom_of_binds Hb).
  forwards* Hbl0: binds_of_indom_read Hin HL.
  forwards* Heq2: binds_inj Hb Hbl0. inverts Heq2.
  applys locks_agree_update Hb.
Qed.

Lemma push_thread_threads_agree :
  forall t t' hn T G T' G' e d h st' e' d' h',
    binds T t (state_running, e, d, h) ->
    binds T t' (st', e', d', h') ->
    push_thread t t' hn T G = (T', G') ->
    threads_agree T T'.
Proof.
  introv Hbt Hbt' Heq. unfold push_thread in Heq.
  destruct (do_commit t hn T G) as (T'' & G'') eqn:HC.
  forwards Hag1: do_commit_threads_agree Hbt HC.
  forwards (d2 & h2 & Hbt''): (proj1 (Hag1 t' st' e')). { exists d' h'. exact Hbt'. }
  destruct (T''[t']) as [[[ts2 e2] d3] h3] eqn:HT'. inverts Heq.
  lets Hin'': (indom_of_binds Hbt'').
  forwards* Hbt2: binds_of_indom_read Hin'' HT'.
  forwards* Heq2: binds_inj Hbt'' Hbt2. inverts Heq2.
  forwards Hag2: threads_agree_update Hbt''.
  applys threads_agree_trans Hag1 Hag2.
Qed.

(* Completeness: every SharedMemory step is matched by a Branching step, and the
   resulting configurations still have the same expressions and locks. *)
Theorem branching_complete :
  forall log log' cfgSh cfgB cfgSh',
    wf_log log ->
    match cfgB with
    | (_, G, _) => wf_graph G
    end ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingBranching.describes log cfgB ->
    same_expressions_and_locks cfgSh cfgB ->
    conflict_free log' ->
    LoggingSharedMemory.step (cfgSh, log) (cfgSh', log') ->
    exists cfgB',
      LoggingBranching.step (cfgB, log) (cfgB', log') /\
      same_expressions_and_locks cfgSh' cfgB'.
Proof.
  introv Hwf HwfG HdescSh HdescB Hsame Hcf Hstep.
  destruct cfgB as [(T & G) L].
  forwards* HdescSh': LoggingSharedMemoryFacts.step_preserves_describes Hwf.
  inverts Hstep;
    match goal with
    | H: binds ?T ?t (?ts', ?e) |- _ =>
        assert (Ht := H);
        apply (proj1 Hsame) in H as (d & h & Hbinds)
    end.
  + (* StepStart *)
    eexists. split; [ constructors* |].
    applys same_expr_thread_update Hsame.
  + (* StepEnd *)
    forwards (h' & Hfresh): exists_commit_fresh HwfG.
    asserts (T' & G' & Hcommit): (exists T' G', do_commit t h' T G = (T', G')).
    {
      exists. unfolds do_commit.
      forwards Hread: read_of_binds Hbinds.
      replace T[t] with (state_running, te_ret r, d, h).
      reflexivity.
    }
    eexists. split; [ constructors* |].
    forwards Hag: do_commit_threads_agree Hbinds Hcommit.
    applys same_expr_thread_update H G. applys same_expr_threads_agree Hsame Hag.
  + (* StepRead *)
    destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
    apply Hwrite in H6 as (t' & log'0 & Hfilter).
    destruct HdescB as (_ & _ & _ & Hrun & _ & _ &
      (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2) & _).
    lets Htin: (indom_of_binds Hbinds).
    forwards (ts0 & e0 & Hbd): Hdelta Htin.
    forwards* Heqdt: binds_inj Hbinds Hbd. inverts Heqdt.
    forwards Hcflog: conflict_free_last_inv Hcf.
    destruct (classic (i \indom (D[t]))) as [Hin | Hnin].
    * (* local (uncommitted) read: [i] is in [t]'s delta *)
      asserts Hdt: (t \indom D). { applys HdomD Htin. }
      asserts Hbdi: (binds (D[t]) i (D[t][i])).
      { applys binds_of_indom_read Hin; (reflexivity || typeclass). }
      forwards (log'' & Hfilt2): conflict_free_last_local_write Hcflog Hplay Hdt Hbdi.
      rewrite Hfilter in Hfilt2.
      forwards (_ & Heqw): last_eq_last_inv Hfilt2. inverts Heqw.
      eexists. split; [ applys StepReadLocal Hbinds; [ eassumption | exact Hbdi ] |].
      applys same_expr_thread_update Hsame.
    * (* global (committed) read: [i] is visible as the latest committed value *)
      forwards Hcfg: conflict_free_log_describes_conflict_free_graph Hwf Hcflog Hplay.
      lets [_ Hback]: Hrun t. forwards (Hms & Hmne): Hback. { do 3 eexists. exact Hbinds. }
      asserts Hwfr: (wf_log (log & event_read t i v)). { applys wf_log_read_last Hms Hmne Hwf. }
      destruct (last_write_position log i log'0 t' v Hfilter) as (mw & HNL & Hlast).
      forwards HLlt: Nth_inbound HNL.
      asserts Hplayf: (exists CHf,
        play_log (log & event_read t i v) (\{}, \{}, (\{}, \{}), \{}) (D, TC, G, LC) CHf).
      { eexists. applys PlaySnoc Hplay. apply PlayRead. }
      destruct Hplayf as (CHf & Hplayf).
      asserts HNLf: (LibList.Nth mw (log & event_read t i v) (event_write t' i v)).
      { applys* Nth_app_l. }
      asserts HNread: (LibList.Nth (length log) (log & event_read t i v) (event_read t i v)).
      { applys* Nth_app_r'. }
      asserts Hlastf:
        (forall k tk vk, LibList.Nth k (log & event_read t i v) (event_write tk i vk) -> k <= mw).
      { introv HNk. forwards [HN' | (Hpe & Hee)]: Nth_last_inv HNk.
        - applys Hlast HN'.
        - inverts Hee. }
      asserts Hacc: (accesses_location i (event_read t i v)). { reflexivity. }
      forwards Hhb: Hcf HNLf HNread Hacc HLlt.
      asserts HndomL: (i \notindom (D[t'])).
      { destruct (classic (t' = t)) as [-> | Hne].
        - exact Hnin.
        - applys last_writer_not_in_delta Hplayf HNLf Hlastf HNread Hhb. simpl. congruence. }
      forwards Hlv:
        (>> hb_last_write_visible Hwfr Hcf Hcfg Hplayf HNLf Hlastf HndomL HNread Hhb).
      simpl in Hlv.
      eexists. split; [ applys StepReadGlobal Hbinds; [ eassumption | exact Hnin | exact Hlv ] |].
      applys same_expr_thread_update Hsame.
  + (* StepWrite *)
    eexists. split; [ constructors* |].
    applys same_expr_thread_update Hsame.
  + (* StepSpawn *)
    forwards (h' & Hfresh): exists_commit_fresh HwfG.
    forwards* (Heq & _): same_expressions_same_domains.
    rewrite Heq in H6.
    asserts* Hneq: (t <> t').
    asserts (T' & G' & Hpush): (exists T' G', push_thread t t' h' T[t:=(state_running, te_exp (K t'), d, h)][t':=(state_new, te_exp e', \{}, 0)] G = (T', G')).
    {
      exists. unfolds push_thread, do_commit.
      rewrite~ read_update_neq.
      rewrite read_update_same.
      rewrite~ read_update_neq.
      rewrite read_update_same.
      reflexivity.
    }
    eexists. split; [ constructors* |].
    asserts HbiTt': (binds (T[t:=(state_running, te_exp (K t'), d, h)][t':=(state_new, te_exp e', \{}, 0)]) t' (state_new, te_exp e', \{}, 0)).
    { apply binds_update_same. }
    asserts HbiTt: (binds (T[t:=(state_running, te_exp (K t'), d, h)][t':=(state_new, te_exp e', \{}, 0)]) t (state_running, te_exp (K t'), d, h)).
    { applys binds_update_neq Hneq. apply binds_update_same. }
    forwards Hag: push_thread_threads_agree HbiTt HbiTt' Hpush.
    applys same_expr_threads_agree H G Hag.
    applys same_expr_thread_update H G.
    applys same_expr_thread_update Hsame.
  + (* StepJoin *)
    forwards (h'' & Hfresh): exists_commit_fresh HwfG.
    apply Hsame in H4 as (d' & h' & Hbinds').
    asserts (T' & G' & Hpull & Hbinds''): (exists T' G', pull_thread t t' h'' T G = (T', G') /\
                                                         binds T' t (state_running, te_exp e, d', h'')).
    {
      exists. unfolds pull_thread, do_merge.
      forwards Hread: read_of_binds Hbinds.
      replace T[t'] with (state_terminated, te_ret r, d, h).
      forwards Hread': read_of_binds Hbinds'.
      replace T[t] with (state_running, te_exp e, d', h').
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
    asserts Hmerge: (conflict_free_merge d' h' h G).
    {
      destruct HdescB as (_ & _ & _ & _ & _ & _ &
        (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2) & _).
      forwards Hcflog: conflict_free_last_inv Hcf.
      (* joiner [t]: [D[t] = d'], [TC[t] = h']. *)
      lets HtT: (indom_of_binds Hbinds').
      forwards (ts0 & e0 & Hbdt): Hdelta HtT.
      forwards* Heqt: binds_inj Hbinds' Hbdt. inverts Heqt.
      (* joined [t']: [TC[t'] = h]. *)
      lets Ht'T: (indom_of_binds Hbinds).
      forwards (ts1 & e1 & Hbdt'): Hdelta Ht'T.
      forwards* Heqt': binds_inj Hbinds Hbdt'. inverts Heqt'.
      forwards Hpgwf: play_log_graph_wf Hplay. destruct Hpgwf as (_ & HTCdom & _).
      applys conflict_free_merge_holds Hwf Hcflog Hplay;
        [ applys HdomD HtT | applys HdomTC HtT | applys HTCdom; applys HdomTC Ht'T ].
    }
    eexists. split; [ constructors* |].
    forwards Hag: pull_thread_threads_agree Hbinds' Hpull.
    applys same_expr_thread_update H G.
    applys same_expr_threads_agree Hsame Hag.
  + (* StepLock *)
    branches.
    * forwards (h'' & Hfresh): exists_commit_fresh HwfG.
      apply Hsame in H0 as (h' & Hlock).
      asserts Hmerge: (conflict_free_merge d h h' G).
      {
        destruct HdescB as (_ & _ & _ & _ & _ & _ &
          (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2) & _).
        forwards Hcflog: conflict_free_last_inv Hcf.
        (* locker [t]: [D[t] = d], [TC[t] = h]. *)
        lets HtT: (indom_of_binds Hbinds).
        forwards (ts0 & e0 & Hbdt): Hdelta HtT.
        forwards* Heqt: binds_inj Hbinds Hbdt. inverts Heqt.
        (* lock [l0]: [LC[l0] = h']. *)
        lets Hl0L: (indom_of_binds Hlock).
        forwards (ls0 & Hbdl): Hlocks Hl0L.
        forwards* Heql: binds_inj Hlock Hbdl. inverts Heql.
        forwards Hpgwf: play_log_graph_wf Hplay. destruct Hpgwf as (_ & _ & HLCdom).
        applys conflict_free_merge_holds Hwf Hcflog Hplay;
          [ applys HdomD HtT | applys HdomTC HtT | applys HLCdom; applys HdomLC Hl0L ].
      }
      asserts (T' & G' & Hpull & Hbinds''): (exists T' G', pull_lock t l0 h'' T G L = (T', G') /\
                                                             binds T' t (state_running, te_exp e, d, h'')).
      {
        exists. unfolds pull_lock, do_merge.
        forwards Hread: read_of_binds Hlock.
        replace L[l0] with (ls_free, h').
        forwards Hread': read_of_binds Hbinds.
        replace T[t] with (state_running, te_exp e, d, h).
        splits.
        - reflexivity.
        - apply binds_update_same.
      }
      eexists. split; [ constructors* |].
      forwards Hag: pull_lock_threads_agree Hbinds Hpull.
      applys same_expr_lock_update H G.
      applys same_expr_thread_update H G.
      applys same_expr_threads_agree Hsame Hag.
    * forwards* (_ & Heq): same_expressions_same_domains.
      rewrite Heq in *.
      eexists. split; [ applys* StepLockFresh |].
      applys same_expr_lock_update H G.
      applys same_expr_thread_update Hsame.
  + (* StepRelease *)
    forwards (h'' & Hfresh): exists_commit_fresh HwfG.
    asserts (h' & HbindsL): (exists h', binds L l0 (ls_held t, h')).
    {
      destruct HdescSh as (_ & _ & _ & _ & Hlock & _).
      match goal with
      | H : binds L0 l0 (ls_held t) |- _ => apply Hlock in H as Hex
      end.
      destruct HdescB as (_ & _ & _ & _ & Hlock' & _).
      apply* Hlock'.
    }
    asserts (T' & G' & L' & Hpush & Hbinds'): (exists T' G' L', push_lock t l0 h'' T G L = (T', G', L') /\ binds T' t (state_running, te_exp e, \{}, h'')).
    {
      exists. unfolds push_lock, do_commit.
      forwards Hread: read_of_binds Hbinds.
      replace T[t] with (state_running, te_exp e, d, h).
      forwards Hread': read_of_binds HbindsL.
      replace L[l0] with (ls_held t, h').
      splits.
      - reflexivity.
      - apply binds_update_same.
    }
    eexists. split; [ constructors* |].
    forwards HagT: push_lock_threads_agree Hbinds Hpush.
    forwards HagL: push_lock_locks_agree HbindsL Hpush.
    forwards* Hs1: same_expr_threads_agree Hsame HagT.
    forwards Hs2: same_expr_locks_agree Hs1 HagL.
    applys same_expr_lock_update.
    applys same_expr_thread_update.
    applys Hs2.
    Unshelve. all: assumption.
Qed.

(* Soundness: every Branching step is matched by a SharedMemory step, with the
   resulting configurations again sharing expressions and locks. *)
Theorem branching_sound :
  forall log log' cfgSh cfgB cfgB',
    wf_log log ->
    match cfgB with
    | (_, G, _) => wf_graph G
    end ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingBranching.describes log cfgB ->
    same_expressions_and_locks cfgSh cfgB ->
    conflict_free log' ->
    LoggingBranching.step (cfgB, log) (cfgB', log') ->
    exists cfgSh',
      LoggingSharedMemory.step (cfgSh, log) (cfgSh', log') /\
      same_expressions_and_locks cfgSh' cfgB'.
Proof.
  introv Hwf HwfG HdescSh HdescB Hsame Hcf Hstep.
  destruct cfgSh as ((Tsh & Hp) & Lsh).
  inverts Hstep;
    try
    match goal with
    | H: binds ?T ?t (?ts, ?e, ?d, ?h) |- _ =>
        asserts Hex: (exists d h, binds T t (ts, e, d, h));
        [exists d; exists h; exact H|];
        apply Hsame in Hex as Hbinds; clear Hex
    end.
  + (* StepStart *)
    eexists. split; [ constructors* |].
    applys same_expr_thread_update Hsame.
  + (* StepEnd *)
    eexists. split; [ constructors* |].
    match goal with
    | Hb : binds T t (state_running, te_ret r, ?dd, ?hh), Hc : do_commit t ?hn T G = (?TT, ?GG) |- _ =>
        forwards Hag: do_commit_threads_agree Hb Hc
    end.
    applys same_expr_thread_update Hp G. applys same_expr_threads_agree Hsame Hag.
  + (* StepReadLocal *)
    eexists. split.
    { constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescB as (_ & _ & _ & Hstart & _ & _ & (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2) & _).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      apply Hwrite.
      forwards Hcf': conflict_free_last_inv Hcf.
      forwards* Hbinds'': HdomD t.
      forwards* Hex: conflict_free_last_local_write Hplay. }
    applys same_expr_thread_update Hsame.
  + (* StepReadGlobal *)
    eexists. split.
    { constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescB as (_ & _ & _ & Hrun & _ & _ & (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2) & _).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      forwards* Heq: binds_inj Hbinds'.
      inverts Heq.
      asserts* ->: (h = TC[t]).
      apply Hwrite.
      asserts Hcfg: (conflict_free_graph G).
      { forwards Hcflog: conflict_free_last_inv Hcf.
        applys conflict_free_log_describes_conflict_free_graph Hwf Hcflog Hplay. }
      asserts Hwfr: (wf_log (log & event_read t i v)).
      { lets [_ Hback]: Hrun t.
        forwards (Hms & Hmne): Hback.
        { do 3 eexists. eassumption. }
        applys wf_log_read_last Hms Hmne Hwf. }
      asserts* Hdom: (t \indom T).
      forwards~ Hdom': HdomTC Hdom.
      forwards* Hex: conflict_free_last_global_write Hcf Hwfr Hcfg Hplay. }
    applys same_expr_thread_update Hsame.
  + (* StepWrite *)
    eexists. split; [ constructors* |].
    applys same_expr_thread_update Hp Hsame.
  + (* StepSpawn *)
    eexists. split.
    { constructors*. forwards* (-> & _): same_expressions_same_domains. }
    asserts* Hneq: (t <> t').
    match goal with
    | Hp : push_thread t t' ?hn ?iT G = (?TT, ?GG) |- _ =>
        asserts HbiTt: (binds iT t (state_running, te_exp (K t'), d, h));
        [ applys binds_update_neq; [ | apply binds_update_same ]; auto |];
        asserts HbiTt': (binds iT t' (state_new, te_exp e', \{}, 0));
        [ apply binds_update_same |];
        forwards Hag: push_thread_threads_agree HbiTt HbiTt' Hp
    end.
    applys same_expr_threads_agree Hp G Hag.
    applys same_expr_thread_update Hp G.
    applys same_expr_thread_update Hsame.
  + (* StepJoin *)
    asserts* Hex: (exists d h, binds T t' (state_terminated, te_ret r, d, h)).
    apply Hsame in Hex.
    eexists. split; [ constructors* |].
    forwards* Hag: pull_thread_threads_agree H8.
    applys same_expr_thread_update Hp G.
    applys same_expr_threads_agree Hsame Hag.
  + (* StepLock *)
    eexists. split.
    { constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & HunlockedSh & _).
      destruct HdescB as (_ & _ & _ & _ & _ & HunlockedB & _).
      forwards Hiff: HunlockedSh l0.
      forwards Hiff': HunlockedB l0.
      left. apply Hiff. apply* Hiff'. }
    match goal with
    | Hp : pull_lock t l0 ?hn T G L = (?TT, ?GG) |- _ =>
        forwards* Hag: pull_lock_threads_agree Hp
    end.
    applys same_expr_lock_update Hp G.
    applys same_expr_thread_update Hp G.
    applys same_expr_threads_agree Hsame Hag.
  + (* StepLockFresh *)
    eexists. split.
    { constructors*. forwards* (_ & ->): same_expressions_same_domains. }
    applys same_expr_lock_update Hp G.
    applys same_expr_thread_update Hsame.
  + (* StepRelease *)
    eexists. split.
    { constructors*.
      destruct HdescSh as (_ & _ & _ & _ & HlockedSh & _ & _).
      destruct HdescB as (_ & _ & _ & _ & HunlockedB & _ & _).
      forwards* (t' & log' & Hiff): HlockedSh t l0.
      forwards* (t'' & log'' & Hiff'): HunlockedB t l0. }
    match goal with
    | Hb : binds L l0 (ls_held t, ?hl), Hp : push_lock t l0 ?hn T G L = (?TT, ?GG, ?LL) |- _ =>
        forwards* HagT: push_lock_threads_agree Hp;
        forwards HagL: push_lock_locks_agree Hb Hp
    end.
    applys same_expr_lock_update Hp G.
    applys same_expr_thread_update Hp G.
    applys same_expr_locks_agree Hp G HagL.
    applys same_expr_threads_agree Hsame HagT.
Qed.

(* The original equivalence is the conjunction of the two directions. *)
Corollary branching_equiv :
  forall log log' cfgSh cfgB,
    wf_log log ->
    match cfgB with
    | (_, G, _) => wf_graph G
    end ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingBranching.describes log cfgB ->
    same_expressions_and_locks cfgSh cfgB ->
    conflict_free log' ->
      (exists cfgSh', LoggingSharedMemory.step (cfgSh, log) (cfgSh', log')) <->
      (exists cfgB', LoggingBranching.step (cfgB, log) (cfgB', log')).
Proof.
  introv Hwf HwfG HdescSh HdescB Hsame Hcf. split.
  - introv (cfgSh' & Hstep).
    forwards* (cfgB' & Hb & _): branching_complete.
  - introv (cfgB' & Hstep).
    forwards* (cfgSh' & Hb & _): branching_sound.
Qed.
