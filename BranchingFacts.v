From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Branching.

Import Graph.
Import GraphFacts.
Import Branching.

(* ===================================================================== *)
(* Well-formedness                                                       *)
(* ===================================================================== *)

(* [wf_cfg] bundles everything [progress] needs to stay inductively true
   across a [step]: the thread map is finite (needed to generate a fresh tid
   for [StepSpawn]), the graph is well-formed (acyclic and finite -- needed
   for [exists_commit_fresh]), [root_commit] is always in the graph (a
   never-touched lock's [lock_read] defaults to it), every thread's and
   lock's commit pointer is already in the graph (needed to justify
   [graph_commit_wf] / [graph_merge_wf] when that thread/lock is next
   touched), and a terminated thread always carries a return value with an
   empty staging area (it became terminated only via [StepEnd]). *)
Definition wf_cfg (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      LibMap.finite T /\
      wf_graph G /\
      graph_indom G root_commit /\
      (forall t e d c, binds T t (state_terminated, e, d, c) ->
         exists r, e = te_ret r /\ d = empty) /\
      (forall t ts e d c, binds T t (ts, e, d, c) -> graph_indom G c) /\
      (forall l ls c, binds L l (ls, c) -> graph_indom G c)
  end.

(* ===================================================================== *)
(* Progress (modulo deadlock, forbidden effects, and conflicts)          *)
(* ===================================================================== *)

(* An effect is *enabled* for thread [t] (staging diff [d], commit pointer
   [h]) when its non-blocking precondition holds: a read must be visible
   either locally (in [d]) or globally (as the latest committed value at
   [h]); an unlock must target a lock [t] itself holds. Writes, spawns,
   joins and locks have no such precondition -- whether a join/lock can
   actually fire is the *blocking* question below, and whether it can fire
   *without* a conflict is the separate [conflict_detected] question. *)
Definition enabled (G : graph) (L : locks) (t : tid) (d : diff) (h : commit) (a : eff) : Prop :=
  match a with
  | eff_read x   => x \indom d \/ exists v, is_latest_value G h x v
  | eff_unlock l => exists h', lock_read L l = (ls_held t, h')
  | _ => True
  end.

(* A *blocking* effect: joining a thread that has not terminated, or
   acquiring a lock that is currently held. These are the legitimate sources
   of deadlock (locks default to free, so there is no "never acquired"
   case). *)
Definition blocked (T : threads) (L : locks) (a : eff) : Prop :=
  match a with
  | eff_join t'  => ~ exists r d c, binds T t' (state_terminated, te_ret r, d, c)
  | eff_lock l   => fst (lock_read L l) <> ls_free
  | _ => False
  end.

(* Progress for the underlying sequential language: every running,
   still-computing thread can take a [step_ul] step. Nothing is assumed
   about whether the resulting effect is [enabled] -- a thread offering a
   [step_ul] to a disabled effect is exactly the [forbidden] situation that
   [progress] reports separately. *)
Definition ul_progress (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      forall t e d h,
        binds T t (state_running, te_exp e, d, h) ->
        exists K a, step_ul e K a
  end.

(* A thread is *forbidden* from stepping when the underlying language offers
   a reduction to an effect that is not enabled: a read that is visible
   neither locally nor globally, or an unlock of a lock the thread does not
   itself hold. *)
Definition forbidden (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      exists t e d h K a,
        binds T t (state_running, te_exp e, d, h) /\
        step_ul e K a /\
        ~ enabled G L t d h a
  end.

(* A thread is poised to synchronise (join a terminated thread, or acquire a
   free lock) but the merge that synchronisation would perform is not
   conflict-free. This is another (non-[forbidden]) way a thread can get
   stuck: not a deadlock (the target is available), not a language-level
   violation (the effect is enabled), but a genuine data race between the
   two histories being merged. *)
Definition conflict_detected (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      exists t e d h K,
        binds T t (state_running, te_exp e, d, h) /\
        ((exists t' r d' c',
             step_ul e K (eff_join t') /\
             binds T t' (state_terminated, te_ret r, d', c') /\
             ~ conflict_free_merge d h c' G)
         \/
         (exists l h',
             step_ul e K (eff_lock l) /\
             lock_read L l = (ls_free, h') /\
             ~ conflict_free_merge d h h' G))
  end.

(* A thread has terminated. *)
Definition terminated (cfg : cfg) (t : tid) : Prop :=
  match cfg with
  | (T, _, _) => exists r c, binds T t (state_terminated, te_ret r, empty, c)
  end.

(* A running thread is *inert* when it is still computing, can take a step,
   but every step it can take is blocked (a join on a non-terminated thread,
   or a lock on a held lock). *)
Definition inert (cfg : cfg) (t : tid) : Prop :=
  match cfg with
  | (T, _, L) =>
      exists e d h,
        binds T t (state_running, te_exp e, d, h) /\
        (exists K a, step_ul e K a) /\
        (forall K a, step_ul e K a -> blocked T L a)
  end.

(* The configuration is *done* when every thread has terminated. *)
Definition done (cfg : cfg) : Prop :=
  match cfg with
  | (T, _, _) => forall t, t \indom T -> terminated cfg t
  end.

(* The configuration is *deadlocked* when every thread is terminated or
   inert, and at least one thread is inert (so [deadlocked] is disjoint from
   [done]). *)
Definition deadlocked (cfg : cfg) : Prop :=
  match cfg with
  | (T, _, _) =>
      (forall t, t \indom T -> terminated cfg t \/ inert cfg t) /\
      (exists t, t \indom T /\ inert cfg t)
  end.

(* A binding in an updated map is either the updated entry or an untouched one. *)
Lemma binds_update_inv' :
  forall A B (M : map A B) i j v w,
    binds (M[i := v]) j w ->
    (j = i /\ w = v) \/ (j <> i /\ binds M j w).
Proof.
  introv Hb. destruct (classic (j = i)) as [-> | Hne].
  - left. split; [ reflexivity | applys binds_update_same_inv Hb ].
  - right. split; [ exact Hne | applys binds_update_neq_inv Hb Hne ].
Qed.

(* A fresh thread id always exists, since the domain is a finite set of
   [nat]s. (Used to discharge the freshness side-condition of [StepSpawn] in
   progress.) *)
Lemma exists_fresh_tid :
  forall (T : threads),
    LibMap.finite T ->
    exists t', t' \notindom T.
Proof.
  introv Hfin.
  lets (l & Hcov): finite_inv_list_covers Hfin.
  exists (1 + fold_right plus 0 l).
  simpl.
  introv Hindom.
  forwards Hmem: Hcov Hindom.
  forwards Hle: mem_le_sum Hmem.
  nat_math.
Qed.

(* ===================================================================== *)
(* [dom T] is preserved (or grows by exactly the fresh tid) by the         *)
(* thread/graph combinators, independently of any [indom] side-condition -- *)
(* [dom_update] is unconditional, so these hold even though the [let]      *)
(* destructuring inside each combinator is opaque about what it reads.     *)
(* ===================================================================== *)

Lemma finite_do_commit :
  forall t h_new T G T' G',
    do_commit t h_new T G = (T', G') ->
    LibSet.finite (dom T) -> LibSet.finite (dom T').
Proof.
  introv Heq Hfin. unfolds do_commit. destruct (T[t]) as [[[s e] d] h].
  inverts Heq. rew_dom. apply~ LibSet.finite_union. apply LibSet.finite_single.
Qed.

Lemma finite_push_thread :
  forall t t' h_new T G T' G',
    push_thread t t' h_new T G = (T', G') ->
    LibSet.finite (dom T) -> LibSet.finite (dom T').
Proof.
  introv Heq Hfin. unfolds push_thread.
  destruct (do_commit t h_new T G) as [T'' G''] eqn:Hdc.
  destruct (T''[t']) as [[[ts e] d] c].
  inverts Heq.
  forwards Hfin'': finite_do_commit Hdc Hfin.
  rew_dom. apply~ LibSet.finite_union. apply LibSet.finite_single.
Qed.

Lemma finite_do_merge :
  forall t h h_new T G T' G',
    do_merge t h h_new T G = (T', G') ->
    LibSet.finite (dom T) -> LibSet.finite (dom T').
Proof.
  introv Heq Hfin. unfolds do_merge. destruct (T[t]) as [[[ts e] d] h_t].
  inverts Heq. rew_dom. apply~ LibSet.finite_union. apply LibSet.finite_single.
Qed.

Lemma finite_pull_thread :
  forall t t' h_new T G T' G',
    pull_thread t t' h_new T G = (T', G') ->
    LibSet.finite (dom T) -> LibSet.finite (dom T').
Proof.
  introv Heq Hfin. unfolds pull_thread. destruct (T[t']) as [[[s e] d] h'].
  applys finite_do_merge Heq Hfin.
Qed.

Lemma finite_pull_lock :
  forall t l h_new T G L T' G',
    pull_lock t l h_new T G L = (T', G') ->
    LibSet.finite (dom T) -> LibSet.finite (dom T').
Proof.
  introv Heq Hfin. unfolds pull_lock. destruct (lock_read L l) as [ls h].
  applys finite_do_merge Heq Hfin.
Qed.

Lemma finite_push_lock :
  forall t l h_new T G L T' G' L',
    push_lock t l h_new T G L = (T', G', L') ->
    LibSet.finite (dom T) -> LibSet.finite (dom T').
Proof.
  introv Heq Hfin. unfolds push_lock.
  destruct (do_commit t h_new T G) as [T'' G''] eqn:Hdc.
  destruct (L[l]) as [ls ?].
  inverts Heq.
  applys finite_do_commit Hdc Hfin.
Qed.

(* A finite thread domain stays finite under a step: every rule either
   updates existing threads in place (domain unchanged) or spawns exactly
   one new thread ([StepSpawn], adding a single element). *)
Lemma step_preserves_finite :
  forall T G L cfg',
    LibSet.finite (dom T) ->
    step (T, G, L) cfg' ->
    match cfg' with (T', _, _) => LibSet.finite (dom T') end.
Proof.
  introv Hfin Hstep.
  hint LibSet.finite_single.
  hint LibSet.finite_union.
  inverts Hstep; simpl.
  - (* StepStart *) rew_dom. autos.
  - (* StepEnd *)
    match goal with H : do_commit _ _ _ _ = (_, _) |- _ =>
      forwards Hfin': finite_do_commit H Hfin end.
    rew_dom. autos.
  - (* StepReadLocal *) rew_dom. autos.
  - (* StepReadGlobal *) rew_dom. autos.
  - (* StepWrite *) rew_dom. autos.
  - (* StepSpawn *)
    asserts Hfin0:
      (LibSet.finite (dom (T[t := (state_running, K t', d, h)][t' := (state_new, te_exp e', empty, 0)]))).
    { rew_dom. autos. }
    applys* finite_push_thread.
  - (* StepJoin *)
    match goal with H : pull_thread _ _ _ _ _ = (_, _) |- _ =>
      forwards Hfin': finite_pull_thread H Hfin end.
    rew_dom. autos.
  - (* StepLock *)
    match goal with H : pull_lock _ _ _ _ _ _ = (_, _) |- _ =>
      forwards Hfin': finite_pull_lock H Hfin end.
    rew_dom. autos.
  - (* StepRelease *)
    match goal with H : push_lock _ _ _ _ _ _ = (_, _, _) |- _ =>
      forwards Hfin': finite_push_lock H Hfin end.
    rew_dom. autos.
Qed.

(* [wf_cfg] is preserved by [step]: finiteness ([step_preserves_finite]),
   well-formedness and [root_commit]-membership of the graph (every graph
   change is a [graph_commit]/[graph_merge] onto a fresh commit, from a
   parent already in the graph -- [graph_commit_wf]/[graph_merge_wf] and
   [graph_commit_indom]/[graph_merge_indom]), the terminated-thread shape
   (only [StepEnd] produces one, with [te_ret] and an empty staging area),
   and every thread's/lock's commit pointer staying in the graph (untouched
   ones by the invariant, touched ones by the same [graph_commit]/
   [graph_merge] indom facts). *)
Theorem step_preserves_wf_cfg :
  forall cfg cfg',
    wf_cfg cfg ->
    step cfg cfg' ->
    wf_cfg cfg'.
Proof.
  introv Hwfc Hstep. destruct cfg as ((T & G) & L).
  destruct Hwfc as (Hfin & Hwf & HrootIndom & Hterm & HdomT & HdomL).
  hint LibSet.finite_single.
  hint LibSet.finite_union.
  inverts Hstep.
  - (* StepStart *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact HrootIndom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq. applys* HdomT.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* HdomT.
    + exact HdomL.
  - (* StepEnd *)
    match goal with H : do_commit _ _ _ _ = (_, _) |- _ => rename H into Hdc end.
    unfolds do_commit.
    match goal with H : binds T t (state_running, te_ret r, ?d0, ?h0) |- _ =>
      replace (T[t]) with (state_running, te_ret r, d0, h0) in Hdc by (symmetry; applys* read_of_binds) end.
    inverts Hdc.
    splits.
    + unfolds finite. rew_dom. autos.
    + apply* graph_commit_wf.
    + apply* graph_commit_indom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq. eexists. splits*.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply* graph_commit_indom_same.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne.
        apply* graph_commit_indom.
    + introv Hbinds. apply* graph_commit_indom.
  - (* StepReadLocal *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact HrootIndom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq. applys* HdomT.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* HdomT.
    + exact HdomL.
  - (* StepReadGlobal *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact HrootIndom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq. applys* HdomT.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* HdomT.
    + exact HdomL.
  - (* StepWrite *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact HrootIndom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq. applys* HdomT.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* HdomT.
    + exact HdomL.
  - (* StepSpawn *)
    match goal with H : push_thread _ _ _ _ _ = (_, _) |- _ => rename H into Hpt end.
    asserts Hneq: (t <> t').
    { introv Heq. subst. match goal with H : t' \notindom T |- _ => applys* H end. }
    unfolds push_thread, do_commit.
    rewrite~ read_update_neq in Hpt. rewrite read_update_same in Hpt.
    rewrite~ read_update_neq in Hpt. rewrite read_update_same in Hpt.
    inverts Hpt.
    splits.
    + asserts Hfin0:
        (LibSet.finite (dom (T[t := (state_running, K t', d, h)][t' := (state_new, te_exp e', empty, 0)]))).
      { unfolds finite. rew_dom. autos. }
      unfolds finite. rew_dom. autos.
    + apply* graph_commit_wf.
    + apply* graph_commit_indom.
    + introv Hbinds. destruct (classic (t0 = t')) as [->|Hne'].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne'.
        destruct (classic (t0 = t)) as [->|Hne].
        -- forwards Heq: binds_update_same_inv Hbinds'. inverts Heq.
        -- forwards Hbinds'': binds_update_neq_inv Hbinds' Hne.
           forwards Hbinds3: binds_update_neq_inv Hbinds'' Hne'.
           forwards Hbinds4: binds_update_neq_inv Hbinds3 Hne.
           applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t')) as [->|Hne'].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply* graph_commit_indom_same.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne'.
        destruct (classic (t0 = t)) as [->|Hne].
        -- forwards Heq: binds_update_same_inv Hbinds'. inverts Heq.
           apply* graph_commit_indom_same.
        -- forwards Hbinds'': binds_update_neq_inv Hbinds' Hne.
           forwards Hbinds3: binds_update_neq_inv Hbinds'' Hne'.
           forwards Hbinds4: binds_update_neq_inv Hbinds3 Hne.
           apply* graph_commit_indom.
    + introv Hbinds. apply* graph_commit_indom.
  - (* StepJoin *)
    match goal with H : pull_thread _ _ _ _ _ = (_, _) |- _ => rename H into Hpt end.
    unfolds pull_thread, do_merge.
    replace (T[t']) with (state_terminated, te_ret r, empty_diff, h') in Hpt
      by (symmetry; applys* read_of_binds).
    replace (T[t]) with (state_running, te_exp e, d, h) in Hpt
      by (symmetry; applys* read_of_binds).
    inverts Hpt.
    splits.
    + unfolds finite. rew_dom. autos.
    + apply* graph_merge_wf.
    + apply* graph_merge_indom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply* graph_merge_indom_same.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne.
        apply* graph_merge_indom.
    + introv Hbinds. apply* graph_merge_indom.
  - (* StepLock: [lock_read] unifies the "already touched" and "never
       touched" (defaulting to [(ls_free, root_commit)]) cases into one
       constructor. *)
    match goal with H : pull_lock _ _ _ _ _ _ = (_, _) |- _ => rename H into Hpl end.
    match goal with H : lock_read L l0 = (ls_free, ?c0) |- _ => rename H into Hread end.
    asserts Hc'indom: (graph_indom G (snd (lock_read L l0))).
    { destruct (classic (l0 \indom L)) as [Hindom|Hnotin].
      - destruct (L[l0]) as [ls0 c0] eqn:HL0.
        asserts Heq: (lock_read L l0 = (ls0, c0)).
        { transitivity (L[l0]); [exact (read_default_indom Hindom) | exact HL0]. }
        rewrite Heq. simpl.
        asserts Hb: (binds L l0 (ls0, c0)). { applys binds_of_indom_read Hindom. exact HL0. }
        applys* HdomL.
      - asserts Heq: (lock_read L l0 = (ls_free, root_commit)).
        { exact (read_default_notindom Hnotin). }
        rewrite Heq. exact HrootIndom. }
    rewrite Hread in Hc'indom. simpl in Hc'indom.
    unfolds pull_lock, do_merge.
    rewrite Hread in Hpl.
    match goal with H : binds T t (state_running, te_exp e, ?d0, ?h0) |- _ =>
      replace (T[t]) with (state_running, te_exp e, d0, h0) in Hpl by (symmetry; applys* read_of_binds) end.
    inverts Hpl.
    splits.
    + unfolds finite. rew_dom. autos.
    + apply* graph_merge_wf.
    + apply* graph_merge_indom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply* graph_merge_indom_same.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne.
        apply* graph_merge_indom.
    + introv Hbinds. destruct (classic (l = l0)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply* graph_merge_indom.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        apply* graph_merge_indom.
  - (* StepRelease: the thread already holds the lock, so its commit is
       already known to be in the graph via [HdomL]. *)
    match goal with H : push_lock _ _ _ _ _ _ = (_, _, _) |- _ => rename H into Hpl end.
    unfolds push_lock, do_commit.
    match goal with H : binds T t (state_running, te_exp e, ?d0, ?h0) |- _ =>
      replace (T[t]) with (state_running, te_exp e, d0, h0) in Hpl by (symmetry; applys* read_of_binds) end.
    match goal with H : binds L l0 (ls_held t, ?c0) |- _ =>
      replace (L[l0]) with (ls_held t, c0) in Hpl by (symmetry; applys* read_of_binds) end.
    inverts Hpl.
    splits.
    + unfolds finite. rew_dom. autos.
    + apply* graph_commit_wf.
    + apply* graph_commit_indom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply* graph_commit_indom_same.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne.
        apply* graph_commit_indom.
    + introv Hbinds. destruct (classic (l = l0)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply* graph_commit_indom_same.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne.
        apply* graph_commit_indom.
Qed.

(* ===================================================================== *)
(* Progress (modulo deadlock, forbidden effects, and conflicts)          *)
(* ===================================================================== *)

(* [thread]/[lock_state * commit]-specialised re-statements of the generic
   [LibMap] read/binds lemmas, with [Branching.inhab_thread]/[inhab_lock]
   supplied *explicitly*. Typeclass search for a bare [Inhab thread] (a
   [Definition], not folded back from its tuple expansion) does not reliably
   find [Branching.inhab_thread] when the goal is stated in unfolded tuple
   form (as [binds_inj]'s generic statement forces) -- pin it down here once
   so the rest of the proof doesn't hit that ambiguity. *)
Lemma thread_read_of_binds :
  forall {t : tid} {T : threads} {v : thread}, binds T t v -> T[t] = v.
Proof. introv Hb. exact (@read_of_binds tid thread Branching.inhab_thread T t v Hb). Qed.

Lemma thread_indom_of_binds :
  forall {t : tid} {T : threads} {v : thread}, binds T t v -> t \indom T.
Proof. introv Hb. exact (@indom_of_binds tid thread Branching.inhab_thread T t v Hb). Qed.

Lemma thread_binds_of_indom_read :
  forall {t : tid} {T : threads} {v : thread}, t \indom T -> T[t] = v -> binds T t v.
Proof. introv Hin Heq. exact (@binds_of_indom_read tid thread Branching.inhab_thread T t v Hin Heq). Qed.

Lemma thread_binds_inj :
  forall {t : tid} {T : threads} {v1 v2 : thread}, binds T t v1 -> binds T t v2 -> v1 = v2.
Proof. introv Hb1 Hb2. exact (@binds_inj tid t thread Branching.inhab_thread v1 v2 T Hb1 Hb2). Qed.

Lemma lock_read_of_binds :
  forall {ll : lid} {L : locks} {v : lock_state * commit}, binds L ll v -> L[ll] = v.
Proof. introv Hb. exact (@read_of_binds lid (lock_state * commit) Branching.inhab_lock L ll v Hb). Qed.

Lemma lock_indom_of_binds :
  forall {ll : lid} {L : locks} {v : lock_state * commit}, binds L ll v -> ll \indom L.
Proof. introv Hb. exact (@indom_of_binds lid (lock_state * commit) Branching.inhab_lock L ll v Hb). Qed.

Lemma lock_binds_of_indom_read :
  forall {ll : lid} {L : locks} {v : lock_state * commit}, ll \indom L -> L[ll] = v -> binds L ll v.
Proof. introv Hin Heq. exact (@binds_of_indom_read lid (lock_state * commit) Branching.inhab_lock L ll v Hin Heq). Qed.

Lemma lock_binds_inj :
  forall {ll : lid} {L : locks} {v1 v2 : lock_state * commit}, binds L ll v1 -> binds L ll v2 -> v1 = v2.
Proof. introv Hb1 Hb2. exact (@binds_inj lid ll (lock_state * commit) Branching.inhab_lock v1 v2 L Hb1 Hb2). Qed.

(* The heart of progress: keep the whole configuration [(T, G, L)] fixed and
   induct over a *list of thread ids* [l]. Either every thread named in [l]
   is terminated-or-inert, or some thread can take a step, or the
   configuration is forbidden, or a synchronising thread's merge conflicts. *)
Lemma progress_aux :
  forall T G L (l : list tid),
    ul_progress (T, G, L) ->
    wf_cfg (T, G, L) ->
    (forall t, mem t l -> t \indom T ->
       terminated (T, G, L) t \/ inert (T, G, L) t)
    \/ (exists cfg', step (T, G, L) cfg')
    \/ forbidden (T, G, L)
    \/ conflict_detected (T, G, L).
Proof.
  introv Hulp Hwfc.
  lets (Hfin & Hwf & HrootIndom & Hterm & HdomT & HdomL): Hwfc.
  induction l as [| a l IH].
  - left. introv Hmem. inverts Hmem.
  - destruct IH as [Hall | [Hstep | [Hforb | Hconf]]];
      [ | right; left; exact Hstep
        | right; right; left; exact Hforb
        | right; right; right; exact Hconf ].
    destruct (classic (a \indom T)) as [Hain | Hanotin].
    + asserts Hbth: (binds T a (T[a])).
      { exact (thread_binds_of_indom_read Hain eq_refl). }
      destruct (T[a]) as (((st & e) & d) & h) eqn:HTa.
      destruct st.
      * (* state_new: StepStart always fires *)
        right. left. exists. applys StepStart Hbth.
      * (* state_running *)
        destruct e as [e | r].
        -- (* still computing: use [ul_progress], split on whether some
              reduction is non-blocked *)
           forwards Hex: Hulp Hbth.
           destruct (classic (exists K a0, step_ul e K a0 /\ ~ blocked T L a0))
             as [(K & a0 & Hul & Hnbl) | Hnone].
           ++ (* a non-blocked reduction is offered *)
              destruct a0; unfold blocked in Hnbl.
              ** (* spawn: pick a fresh tid and a fresh commit *)
                 right. left.
                 forwards (t' & Ht'): exists_fresh_tid Hfin.
                 forwards (c' & Hfresh): exists_commit_fresh Hwf.
                 destruct (push_thread a t' c'
                     (T[a := (state_running, K t', d, h)][t' := (state_new, te_exp e0, empty, 0)]) G)
                   as [T' G'] eqn:Heq.
                 exists. applys StepSpawn Hbth Hul Ht' Hfresh Heq.
              ** (* join: not blocked => target terminated; then split on
                    whether the merge is conflict-free *)
                 rew_logic in Hnbl. destruct Hnbl as (r0 & d0 & c0 & Hbr).
                 forwards (r1 & Heqr1 & Heqd0): Hterm Hbr. inverts Heqr1. subst d0.
                 destruct (classic (conflict_free_merge d h c0 G)) as [Hcfm | Hncfm].
                 --- right. left.
                     forwards (c'' & Hfresh): exists_commit_fresh Hwf.
                     asserts (T' & G' & Hpull & Hbindspull):
                       (exists T' G', pull_thread a t c'' T G = (T', G') /\
                                       binds T' a (state_running, te_exp e, d, c'')).
                     { exists (T[a := (state_running, te_exp e, d, c'')]) (graph_merge G c0 h c'').
                       split.
                       - unfold pull_thread, do_merge.
                         destruct (T[t]) as [[[ts0 e0] d1] c1] eqn:HHt.
                         asserts Hb2t: (binds T t (ts0, e0, d1, c1)).
                         { exact (thread_binds_of_indom_read (thread_indom_of_binds Hbr) HHt). }
                         lets Heqvt: (thread_binds_inj Hbr Hb2t). inverts Heqvt.
                         destruct (T[a]) as [[[ts2 e2] d2] c2] eqn:HHa.
                         asserts Hb2a: (binds T a (ts2, e2, d2, c2)).
                         { exact (thread_binds_of_indom_read (thread_indom_of_binds Hbth) HHa). }
                         lets Heqva: (thread_binds_inj Hbth Hb2a). inverts Heqva.
                         reflexivity.
                       - apply binds_update_same. }
                     exists. applys (>> StepJoin Hbth Hul Hbr Hcfm Hfresh Hpull Hbindspull).
                 --- right. right. right.
                     exists a e d h K. split; [exact Hbth |].
                     left. exists t r1 empty_diff c0. splits*.
              ** (* read: local (in [d]) or global ([is_latest_value]),
                    otherwise forbidden *)
                 destruct (classic (x \indom d)) as [Hxd | Hxnd].
                 --- right. left. asserts Hbv: (binds d x (d[x])).
                     { applys binds_of_indom_read Hxd. reflexivity. }
                     exists. applys StepReadLocal Hbth Hul Hbv.
                 --- destruct (classic (exists v, is_latest_value G h x v)) as [(v & Hlv) | Hnlv].
                     +++ right. left. exists. applys StepReadGlobal Hbth Hul Hxnd Hlv.
                     +++ right. right. left.
                         exists a e d h K (eff_read x). splits*.
                         simpl. rew_logic. splits*.
              ** (* write *)
                 right. left. exists. applys StepWrite Hbth Hul.
              ** (* lock: not blocked => free (or never-acquired); then
                    split on whether the merge is conflict-free *)
                 rew_logic in Hnbl.
                 destruct (classic (conflict_free_merge d h (snd (lock_read L l0)) G)) as [Hcfm | Hncfm].
                 --- right. left.
                     forwards (c'' & Hfresh): exists_commit_fresh Hwf.
                     asserts Hlr: (lock_read L l0 = (ls_free, snd (lock_read L l0))).
                     { destruct (lock_read L l0) as [ls hc] eqn:E. simpl in Hnbl. simpl.
                       rewrite Hnbl. reflexivity. }
                     asserts (T' & G' & Hpull & Hbinds''):
                       (exists T' G', pull_lock a l0 c'' T G L = (T', G') /\
                                       binds T' a (state_running, te_exp e, d, c'')).
                     { exists (T[a := (state_running, te_exp e, d, c'')])
                              (graph_merge G (snd (lock_read L l0)) h c'').
                       split.
                       - unfold pull_lock, do_merge. rewrite Hlr.
                         destruct (T[a]) as [[[ts2 e2] d2] c2] eqn:HHa.
                         asserts Hb2a: (binds T a (ts2, e2, d2, c2)).
                         { exact (thread_binds_of_indom_read (thread_indom_of_binds Hbth) HHa). }
                         lets Heqva: (thread_binds_inj Hbth Hb2a). inverts Heqva.
                         reflexivity.
                       - apply binds_update_same. }
                     exists. applys (>> StepLock Hbth Hul Hlr Hcfm Hfresh Hpull Hbinds'').
                 --- right. right. right.
                     exists a e d h K. split; [exact Hbth |].
                     right. exists l0 (snd (lock_read L l0)).
                     splits.
                     +++ exact Hul.
                     +++ destruct (lock_read L l0) as [ls hc] eqn:E. simpl in Hnbl. simpl.
                         rewrite Hnbl. reflexivity.
                     +++ exact Hncfm.
              ** (* unlock: enabled (thread holds the lock) fires,
                    otherwise forbidden *)
                 destruct (classic (exists h', lock_read L l0 = (ls_held a, h'))) as [(h0 & Hheld) | Hnheld].
                 --- right. left.
                     forwards (c'' & Hfresh): exists_commit_fresh Hwf.
                     asserts Hindom: (l0 \indom L).
                     { destruct (classic (l0 \indom L)) as [Hi|Hni]; auto.
                       asserts Heq: (lock_read L l0 = (ls_free, root_commit)).
                       { exact (read_default_notindom Hni). }
                       rewrite Heq in Hheld. inverts Hheld. }
                     asserts Hbl: (binds L l0 (ls_held a, h0)).
                     { asserts HLeq: (L[l0] = (ls_held a, h0)).
                       { transitivity (lock_read L l0).
                         - symmetry. exact (read_default_indom Hindom).
                         - exact Hheld. }
                       exact (lock_binds_of_indom_read Hindom HLeq). }
                     asserts (T' & G' & L' & Hpush & Hbinds'):
                       (exists T' G' L', push_lock a l0 c'' T G L = (T', G', L') /\
                                          binds T' a (state_running, te_exp e, empty, c'')).
                     { exists (T[a := (state_running, te_exp e, empty, c'')])
                              (graph_commit G h c'' d)
                              (L[l0 := (ls_held a, c'')]).
                       split.
                       - unfold push_lock, do_commit.
                         destruct (T[a]) as [[[ts2 e2] d2] c2] eqn:HHa.
                         asserts Hb2a: (binds T a (ts2, e2, d2, c2)).
                         { exact (thread_binds_of_indom_read (thread_indom_of_binds Hbth) HHa). }
                         lets Heqva: (thread_binds_inj Hbth Hb2a). inverts Heqva.
                         destruct (L[l0]) as [ls0 c0] eqn:HHl.
                         asserts Hb2l: (binds L l0 (ls0, c0)).
                         { exact (lock_binds_of_indom_read (lock_indom_of_binds Hbl) HHl). }
                         lets Heqvl: (lock_binds_inj Hbl Hb2l). inverts Heqvl.
                         reflexivity.
                       - apply binds_update_same. }
                     exists. applys (>> StepRelease Hbth Hul Hbl Hfresh Hpush Hbinds').
                 --- right. right. left.
                     exists a e d h K (eff_unlock l0). splits*.
           ++ (* every reduction is blocked: [a] is inert *)
              asserts Hib: (forall K0 a0, step_ul e K0 a0 -> blocked T L a0).
              { introv Hul0. destruct (classic (blocked T L a0)) as [Hb | Hnb]; auto.
                false Hnone. exists K0 a0. auto. }
              left. introv Hmem Hin. rew_listx in Hmem. destruct Hmem as [-> | Hmeml].
              ** right. exists e d h. splits; [ exact Hbth | exact Hex | exact Hib ].
              ** applys Hall Hmeml Hin.
        -- (* returned a value: StepEnd fires *)
           right. left.
           forwards (c' & Hfresh): exists_commit_fresh Hwf.
           destruct (do_commit a c' T G) as [T' G'] eqn:Heq.
           exists. applys StepEnd Hbth Hfresh Heq.
      * (* state_terminated *)
        destruct e as [e | r].
        -- (* terminated but still carrying [te_exp]: impossible by [wf_cfg] *)
           forwards (r0 & Heq0 & Hd0): Hterm Hbth. inverts Heq0.
        -- (* terminated with a return value: this thread is [terminated] *)
           forwards (r0 & Heq0 & Hd0): Hterm Hbth. inverts Heq0. subst d.
           left. introv Hmem Hin. rew_listx in Hmem. destruct Hmem as [-> | Hmeml].
           ++ left. exists r0 h. exact Hbth.
           ++ applys Hall Hmeml Hin.
    + (* [a] is not in the domain, so it contributes nothing *)
      left. introv Hmem Hin. rew_listx in Hmem. destruct Hmem as [-> | Hmeml].
      * false. applys Hanotin Hin.
      * applys Hall Hmeml Hin.
Qed.

Theorem progress :
  forall T G L,
    ul_progress (T, G, L) ->
    wf_cfg (T, G, L) ->
    done (T, G, L)
    \/ deadlocked (T, G, L)
    \/ (exists cfg', step (T, G, L) cfg')
    \/ forbidden (T, G, L)
    \/ conflict_detected (T, G, L).
Proof.
  introv Hulp Hwfc.
  lets (Hfin & _): Hwfc.
  lets (l & Hcov): finite_inv_list_covers Hfin.
  forwards Hres: (progress_aux T G L l Hulp Hwfc).
  destruct Hres as [Hall | [Hstep | [Hforb | Hconf]]].
  - (* every thread in [dom T] is terminated or inert (via the cover [l]) *)
    asserts Hdi: (forall t, t \indom T ->
                            terminated (T, G, L) t \/ inert (T, G, L) t).
    { introv Hin. applys* Hall. }
    destruct (classic (exists t, t \indom T /\ inert (T, G, L) t)) as [Hi | Hni].
    + (* some thread is inert: deadlocked *)
      right. left. split*.
    + (* no inert thread: every thread is terminated, i.e. done *)
      left. introv Hin. forwards* [Ht | Hinrt]: Hdi Hin.
      false*.
  - right. right. left. exact Hstep.
  - right. right. right. left. exact Hforb.
  - right. right. right. right. exact Hconf.
Qed.
