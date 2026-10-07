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

(* [wf_cfg] bundles everything [progress] needs to stay
   inductively true across a [step]:

   - the thread map is finite (needed to generate a fresh tid for
   [StepSpawn])

   - the graph is well-formed (acyclic and finite -- needed for
   [exists_commit_fresh]),

   - [root_commit] is always in the graph (a never-touched lock's
   [lock_read] defaults to it),

   - every thread's and lock's commit pointer is already in the
   graph (needed to justify [graph_commit_wf] / [graph_merge_wf]
   when that thread/lock is next touched),

   - a terminated thread always carries a return value with an
   empty staging area (it became terminated only via [StepEnd]),

   - every write of a volatile variable [x] is an ancestor of
   [x]'s current pointer [vc_read V x] (every volatile write is
   merged into [V[x]] by [StepWriteVolatile], even when writes of [x]
   race and are incomparable to each other),

   - [V[x]] only ever advances forward, so no earlier write can be
   "ahead" of it, and -- crucially, since dominance alone does
   not give existence -- [vc_read V x] itself always has a
   well-defined latest value whenever [x] has been written at all
   (again maintained via [StepWriteVolatile]. *)
Definition wf_cfg (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L, V) =>
      LibMap.finite T /\
      wf_graph G /\
      graph_indom G root_commit /\
      (forall t e d c, binds T t (state_terminated, e, d, c) ->
         exists r, e = te_ret r /\ d = empty) /\
      (forall t ts e d c, binds T t (ts, e, d, c) -> graph_indom G c) /\
      (forall l ls c, binds L l (ls, c) -> graph_indom G c) /\
      (forall x c, binds V x c -> graph_indom G c) /\
      (forall x t ts e d c, x \in Volatiles -> binds T t (ts, e, d, c) -> x \notindom d) /\
      (forall x c v, x \in Volatiles -> graph_writes G c x v -> ancestor G c (vc_read V x)) /\
      (forall x c v, x \in Volatiles -> graph_writes G c x v ->
         exists v', is_latest_value G (vc_read V x) x v')
  end.

(* ===================================================================== *)
(* Progress (modulo deadlock, forbidden effects, and conflicts)          *)
(* ===================================================================== *)

(* An effect is *enabled* for thread [t] (staging diff [d], commit
   pointer [h]) when its non-blocking precondition holds: a read
   must be visible either locally (in [d]) or globally (as the
   latest committed value at [h]); an unlock must target a lock
   [t] itself holds. *)
Definition enabled (G : graph) (L : locks) (t : tid) (d : diff) (h : commit) (a : eff) : Prop :=
  match a with
  | eff_read x   => x \indom d \/ exists v, is_latest_value G h x v
  | eff_unlock l => exists h', lock_read L l = (ls_held t, h')
  | _ => True
  end.

(* A *blocking* effect: joining a thread that has not terminated,
   or acquiring a lock that is currently held. These are the
   legitimate sources of deadlock (locks default to free, so there
   is no "never acquired" case). *)
Definition blocked (T : threads) (L : locks) (a : eff) : Prop :=
  match a with
  | eff_join t'  => ~ exists r d c, binds T t' (state_terminated, te_ret r, d, c)
  | eff_lock l   => fst (lock_read L l) <> ls_free
  | _ => False
  end.

(* Progress for the underlying sequential language: every running,
   still-computing thread can take a [step_ul] step. *)
Definition ul_progress (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L, V) =>
      forall t e d h,
        binds T t (state_running, te_exp e, d, h) ->
        exists K a, step_ul e K a
  end.

(* A thread is *forbidden* from stepping when the underlying
   language offers a reduction to an effect that is not enabled.
   *)
Definition forbidden (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L, V) =>
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
  | (T, G, L, V) =>
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
             ~ conflict_free_merge d h h' G)
         \/
         (exists x,
             step_ul e K (eff_read x) /\
             x \in Volatiles /\
             ~conflict_free_merge d h (vc_read V x) G))
  end.

(* A thread has terminated. *)
Definition terminated (cfg : cfg) (t : tid) : Prop :=
  match cfg with
  | (T, _, _, _) => exists r c, binds T t (state_terminated, te_ret r, empty, c)
  end.

(* A running thread is *inert* when it is still computing, can take a step,
   but every step it can take is blocked (a join on a non-terminated thread,
   or a lock on a held lock). *)
Definition inert (cfg : cfg) (t : tid) : Prop :=
  match cfg with
  | (T, _, L, _) =>
      exists e d h,
        binds T t (state_running, te_exp e, d, h) /\
        (exists K a, step_ul e K a) /\
        (forall K a, step_ul e K a -> blocked T L a)
  end.

(* The configuration is *done* when every thread has terminated. *)
Definition done (cfg : cfg) : Prop :=
  match cfg with
  | (T, _, _, _) => forall t, t \indom T -> terminated cfg t
  end.

(* The configuration is *deadlocked* when every thread is terminated or
   inert, and at least one thread is inert (so [deadlocked] is disjoint from
   [done]). *)
Definition deadlocked (cfg : cfg) : Prop :=
  match cfg with
  | (T, _, _, _) =>
      (forall t, t \indom T -> terminated cfg t \/ inert cfg t) /\
      (exists t, t \indom T /\ inert cfg t)
  end.

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

Lemma finite_pull_volatile :
  forall t l h_new T G V T' G',
    pull_volatile t l h_new T G V = (T', G') ->
    LibSet.finite (dom T) -> LibSet.finite (dom T').
Proof.
  introv Heq Hfin. unfolds pull_volatile, do_merge. destruct (vc_read V l);
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

Lemma finite_push_volatile :
  forall t l h_new h_merge T G V T' G' V',
    push_volatile t l h_new h_merge T G V = (T', G', V') ->
    LibSet.finite (dom T) -> LibSet.finite (dom T').
Proof.
  introv Heq Hfin. unfolds push_volatile.
  destruct (do_commit t h_new T G) as [T'' G''] eqn:Hdc.
  inverts Heq.
  applys finite_do_commit Hdc Hfin.
Qed.

(* A finite thread domain stays finite under a step: every rule either
   updates existing threads in place (domain unchanged) or spawns exactly
   one new thread ([StepSpawn], adding a single element). *)
Lemma step_preserves_finite :
  forall T G L V cfg',
    LibSet.finite (dom T) ->
    step (T, G, L, V) cfg' ->
    match cfg' with (T', _, _, _) => LibSet.finite (dom T') end.
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
  - (* StepReadVolatile *)
    match goal with H : pull_volatile _ _ _ _ _ _ = (_, _) |- _ =>
      forwards Hfin': finite_pull_volatile H Hfin end.
    rew_dom. autos.
  - (* StepWrite *) rew_dom. autos.
  - (* StepWriteVolatile *)
    asserts Hfin0:
      (LibSet.finite (dom (T[t:=(state_running, te_exp e, d[x:=v], h)]))).
    { rew_dom. autos. }
    match goal with H : push_volatile _ _ _ _ _ _ _ = (_, _, _) |- _ =>
      forwards Hfin'': finite_push_volatile H Hfin0 end.
    rew_dom. autos.
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

(* A step's fresh commit never writes a volatile variable (its diff is some
   thread's staging area, which -- by [Hvd] -- never holds one), so an
   ancestor-of-[vc_read] fact about a volatile writer survives a
   [graph_commit] with [V] unchanged. *)
Lemma vwa_preserved_commit :
  forall G V c cf d,
    (forall x c0 v, x \in Volatiles -> graph_writes G c0 x v -> ancestor G c0 (vc_read V x)) ->
    (forall x, x \in Volatiles -> x \notindom d) ->
    forall x c0 v,
      x \in Volatiles -> graph_writes (graph_commit G c cf d) c0 x v ->
      ancestor (graph_commit G c cf d) c0 (vc_read V x).
Proof.
  introv Hvwa Hnovol Hxvol Hgw.
  destruct (classic (c0 = cf)) as [->|Hne].
  - forwards Hbd: graph_writes_graph_commit_same Hgw.
    exfalso. applys Hnovol Hxvol. applys indom_of_binds Hbd; typeclass.
  - forwards Hgw': graph_writes_graph_commit_inv Hne Hgw.
    forwards Hanc: Hvwa Hxvol Hgw'.
    applys ancestor_graph_commit Hanc.
Qed.

(* A merge's fresh commit writes nothing at all, so likewise a
   [graph_merge] with [V] unchanged preserves the invariant. *)
Lemma vwa_preserved_merge :
  forall G V p1 p2 cf,
    (forall x c0 v, x \in Volatiles -> graph_writes G c0 x v -> ancestor G c0 (vc_read V x)) ->
    forall x c0 v,
      x \in Volatiles -> graph_writes (graph_merge G p1 p2 cf) c0 x v ->
      ancestor (graph_merge G p1 p2 cf) c0 (vc_read V x).
Proof.
  introv Hvwa Hxvol Hgw.
  destruct (classic (c0 = cf)) as [->|Hne].
  - false. applys graph_writes_graph_merge_same_false Hgw.
  - forwards Hgw': graph_writes_graph_merge_inv Hne Hgw.
    forwards Hanc: Hvwa Hxvol Hgw'.
    applys ancestor_graph_merge Hanc.
Qed.

Lemma vc_read_graph_indom_cfg :
  forall G V x,
    (forall x0 c0, binds V x0 c0 -> graph_indom G c0) ->
    graph_indom G root_commit ->
    graph_indom G (vc_read V x).
Proof.
  introv HdomV HrootIndom.
  destruct (classic (x \indom V)) as [Hindom|Hnotin].
  - asserts Heq: (vc_read V x = V[x]).
    { transitivity (V[x]); [exact (read_default_indom Hindom) | autos]. }
    rewrite Heq. asserts Hb: (binds V x V[x]). { applys* binds_of_indom_read Hindom. }
    applys* HdomV.
  - asserts Heq: (vc_read V x = root_commit).
    { exact (read_default_notindom Hnotin). }
    rewrite Heq. exact HrootIndom.
Qed.

Lemma exwa_preserved_commit :
  forall G V c cf d,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G cf ->
    (forall x0 c0, binds V x0 c0 -> graph_indom G c0) ->
    graph_indom G root_commit ->
    (forall x c0 v, x \in Volatiles -> graph_writes G c0 x v ->
       exists v', is_latest_value G (vc_read V x) x v') ->
    forall x c0 v,
      x \notindom d ->
      x \in Volatiles -> graph_writes (graph_commit G c cf d) c0 x v ->
      exists v', is_latest_value (graph_commit G c cf d) (vc_read V x) x v'.
Proof.
  introv Hedge Hfresh HdomV HrootIndom Hexwa Hnovol Hxvol Hgw.
  destruct (classic (c0 = cf)) as [->|Hne].
  - forwards Hbd: graph_writes_graph_commit_same Hgw.
    exfalso. applys Hnovol. applys indom_of_binds Hbd; typeclass.
  - forwards Hgw': graph_writes_graph_commit_inv Hne Hgw.
    forwards (v' & Hval): Hexwa Hxvol Hgw'.
    exists v'.
    asserts Hvcdom: (graph_indom G (vc_read V x)).
    { applys vc_read_graph_indom_cfg HdomV HrootIndom. }
    asserts Hvcne: (vc_read V x <> cf).
    { intro Heq. rewrite Heq in Hvcdom. applys commit_fresh_not_indom Hfresh Hvcdom. }
    asserts Hnovold: (forall v0, ~ binds d x v0).
    { introv Hbd0. applys Hnovol. applys indom_of_binds Hbd0; typeclass. }
    applys is_latest_value_graph_commit_mono Hedge Hfresh Hvcne Hnovold Hval.
Qed.

Lemma exwa_preserved_merge :
  forall G V p1 p2 cf,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G cf ->
    (forall x0 c0, binds V x0 c0 -> graph_indom G c0) ->
    graph_indom G root_commit ->
    (forall x c0 v, x \in Volatiles -> graph_writes G c0 x v ->
       exists v', is_latest_value G (vc_read V x) x v') ->
    forall x c0 v,
      x \in Volatiles -> graph_writes (graph_merge G p1 p2 cf) c0 x v ->
      exists v', is_latest_value (graph_merge G p1 p2 cf) (vc_read V x) x v'.
Proof.
  introv Hedge Hfresh HdomV HrootIndom Hexwa Hxvol Hgw.
  destruct (classic (c0 = cf)) as [->|Hne].
  - false. applys graph_writes_graph_merge_same_false Hgw.
  - forwards Hgw': graph_writes_graph_merge_inv Hne Hgw.
    forwards (v' & Hval): Hexwa Hxvol Hgw'.
    exists v'.
    asserts Hvcdom: (graph_indom G (vc_read V x)).
    { applys vc_read_graph_indom_cfg HdomV HrootIndom. }
    asserts Hvcne: (vc_read V x <> cf).
    { intro Heq. rewrite Heq in Hvcdom. applys commit_fresh_not_indom Hfresh Hvcdom. }
    applys is_latest_value_graph_merge_mono Hedge Hfresh Hvcne Hval.
Qed.

Theorem step_preserves_wf_cfg :
  forall cfg cfg',
    wf_cfg cfg ->
    step cfg cfg' ->
    wf_cfg cfg'.
Proof.
  introv Hwfc Hstep. destruct cfg as (((T & G) & L) & V).
  destruct Hwfc as (Hfin & Hwf & HrootIndom & Hterm & HdomT & HdomL & HdomV & Hvd & Hvwa & Hexwa).
  lets (_ & _ & Hedge): Hwf.
  hint LibSet.finite_single.
  hint LibSet.finite_union.
  forwards* Hfin':step_preserves_finite Hstep.
  inverts Hstep.
  - (* StepStart *)
    splits 10.
    + autos.
    + exact Hwf.
    + exact HrootIndom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq. applys* HdomT.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* HdomT.
    + exact HdomL.
    + exact HdomV.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts* Hbinds'.
      * forwards* Heq: binds_inj Hbinds. typeclass.
    + exact Hvwa.
    + exact Hexwa.
  - (* StepEnd *)
    match goal with H : do_commit _ _ _ _ = (_, _) |- _ => rename H into Hdc end.
    unfolds do_commit.
    match goal with H : binds T t (state_running, te_ret r, ?d0, ?h0) |- _ =>
      replace (T[t]) with (state_running, te_ret r, d0, h0) in Hdc by (symmetry; applys* read_of_binds) end.
    inverts Hdc.
    splits 10.
    + autos.
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
    + introv Hbinds. apply* graph_commit_indom.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts Hbinds'.
        applys indom_empty_inv.
      * forwards* Hbinds'': binds_update_neq_inv Hbinds' C.
    + asserts HnoVolInD: (forall x0, x0 \in Volatiles -> x0 \notindom d).
      { introv Hxvol0. applys Hvd Hxvol0. eassumption. }
      applys vwa_preserved_commit Hvwa HnoVolInD.
    + asserts HnoVolInD: (forall x0, x0 \in Volatiles -> x0 \notindom d).
      { introv Hxvol0. applys Hvd Hxvol0. eassumption. }
      introv Hxvol Hgw.
      applys* (>> exwa_preserved_commit Hedge HdomV HrootIndom Hexwa (HnoVolInD x Hxvol) Hxvol Hgw).
  - (* StepReadLocal *)
    splits 10.
    + autos.
    + exact Hwf.
    + exact HrootIndom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq. applys* HdomT.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* HdomT.
    + exact HdomL.
    + exact HdomV.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts* Hbinds'.
      * auto_star.
    + exact Hvwa.
    + exact Hexwa.
  - (* StepReadGlobal *)
    splits 10.
    + autos.
    + exact Hwf.
    + exact HrootIndom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq. applys* HdomT.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* HdomT.
    + exact HdomL.
    + exact HdomV.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts* Hbinds'.
      * auto_star.
    + exact Hvwa.
    + exact Hexwa.
  - (* StepReadVolatile *)
    match goal with H : pull_volatile _ _ _ _ _ _ = (_, _) |- _ => rename H into Hpv end.
    asserts Hvcindom: (graph_indom G (vc_read V x)).
    {
      destruct (classic (x \indom V)) as [Hindom|Hnotin].
      - asserts Heq: (vc_read V x = V[x]).
        { transitivity (V[x]); [exact (read_default_indom Hindom) | autos]. }
        rewrite Heq.
        asserts Hb: (binds V x V[x]). { applys* binds_of_indom_read Hindom. }
        applys* HdomV.
      - asserts Heq: (vc_read V x = root_commit).
        { exact (read_default_notindom Hnotin). }
        rewrite Heq. exact HrootIndom.
    }
    unfolds pull_volatile, do_merge.
    match goal with H : binds T t (state_running, te_exp e, ?d0, ?h0) |- _ =>
      replace (T[t]) with (state_running, te_exp e, d0, h0) in Hpv by (symmetry; applys* read_of_binds) end.
    inverts Hpv.
    splits 10.
    + autos.
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
    + introv Hbinds. apply* graph_merge_indom.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts* Hbinds'.
      * forwards* Hbinds'': binds_update_neq_inv Hbinds'.
    + applys vwa_preserved_merge Hvwa.
    + applys* exwa_preserved_merge Hedge HdomV HrootIndom Hexwa.
  - (* StepWrite *)
    splits 10.
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
    + exact HdomV.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts Hbinds'.
        rew_dom. intros contra. rew_set in contra.
        branches; auto_star.
        apply* Hvd.
      * auto_star.
    + exact Hvwa.
    + exact Hexwa.
  - (* StepWriteVolatile *)
    match goal with H : push_volatile _ _ _ _ _ _ _ = (_, _, _) |- _ => rename H into Hpv end.
    asserts Hvcindom: (graph_indom G (vc_read V x)).
    { applys vc_read_graph_indom_cfg HdomV HrootIndom. }
    asserts Hhindom: (graph_indom G h).
    { match goal with H : binds T t (state_running, te_exp e, d, h) |- _ => applys HdomT H end. }
    match goal with H : commit_fresh G h' |- _ => rename H into Hfresh1 end.
    match goal with H : commit_fresh (graph_commit G h h' d[x:=v]) h'' |- _ => rename H into Hfresh2 end.
    unfolds push_volatile, do_commit.
    rewrite read_update_same in Hpv.
    inverts Hpv.
    asserts HnoVolInD: (forall x1, x1 \in Volatiles -> x1 \notindom d).
    { introv Hxvol1. applys Hvd Hxvol1. eassumption. }
    asserts Hwf1: (wf_graph (graph_commit G h h' d[x:=v])).
    { applys graph_commit_wf Hwf Hfresh1 Hhindom. }
    lets (_ & _ & Hedge1): Hwf1.
    asserts Hvcindom1: (graph_indom (graph_commit G h h' d[x:=v]) (vc_read V x)).
    { apply graph_commit_indom. exact Hvcindom. }
    splits 10.
    + unfolds finite. rew_dom. autos.
    + applys graph_merge_wf Hwf1 Hfresh2 Hvcindom1.
      apply graph_commit_indom_same.
    + apply graph_merge_indom. apply graph_commit_indom. exact HrootIndom.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds1: binds_update_neq_inv Hbinds Hne.
        forwards Hbinds2: binds_update_neq_inv Hbinds1 Hne.
        forwards Hbinds3: binds_update_neq_inv Hbinds2 Hne.
        applys* Hterm.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply graph_merge_indom. apply graph_commit_indom_same.
      * forwards Hbinds1: binds_update_neq_inv Hbinds Hne.
        forwards Hbinds2: binds_update_neq_inv Hbinds1 Hne.
        forwards Hbinds3: binds_update_neq_inv Hbinds2 Hne.
        apply graph_merge_indom. apply graph_commit_indom.
        applys* HdomT.
    + introv Hbinds. apply graph_merge_indom. apply graph_commit_indom.
      applys* HdomL.
    + introv Hbinds. destruct (classic (x0 = x)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply graph_merge_indom_same.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        apply graph_merge_indom. apply graph_commit_indom.
        applys* HdomV.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts Hbinds'.
        applys indom_empty_inv.
      * do 2 apply binds_update_neq_inv in Hbinds'; auto_star.
    + (* [x]'s stored commit [h''] merges the old stored commit and the fresh
         write [h'], so every earlier [x]-writer still reaches it; any other
         volatile is untouched and its writers cannot be [h'']/[h'] (whose own
         diffs carry no other volatile, by [Hvd], and merge nothing). *)
      intros x0 c0 v0 Hxvol0 Hgw0.
      destruct (classic (c0 = h'')) as [->|Hneh''].
      * false. applys graph_writes_graph_merge_same_false Hgw0.
      * forwards Hgw1: graph_writes_graph_merge_inv Hneh'' Hgw0.
        destruct (classic (x0 = x)) as [->|Hnex0].
        -- asserts Hveq: (vc_read (V[x := h'']) x = h'').
           { unfold vc_read. apply read_default_update_same. }
           rewrite Hveq.
           destruct (classic (c0 = h')) as [->|Hneh'].
           ++ apply ancestor_graph_merge_edge_l.
           ++ forwards Hgw2: graph_writes_graph_commit_inv Hneh' Hgw1.
              forwards Hanc0: Hvwa Hxvol0 Hgw2.
              applys ancestor_trans (vc_read V x).
              ** apply ancestor_graph_merge. apply ancestor_graph_commit. exact Hanc0.
              ** apply ancestor_graph_merge_edge_r.
        -- asserts Hveq: (vc_read (V[x := h'']) x0 = vc_read V x0).
           { unfold vc_read. apply read_default_update_neq. intro Heq. applys Hnex0. symmetry. exact Heq. }
           rewrite Hveq.
           destruct (classic (c0 = h')) as [->|Hneh'].
           ++ forwards Hbd: graph_writes_graph_commit_same Hgw1.
              forwards Hbd': binds_update_neq_inv Hbd Hnex0.
              exfalso. applys HnoVolInD Hxvol0. applys indom_of_binds Hbd'; typeclass.
           ++ forwards Hgw2: graph_writes_graph_commit_inv Hneh' Hgw1.
              forwards Hanc0: Hvwa Hxvol0 Hgw2.
              apply ancestor_graph_merge. apply ancestor_graph_commit. exact Hanc0.
    + (* the just-written [x] has [is_latest_value] at the merge [h'']: the
         fresh write [h'] is a sink writer of [x]
         ([is_latest_value_graph_merge_fresh_writer]), even when earlier
         writers of [x] are incomparable to it. Any other volatile is
         untouched: lift the old witness through the commit then the merge. *)
      intros x0 c0 v0 Hxvol0 Hgw0.
      destruct (classic (c0 = h'')) as [->|Hneh''].
      * false. applys graph_writes_graph_merge_same_false Hgw0.
      * forwards Hgw1: graph_writes_graph_merge_inv Hneh'' Hgw0.
        destruct (classic (x0 = x)) as [->|Hnex0].
        -- asserts Hveq: (vc_read (V[x := h'']) x = h'').
           { unfold vc_read. apply read_default_update_same. }
           rewrite Hveq.
           exists v.
           applys is_latest_value_graph_merge_fresh_writer Hedge1 Hfresh2.
           ++ apply graph_commit_indom_same.
           ++ applys graph_writes_graph_commit_new. apply binds_update_same.
           ++ applys graph_commit_new_sink Hedge Hfresh1 Hhindom.
        -- asserts Hveq: (vc_read (V[x := h'']) x0 = vc_read V x0).
           { unfold vc_read. apply read_default_update_neq. intro Heq. applys Hnex0. symmetry. exact Heq. }
           rewrite Hveq.
           asserts Hnovol0: (x0 \notindom (d[x := v])).
           { intro Hin. destruct (indom_update_inv Hin) as [Hc | Hd0].
             - applys Hnex0 Hc.
             - applys HnoVolInD Hxvol0 Hd0. }
           forwards (v' & Hlv1): (>> exwa_preserved_commit Hedge Hfresh1 HdomV HrootIndom Hexwa Hnovol0 Hxvol0 Hgw1).
           exists v'.
           asserts Hvcne2: (vc_read V x0 <> h'').
           { intro Heq.
             asserts Hdom2: (graph_indom (graph_commit G h h' d[x:=v]) (vc_read V x0)).
             { apply graph_commit_indom. applys vc_read_graph_indom_cfg HdomV HrootIndom. }
             rewrite Heq in Hdom2. applys commit_fresh_not_indom Hfresh2 Hdom2. }
           applys is_latest_value_graph_merge_mono Hedge1 Hfresh2 Hvcne2 Hlv1.
  - (* StepSpawn *)
    match goal with H : push_thread _ _ _ _ _ = (_, _) |- _ => rename H into Hpt end.
    asserts Hneq: (t <> t').
    { introv Heq. subst. match goal with H : t' \notindom T |- _ => applys* H end. }
    unfolds push_thread, do_commit.
    rewrite~ read_update_neq in Hpt. rewrite read_update_same in Hpt.
    rewrite~ read_update_neq in Hpt. rewrite read_update_same in Hpt.
    inverts Hpt.
    splits 10.
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
    + introv Hbinds. apply* graph_commit_indom.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts Hbinds'.
        applys indom_empty_inv.
      * forwards Hbinds'': binds_update_inv Hbinds'.
        case_if as C'.
        -- subst. inverts Hbinds''. applys indom_empty_inv.
        -- do 2 apply binds_update_neq_inv in Hbinds''; autos.
           auto_star.
    + asserts HnoVolInD: (forall x0, x0 \in Volatiles -> x0 \notindom d).
      { introv Hxvol0. applys Hvd Hxvol0. eassumption. }
      applys vwa_preserved_commit Hvwa HnoVolInD.
    + asserts HnoVolInD: (forall x0, x0 \in Volatiles -> x0 \notindom d).
      { introv Hxvol0. applys Hvd Hxvol0. eassumption. }
      introv Hxvol Hgw.
      applys* (>> exwa_preserved_commit Hedge HdomV HrootIndom Hexwa (HnoVolInD x Hxvol) Hxvol Hgw).
  - (* StepJoin *)
    match goal with H : pull_thread _ _ _ _ _ = (_, _) |- _ => rename H into Hpt end.
    unfolds pull_thread, do_merge.
    replace (T[t']) with (state_terminated, te_ret r, empty_diff, h') in Hpt
      by (symmetry; applys* read_of_binds).
    replace (T[t]) with (state_running, te_exp e, d, h) in Hpt
      by (symmetry; applys* read_of_binds).
    inverts Hpt.
    splits 10.
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
    + introv Hbinds. apply* graph_merge_indom.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts* Hbinds'.
      * forwards* Hbinds'': binds_update_neq_inv Hbinds' C.
    + applys vwa_preserved_merge Hvwa.
    + applys* exwa_preserved_merge Hedge HdomV HrootIndom Hexwa.
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
    splits 10.
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
    + introv Hbinds. apply* graph_merge_indom.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts* Hbinds'.
      * forwards* Hbinds'': binds_update_neq_inv Hbinds' C.
    + applys vwa_preserved_merge Hvwa.
    + applys* exwa_preserved_merge Hedge HdomV HrootIndom Hexwa.
  - (* StepRelease: the thread already holds the lock, so its commit is
       already known to be in the graph via [HdomL]. *)
    match goal with H : push_lock _ _ _ _ _ _ = (_, _, _) |- _ => rename H into Hpl end.
    unfolds push_lock, do_commit.
    match goal with H : binds T t (state_running, te_exp e, ?d0, ?h0) |- _ =>
      replace (T[t]) with (state_running, te_exp e, d0, h0) in Hpl by (symmetry; applys* read_of_binds) end.
    match goal with H : binds L l0 (ls_held t, ?c0) |- _ =>
      replace (L[l0]) with (ls_held t, c0) in Hpl by (symmetry; applys* read_of_binds) end.
    inverts Hpl.
    splits 10.
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
    + introv Hbinds. apply* graph_commit_indom.
    + introv Hvol Hbinds.
      forwards Hbinds': binds_update_inv Hbinds.
      case_if as C.
      * subst. inverts Hbinds'. applys indom_empty_inv.
      * forwards* Hbinds'': binds_update_neq_inv Hbinds' C.
    + asserts HnoVolInD: (forall x0, x0 \in Volatiles -> x0 \notindom d).
      { introv Hxvol0. applys Hvd Hxvol0. eassumption. }
      applys vwa_preserved_commit Hvwa HnoVolInD.
    + asserts HnoVolInD: (forall x0, x0 \in Volatiles -> x0 \notindom d).
      { introv Hxvol0. applys Hvd Hxvol0. eassumption. }
      introv Hxvol Hgw.
      applys* (>> exwa_preserved_commit Hedge HdomV HrootIndom Hexwa (HnoVolInD x Hxvol) Hxvol Hgw).
Qed.

(* ===================================================================== *)
(* Progress (modulo deadlock, forbidden effects, and conflicts)          *)
(* ===================================================================== *)

Lemma thread_indom_of_binds :
  forall {t : tid} {T : threads} {v : thread}, binds T t v -> t \indom T.
Proof. introv Hb. exact (@indom_of_binds tid thread Branching.inhab_thread T t v Hb). Qed.

Lemma thread_binds_of_indom_read :
  forall {t : tid} {T : threads} {v : thread}, t \indom T -> T[t] = v -> binds T t v.
Proof. introv Hin Heq. exact (@binds_of_indom_read tid thread Branching.inhab_thread T t v Hin Heq). Qed.

Lemma thread_binds_inj :
  forall {t : tid} {T : threads} {v1 v2 : thread}, binds T t v1 -> binds T t v2 -> v1 = v2.
Proof. introv Hb1 Hb2. exact (@binds_inj tid t thread Branching.inhab_thread v1 v2 T Hb1 Hb2). Qed.

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
  forall T G L V (l : list tid),
    ul_progress (T, G, L, V) ->
    wf_cfg (T, G, L, V) ->
    (forall t, mem t l -> t \indom T ->
       terminated (T, G, L, V) t \/ inert (T, G, L, V) t)
    \/ (exists cfg', step (T, G, L, V) cfg')
    \/ forbidden (T, G, L, V)
    \/ conflict_detected (T, G, L, V).
Proof.
  introv Hulp Hwfc.
  lets (Hfin & Hwf & HrootIndom & Hterm & HdomT & HdomL & HdomV & Hvd & Hvwa & Hexwa): Hwfc.
  lets (_ & _ & Hedge): Hwf.
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
              ** (* read: volatile or normal *)
                 destruct (classic (x \in Volatiles)) as [Hvol | Hnvol].
                 --- (* volatile read: split on whether the merge is conflict-free *)
                     destruct (classic (conflict_free_merge d h (vc_read V x) G)) as [Hcfm | Hncfm].
                     +++ forwards (c'' & Hfresh): exists_commit_fresh Hwf.
                         asserts (T' & G' & Hpull & Hbinds''):
                           (exists T' G', pull_volatile a x c'' T G V = (T', G') /\
                                          binds T' a (state_running, te_exp e, d, c'')).
                         {
                           exists (T[a := (state_running, te_exp e, d, c'')])
                                  (graph_merge G (vc_read V x) h c'').
                           split.
                           - unfold pull_volatile, do_merge.
                             replace (T[a]) with (state_running, te_exp e, d, h).
                             reflexivity.
                           - apply binds_update_same.
                         }
                         (* split on whether there is a latest value *)
                         destruct (classic (exists v, is_latest_value G' c'' x v)) as [(v & Hlv)| Hnex].
                         *** right. left.
                             exists. applys* StepReadVolatile.
                         *** right. right. left.
                             exists a e d h K (eff_read x). splits; auto.
                             unfolds pull_volatile, do_merge.
                             replace (T[a]) with (state_running, te_exp e, d, h) in Hpull.
                             inverts Hpull.
                             simpl. rew_logic. split; [applys* Hvd|].
                             (* derive a latest value at [c''] to contradict [Hnex] *)
                             intros v contra. apply Hnex.
                             forwards (c & Hwrites & Hdomc & Hanc): is_latest_value_writer_indom contra.
                             forwards* (v0 & Hval0): Hexwa Hwrites.
                             asserts Hp1dom: (graph_indom G (vc_read V x)).
                             { applys vc_read_graph_indom_cfg HdomV HrootIndom. }
                             asserts Hp2dom: (graph_indom G h). { applys* HdomT. }
                             exists v0.
                             applys* is_latest_value_graph_merge_fresh Hedge Hfresh Hp1dom Hp2dom Hval0.
                     +++ right. right. right.
                         exists a e d h K. splits~.
                         right. right.
                         exists x. splits*.
                 --- (* normal read: local (in [d]) or global ([is_latest_value]),
                        otherwise forbidden *)
                   destruct (classic (x \indom d)) as [Hxd | Hxnd].
                   +++ right. left. asserts Hbv: (binds d x (d[x])).
                       { applys binds_of_indom_read Hxd. reflexivity. }
                       exists. applys StepReadLocal Hbth Hul Hnvol Hbv.
                   +++ destruct (classic (exists v, is_latest_value G h x v)) as [(v & Hlv) | Hnlv].
                       *** right. left. exists. applys StepReadGlobal Hbth Hul Hnvol Hxnd Hlv.
                       *** right. right. left.
                           exists a e d h K (eff_read x). splits*.
                           simpl. rew_logic. splits*.
              ** (* write: volatile or normal *)
                 destruct (classic (x \in Volatiles)) as [Hvol | Hnvol].
                 --- (* volatile write: commit then merge; there is no conflict check
                        and no [is_latest_value] obligation, so it always fires. *)
                     right. left.
                     asserts Hp2dom: (graph_indom G h). { applys* HdomT. }
                     forwards (c' & Hfresh1): exists_commit_fresh Hwf.
                     asserts Hwf1: (wf_graph (graph_commit G h c' d[x := v])).
                     { applys graph_commit_wf Hwf Hfresh1 Hp2dom. }
                     forwards (c'' & Hfresh2): exists_commit_fresh Hwf1.
                     asserts (T' & G' & V' & Hpush):
                       (exists T' G' V',
                          push_volatile a x c' c''
                            (T[a := (state_running, te_exp e, d[x := v], h)]) G V
                          = (T', G', V')).
                     { exists. unfold push_volatile, do_commit. rewrite read_update_same. reflexivity. }
                     exists. applys* StepWriteVolatile.
                 --- right. left. exists. applys StepWrite Hbth Hul Hnvol.
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
                     right. left. exists l0 (snd (lock_read L l0)).
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
  forall T G L V,
    ul_progress (T, G, L, V) ->
    wf_cfg (T, G, L, V) ->
    done (T, G, L, V)
    \/ deadlocked (T, G, L, V)
    \/ (exists cfg', step (T, G, L, V) cfg')
    \/ forbidden (T, G, L, V)
    \/ conflict_detected (T, G, L, V).
Proof.
  introv Hulp Hwfc.
  lets (Hfin & _): Hwfc.
  lets (l & Hcov): finite_inv_list_covers Hfin.
  forwards Hres: (progress_aux T G L V l Hulp Hwfc).
  destruct Hres as [Hall | [Hstep | [Hforb | Hconf]]].
  - (* every thread in [dom T] is terminated or inert (via the cover [l]) *)
    asserts Hdi: (forall t, t \indom T ->
                            terminated (T, G, L, V) t \/ inert (T, G, L, V) t).
    { introv Hin. applys* Hall. }
    destruct (classic (exists t, t \indom T /\ inert (T, G, L, V) t)) as [Hi | Hni].
    + (* some thread is inert: deadlocked *)
      right. left. split*.
    + (* no inert thread: every thread is terminated, i.e. done *)
      left. introv Hin. forwards* [Ht | Hinrt]: Hdi Hin.
      false*.
  - right. right. left. exact Hstep.
  - right. right. right. left. exact Hforb.
  - right. right. right. right. exact Hconf.
Qed.
