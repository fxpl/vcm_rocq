From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Linear.

Import Graph.
Import GraphFacts.
Import Linear.

(* ===================================================================== *)
(* Well-formedness                                                       *)
(* ===================================================================== *)

(* [wf_cfg] bundles everything [progress] needs to stay inductively true
   across a [step]: the thread map is finite (needed to generate a fresh tid
   for [StepSpawn]), the graph is well-formed (acyclic and finite -- needed
   for [exists_commit_fresh]), the global head [g] is always in the graph
   (every [global_commit] commits *onto* [g], so this is the only
   graph-indom fact [progress] ever needs -- unlike [Branching], threads
   never carry an independent commit that needs its own invariant, since
   every thread's pointer is either [g] itself or an old snapshot of it,
   never freshly created), and a terminated thread always carries a return
   value with an empty staging area (it became terminated only via
   [StepEnd]). *)
Definition wf_cfg (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, g, L) =>
      LibMap.finite T /\
      wf_graph G /\
      graph_indom G g /\
      (forall t e d c, binds T t (state_terminated, e, d, c) ->
         exists r, e = te_ret r /\ d = empty)
  end.

(* ===================================================================== *)
(* Progress (modulo deadlock, forbidden effects, and conflicts)          *)
(* ===================================================================== *)

(* An effect is *enabled* for thread [t] (staging diff [d], commit pointer
   [c]) when its non-blocking precondition holds: a read must be visible
   either locally (in [d]) or globally (as the latest committed value at
   [c]); an unlock must target a lock [t] itself holds (locks carry no
   commit in this model -- synchronisation goes entirely through the global
   head [g], so this is exactly [SharedMemory]'s notion). Writes, spawns,
   joins and locks have no such precondition -- whether a join/lock can
   actually fire is the *blocking* question below, and whether *any*
   synchronising step (end/spawn/join/lock/release) can fire *without* a
   conflict is the separate [conflict_detected] question. *)
Definition enabled (G : graph) (L : locks) (t : tid) (d : diff) (c : commit) (a : eff) : Prop :=
  match a with
  | eff_read x   => x \indom d \/ exists v, is_latest_value G c x v
  | eff_unlock l => lock_read L l = ls_held t
  | _ => True
  end.

(* A *blocking* effect: joining a thread that has not terminated, or
   acquiring a lock that is currently held. These are the legitimate
   sources of deadlock (locks default to free, so there is no "never
   acquired" case). *)
Definition blocked (T : threads) (L : locks) (a : eff) : Prop :=
  match a with
  | eff_join t'  => ~ exists r d c, binds T t' (state_terminated, te_ret r, d, c)
  | eff_lock l   => lock_read L l <> ls_free
  | _ => False
  end.

(* Progress for the underlying sequential language: every running,
   still-computing thread can take a [step_ul] step. Nothing is assumed
   about whether the resulting effect is [enabled] -- a thread offering a
   [step_ul] to a disabled effect is exactly the [forbidden] situation that
   [progress] reports separately. *)
Definition ul_progress (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, g, L) =>
      forall t e d c,
        binds T t (state_running, te_exp e, d, c) ->
        exists K a, step_ul e K a
  end.

(* A thread is *forbidden* from stepping when the underlying language offers
   a reduction to an effect that is not enabled: a read that is visible
   neither locally nor globally, or an unlock of a lock the thread does not
   itself hold. *)
Definition forbidden (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, g, L) =>
      exists t e d c K a,
        binds T t (state_running, te_exp e, d, c) /\
        step_ul e K a /\
        ~ enabled G L t d c a
  end.

(* A thread is poised to synchronise with the global branch -- return
   (commit its final diff), spawn (commit and hand the child a snapshot),
   join a terminated thread, acquire a free lock, or release a held one --
   but the commit that synchronisation would perform is not conflict-free
   ([lin_conflict_free]: some variable it wrote was also written, on the
   global branch, since its own commit [c]). This is the other
   (non-[forbidden]) way a thread can get stuck: not a deadlock (the
   blocking precondition, if any, is satisfied), not a language-level
   violation (the effect is enabled), but a genuine write-write race against
   the single global branch. Unlike [Branching] (where only [join]/[lock]
   perform a check beyond blocking), *every* synchronising operation here
   checks [lin_conflict_free], since they all commit onto the one shared
   branch. *)
Definition conflict_detected (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, g, L) =>
      exists t d c,
        (exists r,
            binds T t (state_running, te_ret r, d, c) /\
            ~ lin_conflict_free d c g G)
        \/
        (exists e K,
            binds T t (state_running, te_exp e, d, c) /\
            ((exists e', step_ul e K (eff_spawn e')) \/
             (exists t' r d' c', step_ul e K (eff_join t') /\
                                  binds T t' (state_terminated, te_ret r, d', c')) \/
             (exists l, step_ul e K (eff_lock l) /\ lock_read L l = ls_free) \/
             (exists l, step_ul e K (eff_unlock l) /\ lock_read L l = ls_held t)) /\
            ~ lin_conflict_free d c g G)
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
  | (T, _, _, L) =>
      exists e d c,
        binds T t (state_running, te_exp e, d, c) /\
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

(* [thread]-specialised re-statements of the generic [LibMap] read/binds
   lemmas, with [Linear.inhab_thread] supplied *explicitly*. Typeclass
   search for a bare [Inhab thread] (a [Definition], not folded back from
   its tuple expansion) does not reliably find [Linear.inhab_thread] when
   the goal is stated in unfolded tuple form (as [binds_inj]'s generic
   statement forces) -- pin it down here once so the rest of the proof
   doesn't hit that ambiguity. (Locks carry no commit in this model --
   [locks := map lid lock_state] -- so [lock_state]'s single, canonical
   [Inhab] instance from [Common.v] is unambiguous and needs no such
   wrapper.) *)
Lemma thread_read_of_binds :
  forall {t : tid} {T : threads} {v : thread}, binds T t v -> T[t] = v.
Proof. introv Hb. exact (@read_of_binds tid thread Linear.inhab_thread T t v Hb). Qed.

Lemma thread_indom_of_binds :
  forall {t : tid} {T : threads} {v : thread}, binds T t v -> t \indom T.
Proof. introv Hb. exact (@indom_of_binds tid thread Linear.inhab_thread T t v Hb). Qed.

Lemma thread_binds_of_indom_read :
  forall {t : tid} {T : threads} {v : thread}, t \indom T -> T[t] = v -> binds T t v.
Proof. introv Hin Heq. exact (@binds_of_indom_read tid thread Linear.inhab_thread T t v Hin Heq). Qed.

Lemma thread_binds_inj :
  forall {t : tid} {T : threads} {v1 v2 : thread}, binds T t v1 -> binds T t v2 -> v1 = v2.
Proof. introv Hb1 Hb2. exact (@binds_inj tid t thread Linear.inhab_thread v1 v2 T Hb1 Hb2). Qed.

(* [global_commit] computes to a concrete pair once [T[t]]'s shape is known
   -- avoids ever touching a bare, un-generalised [T[t]] inside a [let]
   scrutinee (which [rewrite] cannot reliably see into). *)
Lemma global_commit_eq :
  forall (g g' : commit) {t : tid} {T : threads} {G : graph}
         {st : thread_state} {e : thread_exp} {d : diff} {c : commit},
    binds T t (st, e, d, c) ->
    global_commit t g g' T G = (T[t := (st, e, empty, g')], graph_commit G g g' d).
Proof.
  introv Hb. unfold global_commit.
  destruct (T[t]) as [[[st0 e0] d0] c0] eqn:HH.
  asserts Hb2: (binds T t (st0, e0, d0, c0)).
  { exact (thread_binds_of_indom_read (thread_indom_of_binds Hb) HH). }
  lets Heqv: (thread_binds_inj Hb Hb2). inverts Heqv.
  reflexivity.
Qed.

Lemma finite_global_commit :
  forall t g g' T G T' G',
    global_commit t g g' T G = (T', G') ->
    LibSet.finite (dom T) -> LibSet.finite (dom T').
Proof.
  introv Heq Hfin. unfolds global_commit. destruct (T[t]) as [[[st e] d] c].
  inverts Heq. rew_dom. apply~ LibSet.finite_union. apply LibSet.finite_single.
Qed.

(* A finite thread domain stays finite under a step: every rule either
   updates existing threads in place (domain unchanged) or spawns exactly
   one new thread ([StepSpawn], adding a single element). *)
Lemma step_preserves_finite :
  forall T G g L cfg',
    LibSet.finite (dom T) ->
    step (T, G, g, L) cfg' ->
    match cfg' with (T', _, _, _) => LibSet.finite (dom T') end.
Proof.
  introv Hfin Hstep.
  hint LibSet.finite_single.
  hint LibSet.finite_union.
  inverts Hstep; simpl.
  - (* StepStart *) rew_dom. autos.
  - (* StepEnd *)
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ =>
      forwards Hfin': finite_global_commit H Hfin end.
    rew_dom. autos.
  - (* StepReadLocal *) rew_dom. autos.
  - (* StepReadGlobal *) rew_dom. autos.
  - (* StepWrite *) rew_dom. autos.
  - (* StepSpawn *)
    asserts Hfin0:
      (LibSet.finite (dom (T[t := (state_running, K t', d, c)][t' := (state_new, te_exp e', empty, g')]))).
    { rew_dom. autos. }
    applys* finite_global_commit.
  - (* StepJoin *) rew_dom. autos.
  - (* StepLock *) rew_dom. autos.
  - (* StepRelease *)
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ =>
      forwards Hfin': finite_global_commit H Hfin end.
    rew_dom. autos.
Qed.

(* [wf_cfg] is preserved by [step]: finiteness ([step_preserves_finite]),
   well-formedness and indom-ness of the (possibly advanced) global head
   (every graph change is a [graph_commit] onto [g], from [g] itself, which
   is already in the graph by [HrootG] -- [graph_commit_wf] /
   [graph_commit_indom_same]), and the terminated-thread shape (only
   [StepEnd] produces one, with [te_ret] and an empty staging area). *)
Theorem step_preserves_wf_cfg :
  forall cfg cfg',
    wf_cfg cfg ->
    step cfg cfg' ->
    wf_cfg cfg'.
Proof.
  introv Hwfc Hstep. destruct cfg as (((T & G) & g) & L).
  destruct Hwfc as (Hfin & Hwf & HrootG & Hterm).
  hint LibSet.finite_single.
  hint LibSet.finite_union.
  inverts Hstep.
  - (* StepStart *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact HrootG.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepEnd *)
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    rewrite (global_commit_eq g g' H3) in Hgc.
    inverts Hgc.
    splits.
    + unfolds finite. rew_dom. autos.
    + apply* graph_commit_wf.
    + apply* graph_commit_indom_same.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq. eexists. splits*.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne. applys* Hterm.
  - (* StepReadLocal *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact HrootG.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepReadGlobal *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact HrootG.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepWrite *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact HrootG.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepSpawn *)
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    asserts Hneq: (t <> t').
    { introv Heqtt. subst. match goal with H : t' \notindom T |- _ => applys* H end. }
    asserts Hbt: (binds (T[t := (state_running, K t', d, c)][t' := (state_new, te_exp e', empty, g')]) t
                    (state_running, K t', d, c)).
    { applys binds_update_neq; [ | applys binds_update_same ]. auto. }
    rewrite (global_commit_eq g g' Hbt) in Hgc.
    inverts Hgc.
    splits.
    + asserts Hfin0:
        (LibSet.finite (dom (T[t := (state_running, K t', d, c)][t' := (state_new, te_exp e', empty, g')]))).
      { unfolds finite. rew_dom. autos. }
      unfolds finite. rew_dom. autos.
    + apply* graph_commit_wf.
    + apply* graph_commit_indom_same.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        destruct (classic (t0 = t')) as [->|Hne'].
        -- forwards Heq: binds_update_same_inv Hbinds'. inverts Heq.
        -- forwards Hbinds'': binds_update_neq_inv Hbinds' Hne'.
           forwards Hbinds3: binds_update_neq_inv Hbinds'' Hne. applys* Hterm.
  - (* StepJoin *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact HrootG.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepLock *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact HrootG.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepRelease *)
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    rewrite (global_commit_eq g g' H3) in Hgc.
    inverts Hgc.
    splits.
    + unfolds finite. rew_dom. autos.
    + apply* graph_commit_wf.
    + apply* graph_commit_indom_same.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne. applys* Hterm.
Qed.

(* ===================================================================== *)
(* Progress (modulo deadlock, forbidden effects, and conflicts)          *)
(* ===================================================================== *)

(* The heart of progress: keep the whole configuration [(T, G, g, L)] fixed
   and induct over a *list of thread ids* [l]. Either every thread named in
   [l] is terminated-or-inert, or some thread can take a step, or the
   configuration is forbidden, or a synchronising thread's commit
   conflicts. *)
Lemma progress_aux :
  forall T G g L (l : list tid),
    ul_progress (T, G, g, L) ->
    wf_cfg (T, G, g, L) ->
    (forall t, mem t l -> t \indom T ->
       terminated (T, G, g, L) t \/ inert (T, G, g, L) t)
    \/ (exists cfg', step (T, G, g, L) cfg')
    \/ forbidden (T, G, g, L)
    \/ conflict_detected (T, G, g, L).
Proof.
  introv Hulp Hwfc.
  lets (Hfin & Hwf & HrootG & Hterm): Hwfc.
  induction l as [| a l IH].
  - left. introv Hmem. inverts Hmem.
  - destruct IH as [Hall | [Hstep | [Hforb | Hconf]]];
      [ | right; left; exact Hstep
        | right; right; left; exact Hforb
        | right; right; right; exact Hconf ].
    destruct (classic (a \indom T)) as [Hain | Hanotin].
    + asserts Hbth: (binds T a (T[a])).
      { exact (thread_binds_of_indom_read Hain eq_refl). }
      destruct (T[a]) as (((st & e) & d) & c) eqn:HTa.
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
              ** (* spawn: pick a fresh tid; then split on the conflict check *)
                 forwards (t' & Ht'): exists_fresh_tid Hfin.
                 destruct (classic (lin_conflict_free d c g G)) as [Hcfm | Hncfm].
                 --- right. left.
                     forwards (g'' & Hfresh): exists_commit_fresh Hwf.
                     destruct (global_commit a g g''
                         (T[a := (state_running, K t', d, c)][t' := (state_new, te_exp e0, empty, g'')]) G)
                       as [T' G'] eqn:Heq.
                     exists. applys (>> StepSpawn Hbth Hul Ht' Hcfm Hfresh Heq).
                 --- right. right. right.
                     exists a d c. right. exists e K. splits.
                     +++ exact Hbth.
                     +++ left. exists e0. exact Hul.
                     +++ exact Hncfm.
              ** (* join: not blocked => target terminated; then split on the
                    conflict check *)
                 rew_logic in Hnbl. destruct Hnbl as (r0 & d0 & c0 & Hbr).
                 forwards (r1 & Heqr1 & Heqd0): Hterm Hbr. inverts Heqr1. subst d0.
                 destruct (classic (lin_conflict_free d c g G)) as [Hcfm | Hncfm].
                 --- right. left.
                     exists. applys StepJoin Hbth Hul Hbr Hcfm.
                 --- right. right. right.
                     exists a d c. right. exists e K. splits.
                     +++ exact Hbth.
                     +++ right. left. exists t r1 empty_diff c0. split; [exact Hul | exact Hbr].
                     +++ exact Hncfm.
              ** (* read: local (in [d]) or global ([is_latest_value]),
                    otherwise forbidden *)
                 destruct (classic (x \indom d)) as [Hxd | Hxnd].
                 --- right. left. asserts Hbv: (binds d x (d[x])).
                     { applys binds_of_indom_read Hxd. reflexivity. }
                     exists. applys StepReadLocal Hbth Hul Hbv.
                 --- destruct (classic (exists v, is_latest_value G c x v)) as [(v & Hlv) | Hnlv].
                     +++ right. left. exists. applys StepReadGlobal Hbth Hul Hxnd Hlv.
                     +++ right. right. left.
                         exists a e d c K (eff_read x). splits*.
                         simpl. rew_logic. splits*.
              ** (* write *)
                 right. left. exists. applys StepWrite Hbth Hul.
              ** (* lock: not blocked => free; then split on the conflict
                    check *)
                 rew_logic in Hnbl.
                 destruct (classic (lin_conflict_free d c g G)) as [Hcfm | Hncfm].
                 --- right. left. exists. applys StepLock Hbth Hul Hnbl Hcfm.
                 --- right. right. right.
                     exists a d c. right. exists e K. splits.
                     +++ exact Hbth.
                     +++ right. right. left. exists l0. split; [exact Hul | exact Hnbl].
                     +++ exact Hncfm.
              ** (* unlock: enabled (thread holds the lock) fires -- modulo
                    the conflict check -- otherwise forbidden *)
                 destruct (classic (lock_read L l0 = ls_held a)) as [Hheld | Hnheld].
                 --- destruct (classic (lin_conflict_free d c g G)) as [Hcfm | Hncfm].
                     +++ right. left.
                         forwards (g'' & Hfresh): exists_commit_fresh Hwf.
                         destruct (global_commit a g g'' T G) as [T' G'] eqn:Heq.
                         exists. applys (>> StepRelease Hbth Hul Hheld Hcfm Hfresh Heq).
                     +++ right. right. right.
                         exists a d c. right. exists e K. splits.
                         *** exact Hbth.
                         *** right. right. right. exists l0. split; [exact Hul | exact Hheld].
                         *** exact Hncfm.
                 --- right. right. left.
                     exists a e d c K (eff_unlock l0). splits*.
           ++ (* every reduction is blocked: [a] is inert *)
              asserts Hib: (forall K0 a0, step_ul e K0 a0 -> blocked T L a0).
              { introv Hul0. destruct (classic (blocked T L a0)) as [Hb | Hnb]; auto.
                false Hnone. exists K0 a0. auto. }
              left. introv Hmem Hin. rew_listx in Hmem. destruct Hmem as [-> | Hmeml].
              ** right. exists e d c. splits; [ exact Hbth | exact Hex | exact Hib ].
              ** applys Hall Hmeml Hin.
        -- (* returned a value: split on the conflict check, else [StepEnd]
              fires *)
           destruct (classic (lin_conflict_free d c g G)) as [Hcfm | Hncfm].
           ++ right. left.
              forwards (g'' & Hfresh): exists_commit_fresh Hwf.
              destruct (global_commit a g g'' T G) as [T' G'] eqn:Heq.
              exists. applys StepEnd Hbth Hcfm Hfresh Heq.
           ++ right. right. right.
              exists a d c. left. exists r. splits*.
      * (* state_terminated *)
        destruct e as [e | r].
        -- (* terminated but still carrying [te_exp]: impossible by [wf_cfg] *)
           forwards (r0 & Heq0 & Hd0): Hterm Hbth. inverts Heq0.
        -- (* terminated with a return value: this thread is [terminated] *)
           forwards (r0 & Heq0 & Hd0): Hterm Hbth. inverts Heq0. subst d.
           left. introv Hmem Hin. rew_listx in Hmem. destruct Hmem as [-> | Hmeml].
           ++ left. exists r0 c. exact Hbth.
           ++ applys Hall Hmeml Hin.
    + (* [a] is not in the domain, so it contributes nothing *)
      left. introv Hmem Hin. rew_listx in Hmem. destruct Hmem as [-> | Hmeml].
      * false. applys Hanotin Hin.
      * applys Hall Hmeml Hin.
Qed.

Theorem progress :
  forall T G g L,
    ul_progress (T, G, g, L) ->
    wf_cfg (T, G, g, L) ->
    done (T, G, g, L)
    \/ deadlocked (T, G, g, L)
    \/ (exists cfg', step (T, G, g, L) cfg')
    \/ forbidden (T, G, g, L)
    \/ conflict_detected (T, G, g, L).
Proof.
  introv Hulp Hwfc.
  lets (Hfin & _): Hwfc.
  lets (l & Hcov): finite_inv_list_covers Hfin.
  forwards Hres: (progress_aux T G g L l Hulp Hwfc).
  destruct Hres as [Hall | [Hstep | [Hforb | Hconf]]].
  - (* every thread in [dom T] is terminated or inert (via the cover [l]) *)
    asserts Hdi: (forall t, t \indom T ->
                            terminated (T, G, g, L) t \/ inert (T, G, g, L) t).
    { introv Hin. applys* Hall. }
    destruct (classic (exists t, t \indom T /\ inert (T, G, g, L) t)) as [Hi | Hni].
    + (* some thread is inert: deadlocked *)
      right. left. split*.
    + (* no inert thread: every thread is terminated, i.e. done *)
      left. introv Hin. forwards* [Ht | Hinrt]: Hdi Hin.
      false*.
  - right. right. left. exact Hstep.
  - right. right. right. left. exact Hforb.
  - right. right. right. right. exact Hconf.
Qed.
