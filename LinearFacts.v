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
   for [StepSpawn]), the graph is well-formed and totally ordered (acyclic
   and finite -- needed for [exists_commit_fresh] -- and a single chain), a
   global head always exists ([is_global_head] -- the graph is never empty,
   and [total_order] plus [wf_graph] is what lets [total_order_max_commit]
   produce it; every [global_commit] commits *onto* this head, so this is
   the only graph-indom fact [progress] ever needs -- unlike [Branching],
   threads never carry an independent commit that needs its own invariant,
   since every thread's pointer is either the head itself or an old snapshot
   of it, never freshly created), and a terminated thread always carries a
   return value with an empty staging area (it became terminated only via
   [StepEnd]). *)
Definition wf_cfg (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      LibMap.finite T /\
      wf_graph G /\
      total_order G /\
      (exists g, is_global_head G g) /\
      (forall t e d c, binds T t (state_terminated, e, d, c) ->
         exists r, e = te_ret r /\ d = empty)
  end.

(* ===================================================================== *)
(* Progress (modulo deadlock, forbidden effects, and conflicts)          *)
(* ===================================================================== *)

(* An effect is *enabled* for thread [t] (staging diff [d], commit pointer
   [c], global head [g]) when its non-blocking precondition holds. A
   NON-volatile read must be visible either locally (in [d]) or globally (as
   the latest committed value at [c]). A VOLATILE read is never staged in
   [d] ([StepWriteVolatile] always pushes immediately), and it is read at the
   CURRENT global head [g], not at the thread's own (possibly stale) [c] --
   this is the only place [enabled] needs to know [g] at all. An unlock must
   target a lock [t] itself holds (locks carry no commit in this model --
   synchronisation goes entirely through the global head [g], so this is
   exactly [SharedMemory]'s notion). Writes, spawns, joins and locks have no
   such precondition -- whether a join/lock can actually fire is the
   *blocking* question below, and whether *any* synchronising or
   volatile-touching step can fire *without* a conflict is the separate
   [conflict_detected] question. *)
Definition enabled (G : graph) (L : locks) (t : tid) (d : diff) (c g : commit) (a : eff) : Prop :=
  match a with
  | eff_read x   => (x \in Volatiles /\ exists v, is_latest_value G g x v)
                     \/ (x \notin Volatiles /\ (x \indom d \/ exists v, is_latest_value G c x v))
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
   still-computing thread can take a [step_ul] step. *)
Definition ul_progress (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      forall t e d c,
        binds T t (state_running, te_exp e, d, c) ->
        exists K a, step_ul e K a
  end.

(* A thread is *forbidden* from stepping when the underlying language offers
   a reduction to an effect that is not enabled: a read that is visible
   neither locally nor globally (nor, for a volatile, at the current global
   head), or an unlock of a lock the thread does not itself hold. *)
Definition forbidden (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      exists t e d c K a g,
        is_global_head G g /\
        binds T t (state_running, te_exp e, d, c) /\
        step_ul e K a /\
        ~ enabled G L t d c g a
  end.

Definition conflict_detected (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      exists t d c g,
        is_global_head G g /\
        ((exists r,
            binds T t (state_running, te_ret r, d, c) /\
            ~ lin_conflict_free d c g G)
        \/
        (exists e K,
            binds T t (state_running, te_exp e, d, c) /\
            ((exists e', step_ul e K (eff_spawn e') /\
                         ~ lin_conflict_free d c g G) \/
             (exists t' r d' c', step_ul e K (eff_join t') /\
                                  binds T t' (state_terminated, te_ret r, d', c') /\
                                  ~ lin_conflict_free d c g G) \/
             (exists l, step_ul e K (eff_lock l) /\ lock_read L l = ls_free /\
                        ~ lin_conflict_free d c g G) \/
             (exists l, step_ul e K (eff_unlock l) /\ lock_read L l = ls_held t /\
                        ~ lin_conflict_free d c g G) \/
             (exists x, step_ul e K (eff_read x) /\ x \in Volatiles /\
                        ~ lin_conflict_free d c g G) \/
             (exists x v, step_ul e K (eff_write x v) /\ x \in Volatiles /\
                          ~ lin_conflict_free d[x := v] c g G))))
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
      exists e d c,
        binds T t (state_running, te_exp e, d, c) /\
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
   lemmas, with [Linear.inhab_thread] supplied *explicitly*, since typeclass
   search does not reliably resolve a bare [Inhab thread] when the goal is
   stated in unfolded tuple form (as [binds_inj]'s generic statement
   forces). (Locks carry no commit in this model -- [locks := map lid
   lock_state] -- so [lock_state]'s single, canonical [Inhab] instance from
   [Common.v] is unambiguous and needs no such wrapper.) *)
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

Theorem step_preserves_wf_cfg :
  forall cfg cfg',
    wf_cfg cfg ->
    step cfg cfg' ->
    wf_cfg cfg'.
Proof.
  introv Hwfc Hstep. destruct cfg as ((T & G) & L).
  destruct Hwfc as (Hfin & Hwf & Htot & Hhex & Hterm).
  hint LibSet.finite_single.
  hint LibSet.finite_union.
  inverts Hstep.
  - (* StepStart: graph unchanged, [Hhex] carries over as-is *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact Htot.
    + exact Hhex.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepEnd: [is_global_head_commit] gives the new head [g'] at once *)
    match goal with Hb : binds _ _ (state_running, te_ret _, _, _) |- _ => rename Hb into Hbr end.
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hhead0 end.
    match goal with Hf : commit_fresh G _ |- _ => rename Hf into Hfresh0 end.
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    rewrite (global_commit_eq _ _ Hbr) in Hgc.
    inverts Hgc.
    forwards (Htot' & Hhead'): is_global_head_commit Htot Hhead0 Hfresh0.
    splits.
    + unfolds finite. rew_dom. autos.
    + applys graph_commit_wf Hwf Hfresh0 (proj1 Hhead0).
    + exact Htot'.
    + eexists. exact Hhead'.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq. eexists. splits*.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne. applys* Hterm.
  - (* StepReadLocal: graph unchanged *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact Htot.
    + exact Hhex.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepReadGlobal: graph unchanged *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact Htot.
    + exact Hhex.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepReadVolatile: graph unchanged (the pull is a fast-forward, not a
       commit) -- [Hhex] carries over regardless of which head the rule
       itself fast-forwarded to *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact Htot.
    + exact Hhex.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepWrite: graph unchanged *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact Htot.
    + exact Hhex.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepWriteVolatile *)
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hhead0 end.
    match goal with Hf : commit_fresh G _ |- _ => rename Hf into Hfresh0 end.
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    asserts Hbt: (binds (T[t := (state_running, te_exp e, d[x := v], c)]) t
                    (state_running, te_exp e, d[x := v], c)).
    { applys binds_update_same. }
    rewrite (global_commit_eq _ _ Hbt) in Hgc.
    inverts Hgc.
    forwards (Htot' & Hhead'): is_global_head_commit Htot Hhead0 Hfresh0.
    splits.
    + asserts Hfin0:
        (LibSet.finite (dom (T[t := (state_running, te_exp e, d[x := v], c)]))).
      { unfolds finite. rew_dom. autos. }
      unfolds finite. rew_dom. autos.
    + applys graph_commit_wf Hwf Hfresh0 (proj1 Hhead0).
    + exact Htot'.
    + eexists. exact Hhead'.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne.
        forwards Hbinds3: binds_update_neq_inv Hbinds'' Hne. applys* Hterm.
  - (* StepSpawn *)
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hhead0 end.
    match goal with Hf : commit_fresh G _ |- _ => rename Hf into Hfresh0 end.
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    asserts Hneq: (t <> t').
    { introv Heqtt. subst. match goal with H : t' \notindom T |- _ => applys* H end. }
    asserts Hbt: (binds (T[t := (state_running, K t', d, c)][t' := (state_new, te_exp e', empty, g')]) t
                    (state_running, K t', d, c)).
    { applys binds_update_neq; [ | applys binds_update_same ]. auto. }
    rewrite (global_commit_eq _ _ Hbt) in Hgc.
    inverts Hgc.
    forwards (Htot' & Hhead'): is_global_head_commit Htot Hhead0 Hfresh0.
    splits.
    + asserts Hfin0:
        (LibSet.finite (dom (T[t := (state_running, K t', d, c)][t' := (state_new, te_exp e', empty, g')]))).
      { unfolds finite. rew_dom. autos. }
      unfolds finite. rew_dom. autos.
    + applys graph_commit_wf Hwf Hfresh0 (proj1 Hhead0).
    + exact Htot'.
    + eexists. exact Hhead'.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        destruct (classic (t0 = t')) as [->|Hne'].
        -- forwards Heq: binds_update_same_inv Hbinds'. inverts Heq.
        -- forwards Hbinds'': binds_update_neq_inv Hbinds' Hne'.
           forwards Hbinds3: binds_update_neq_inv Hbinds'' Hne. applys* Hterm.
  - (* StepJoin: graph unchanged *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact Htot.
    + exact Hhex.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepLock: graph unchanged *)
    splits.
    + unfolds finite. rew_dom. autos.
    + exact Hwf.
    + exact Htot.
    + exact Hhex.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne. applys* Hterm.
  - (* StepRelease *)
    match goal with Hb : binds _ _ (state_running, te_exp _, _, _) |- _ => rename Hb into Hbr end.
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hhead0 end.
    match goal with Hf : commit_fresh G _ |- _ => rename Hf into Hfresh0 end.
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    rewrite (global_commit_eq _ _ Hbr) in Hgc.
    inverts Hgc.
    forwards (Htot' & Hhead'): is_global_head_commit Htot Hhead0 Hfresh0.
    splits.
    + unfolds finite. rew_dom. autos.
    + applys graph_commit_wf Hwf Hfresh0 (proj1 Hhead0).
    + exact Htot'.
    + eexists. exact Hhead'.
    + introv Hbinds. destruct (classic (t0 = t)) as [->|Hne].
      * forwards Heq: binds_update_same_inv Hbinds. inverts Heq.
      * forwards Hbinds': binds_update_neq_inv Hbinds Hne.
        forwards Hbinds'': binds_update_neq_inv Hbinds' Hne. applys* Hterm.
Qed.

(* ===================================================================== *)
(* Progress (modulo deadlock, forbidden effects, and conflicts)          *)
(* ===================================================================== *)

(* The heart of progress: keep the whole configuration [(T, G, L)] fixed
   and induct over a *list of thread ids* [l]. Either every thread named in
   [l] is terminated-or-inert, or some thread can take a step, or the
   configuration is forbidden, or a synchronising thread's commit
   conflicts. *)
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
  lets (Hfin & Hwf & Htot & (g & Hhead) & Hterm): Hwfc.
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
        right. left. exists. applys StepStart Hbth Hhead.
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
                     exists. applys (>> StepSpawn Hbth Hul Ht' Hhead Hcfm Hfresh Heq).
                 --- right. right. right.
                     exists a d c g. split; [ exact Hhead | ].
                     right. exists e K. split.
                     +++ exact Hbth.
                     +++ left. exists e0. split; [exact Hul | exact Hncfm].
              ** (* join: not blocked => target terminated; then split on the
                    conflict check *)
                 rew_logic in Hnbl. destruct Hnbl as (r0 & d0 & c0 & Hbr).
                 forwards (r1 & Heqr1 & Heqd0): Hterm Hbr. inverts Heqr1. subst d0.
                 destruct (classic (lin_conflict_free d c g G)) as [Hcfm | Hncfm].
                 --- right. left.
                     exists. applys StepJoin Hbth Hul Hbr Hhead Hcfm.
                 --- right. right. right.
                     exists a d c g. split; [ exact Hhead | ].
                     right. exists e K. split.
                     +++ exact Hbth.
                     +++ right. left. exists t r1 empty_diff c0.
                         splits; [exact Hul | exact Hbr | exact Hncfm].
              ** (* read: volatile (a pull, conflict-checked, then read at
                    the global head [g]) or normal (local in [d], or global
                    at [c]); otherwise forbidden / conflict-detected *)
                 destruct (classic (x \in Volatiles)) as [Hxvol | Hxnvol].
                 --- (* volatile: split on conflict-freedom of the pull,
                        then on whether [g] has a latest value *)
                     destruct (classic (lin_conflict_free d c g G)) as [Hcfm | Hncfm].
                     +++ destruct (classic (exists v, is_latest_value G g x v)) as [(v & Hlv) | Hnlv].
                         *** right. left. exists. applys (>> StepReadVolatile Hbth Hul Hxvol Hhead Hcfm Hlv).
                         *** right. right. left.
                             exists a e d c K (eff_read x). exists g. splits*.
                             simpl. rew_logic. splits*.
                     +++ right. right. right.
                         exists a d c g. split; [ exact Hhead | ].
                         right. exists e K. split.
                         *** exact Hbth.
                         *** right; right; right; right; left. exists x.
                             splits; [exact Hul | exact Hxvol | exact Hncfm].
                 --- (* normal: local (in [d]) or global ([is_latest_value]
                        at [c]), otherwise forbidden *)
                     destruct (classic (x \indom d)) as [Hxd | Hxnd].
                     +++ right. left. asserts Hbv: (binds d x (d[x])).
                         { applys binds_of_indom_read Hxd. reflexivity. }
                         exists. applys StepReadLocal Hbth Hul Hxnvol Hbv.
                     +++ destruct (classic (exists v, is_latest_value G c x v)) as [(v & Hlv) | Hnlv].
                         *** right. left. exists. applys StepReadGlobal Hbth Hul Hxnvol Hxnd Hlv.
                         *** right. right. left.
                             exists a e d c K (eff_read x). exists g. splits*.
                             simpl. rew_logic. splits*.
              ** (* write: volatile (a pull-then-push, conflict-checked) or
                    normal (always succeeds, staged into [d]) *)
                 destruct (classic (x \in Volatiles)) as [Hxvol | Hxnvol].
                 --- (* volatile: split on the conflict check, which now covers
                        [x] itself (folded into the diff) too, catching an
                        unordered write-write race on the volatile as a
                        conflict rather than silently overwriting it. *)
                     destruct (classic (lin_conflict_free d[x := v] c g G)) as [Hcfm | Hncfm].
                     +++ right. left.
                         forwards (g'' & Hfresh): exists_commit_fresh Hwf.
                         destruct (global_commit a g g''
                             (T[a := (state_running, te_exp e, d[x := v], c)]) G)
                           as [T' G'] eqn:Heq.
                         exists. applys (>> StepWriteVolatile Hbth Hul Hxvol Hhead Hcfm Hfresh Heq).
                     +++ right. right. right.
                         exists a d c g. split; [ exact Hhead | ].
                         right. exists e K. split.
                         *** exact Hbth.
                         *** right; right; right; right; right. exists x v.
                             splits; [exact Hul | exact Hxvol | exact Hncfm].
                 --- right. left. exists. applys StepWrite Hbth Hul Hxnvol.
              ** (* lock: not blocked => free; then split on the conflict
                    check *)
                 rew_logic in Hnbl.
                 destruct (classic (lin_conflict_free d c g G)) as [Hcfm | Hncfm].
                 --- right. left. exists. applys StepLock Hbth Hul Hnbl Hhead Hcfm.
                 --- right. right. right.
                     exists a d c g. split; [ exact Hhead | ].
                     right. exists e K. split.
                     +++ exact Hbth.
                     +++ right. right. left. exists l0. splits; [exact Hul | exact Hnbl | exact Hncfm].
              ** (* unlock: enabled (thread holds the lock) fires -- modulo
                    the conflict check -- otherwise forbidden *)
                 destruct (classic (lock_read L l0 = ls_held a)) as [Hheld | Hnheld].
                 --- destruct (classic (lin_conflict_free d c g G)) as [Hcfm | Hncfm].
                     +++ right. left.
                         forwards (g'' & Hfresh): exists_commit_fresh Hwf.
                         destruct (global_commit a g g'' T G) as [T' G'] eqn:Heq.
                         exists. applys (>> StepRelease Hbth Hul Hheld Hhead Hcfm Hfresh Heq).
                     +++ right. right. right.
                         exists a d c g. split; [ exact Hhead | ].
                         right. exists e K. split.
                         *** exact Hbth.
                         *** right. right. right. left. exists l0.
                             splits; [exact Hul | exact Hheld | exact Hncfm].
                 --- right. right. left.
                     exists a e d c K (eff_unlock l0). exists g. splits*.
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
              exists. applys StepEnd Hbth Hhead Hcfm Hfresh Heq.
           ++ right. right. right.
              exists a d c g. split; [ exact Hhead | ].
              left. exists r. splits*.
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
