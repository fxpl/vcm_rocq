From Vcm Require Import Common.
From Vcm Require Import SharedMemory.

Import SharedMemory.

(* ===================================================================== *)
(* Progress (modulo deadlock)                                            *)
(* ===================================================================== *)

(* An effect is *enabled* in the current heap [H] / locks [L] for thread [t]
   when its non-blocking precondition holds: a read must target an allocated
   variable and an unlock a lock the thread holds. Writes, spawns, joins and
   locks have no such precondition (for a join/lock, whether it can actually
   fire is the *blocking* question below). An effect that is not enabled is
   the other (non-deadlock) way a thread can get stuck: reading an
   unallocated variable, or unlocking a lock it does not hold -- see
   [forbidden] below. *)
Definition enabled (H : heap) (L : locks) (t : tid) (a : eff) : Prop :=
  match a with
  | eff_read x   => x \indom H
  | eff_unlock l => lock_read L l = ls_held t
  | _ => True
  end.

(* A *blocking* effect: joining a thread that has not terminated, or acquiring a
   lock that is currently held. These are the legitimate sources of deadlock
   (locks default to free, so there is no "never acquired" case). *)
Definition blocked (T : threads) (L : locks) (a : eff) : Prop :=
  match a with
  | eff_join t'  => ~ exists r, binds T t' (state_terminated, te_ret r)
  | eff_lock l   => lock_read L l <> ls_free
  | _ => False
  end.

(* Progress for the underlying sequential language: every running,
   still-computing thread can take a [step_ul] step. *)
Definition ul_progress (cfg : cfg) : Prop :=
  match cfg with
  | (T, H, L) =>
      forall t e,
        binds T t (state_running, te_exp e) ->
        exists K a, step_ul e K a
  end.

(* A thread is *forbidden* from stepping when the underlying language offers
   a reduction to an effect that is not enabled: a read of a variable that is
   not (yet) allocated, or an unlock of a lock the thread does not itself
   hold. *)
Definition forbidden (cfg : cfg) : Prop :=
  match cfg with
  | (T, H, L) =>
      exists t e K a,
        binds T t (state_running, te_exp e) /\
        step_ul e K a /\
        ~ enabled H L t a
  end.

(* A thread has terminated. *)
Definition terminated (cfg : cfg) (t : tid) : Prop :=
  match cfg with
  | (T, _, _) => exists r, binds T t (state_terminated, te_ret r)
  end.

(* A running thread is *inert* when it is still computing, can take a step, but
   every step it can take is blocked (a join on a non-terminated thread, or a
   lock on a held lock). *)
Definition inert (cfg : cfg) (t : tid) : Prop :=
  match cfg with
  | (T, _, L) =>
      exists e,
        binds T t (state_running, te_exp e) /\
        (exists K a, step_ul e K a) /\
        (forall K a, step_ul e K a -> blocked T L a)
  end.

(* Well-formedness: a terminated thread always carries a return value (it became
   terminated only via [StepEnd], whose continuation handed one back). This rules
   out the otherwise-stuck [(state_terminated, te_exp _)] thread in progress. *)
Definition wf_cfg (cfg : cfg) : Prop :=
  match cfg with
  | (T, _, _) => LibMap.finite T /\ forall t e, binds T t (state_terminated, e) -> exists r, e = te_ret r
  end.

(* The configuration is *done* when every thread has terminated. *)
Definition done (cfg : cfg) : Prop :=
  match cfg with
  | (T, _, _) => forall t, t \indom T -> terminated cfg t
  end.

(* The configuration is *deadlocked* when every thread is terminated or inert,
   and at least one thread is inert (so [deadlocked] is disjoint from [done]). *)
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

(* A finite thread domain stays finite under a step: every rule either updates
   an existing thread in place (domain unchanged) or spawns exactly one new
   thread (adds a single element). *)
Lemma step_preserves_finite :
  forall T H L cfg',
    LibSet.finite (dom T) ->
    step (T, H, L) cfg' ->
    match cfg' with (T', _, _) => LibSet.finite (dom T') end.
Proof.
  introv Hfin Hstep.
  hint LibSet.finite_single.
  hint LibSet.finite_union.
  inverts Hstep; rew_dom; autos.
Qed.

(* [wf_cfg] is preserved by [step]: the only rule that produces a terminated
   thread is [StepEnd], which gives it a [te_ret]; every other rule leaves a
   thread running or new, and untouched threads are covered by the hypothesis. *)
Theorem step_preserves_wf_cfg :
  forall cfg cfg',
    wf_cfg cfg ->
    step cfg cfg' ->
    wf_cfg cfg'.
Proof.
  introv Hwf Hstep.
  destruct cfg as ((T & H) & L).
  forwards: step_preserves_finite Hstep; [inverts~ Hwf|].
  inverts Hstep; simpl in *; splits*; introv Hb;
    forwards* [(-> & Heq) | (_ & Hb')]: binds_update_inv' Hb.
  - (* StepEnd *)
    inverts* Heq.
  - (* StepSpawn: second update update *)
    forwards* [(-> & Heq) | (_ & Hb2)]: binds_update_inv' Hb'.
Qed.

(* A fresh thread id always exists, since the domain is a finite set of [nat]s.
   (Used to discharge the freshness side-condition of [StepSpawn] in progress.) *)
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

(* Progress, modulo deadlock and forbidden effects.

   Assuming (i) the thread domain is finite and (ii) progress for the underlying
   sequential language, every configuration is in exactly one of four
   situations: it is [done] (all threads have terminated), it is [deadlocked]
   (every thread is terminated or inert, and at least one is inert), it can
   take one more [step], or it is [forbidden] (some thread's next [step_ul] is
   to a disabled effect: a read of an unallocated variable, or an unlock of a
   lock it does not hold).
*)
#[local] Instance inhab_sm_thread : Inhab thread.
Proof. apply (Inhab_of_val (state_new, te_ret ret_race)). Qed.

(* The heart of progress: keep the whole map [T] (and [H], [L]) fixed and induct
   over a *list of thread ids* [l]. The induction hypothesis is then about the
   same whole configuration, restricted to the threads named in [l] -- so
   [step]/[terminated]/[inert]/[forbidden] always range over all of [T]. Either
   every thread named in [l] is terminated-or-inert, or some thread can take a
   step, or the configuration is forbidden. *)
Lemma progress_aux :
  forall T H L (l : list tid),
    ul_progress (T, H, L) ->
    wf_cfg (T, H, L) ->
    (forall t, mem t l -> t \indom T ->
       terminated (T, H, L) t \/ inert (T, H, L) t)
    \/ (exists cfg', step (T, H, L) cfg')
    \/ forbidden (T, H, L).
Proof.
  introv Hulp Hwfc.
  lets (Hfin & Hterm): Hwfc.
  induction l as [| a l IH].
  - left. introv Hmem. inverts Hmem.
  - destruct IH as [Hall | [Hstep | Hforb]];
      [| right; left; exact Hstep | right; right; exact Hforb].
    destruct (classic (a \indom T)) as [Hain | Hanotin].
    + asserts Hbth: (binds T a (T[a])).
      { applys binds_of_indom_read Hain. reflexivity. }
      destruct (T[a]) as (st & e).
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
           ++ (* a non-blocked reduction is offered; it fires if enabled,
                 otherwise the configuration is forbidden *)
              destruct a0; unfold enabled, blocked in *.
              ** (* spawn: pick a fresh tid *)
                 right. left. forwards (t' & Ht'): exists_fresh_tid Hfin.
                 exists. applys StepSpawn Hbth Hul Ht'.
              ** (* join: not blocked => target terminated *)
                 right. left. rew_logic in Hnbl. destruct Hnbl as (r & Hr).
                 exists. applys StepJoin Hbth Hul Hr.
              ** (* read: allocated fires, otherwise forbidden *)
                 destruct (classic (x \indom H)) as [Hxin | Hxnotin].
                 --- right. left. asserts Hbv: (binds H x (H[x])).
                     { applys binds_of_indom_read Hxin. reflexivity. }
                     exists. applys StepRead Hbth Hul Hbv.
                 --- right. right. exists a e K (eff_read x). splits*.
              ** (* write *)
                 right. left. exists. applys StepWrite Hbth Hul.
              ** (* lock: not blocked => free or never-acquired *)
                 right. left. rew_logic in Hnbl. exists. applys StepLock Hbth Hul Hnbl.
              ** (* unlock: held fires, otherwise forbidden *)
                 destruct (classic (lock_read L l0 = ls_held a)) as [Hheld | Hnheld].
                 --- right. left. exists. applys StepRelease Hbth Hul Hheld.
                 --- right. right. exists a e K (eff_unlock l0). splits*.
           ++ (* every reduction is blocked: [a] is inert *)
              asserts Hib: (forall K0 a0, step_ul e K0 a0 -> blocked T L a0).
              { introv Hul0. destruct (classic (blocked T L a0)) as [Hb | Hnb]; auto.
                false Hnone. exists K0 a0. auto. }
              left. introv Hmem Hin. rew_listx in Hmem. destruct Hmem as [-> | Hmeml].
              ** right. exists e. splits; [ exact Hbth | exact Hex | exact Hib ].
              ** applys Hall Hmeml Hin.
        -- (* returned a value: StepEnd fires *)
           right. left. exists. applys StepEnd Hbth.
      * (* state_terminated *)
        destruct e as [e | r].
        -- (* terminated but still carrying [te_exp]: impossible by [wf_cfg] *)
           forwards (r & Hr): Hterm Hbth. inverts Hr.
        -- (* terminated with a return value: this thread is [terminated] *)
           left. introv Hmem Hin. rew_listx in Hmem. destruct Hmem as [-> | Hmeml].
           ++ left. exists r. exact Hbth.
           ++ applys Hall Hmeml Hin.
    + (* [a] is not in the domain, so it contributes nothing *)
      left. introv Hmem Hin. rew_listx in Hmem. destruct Hmem as [-> | Hmeml].
      * false. applys Hanotin Hin.
      * applys Hall Hmeml Hin.
Qed.

Theorem progress :
  forall T H L,
    ul_progress (T, H, L) ->
    wf_cfg (T, H, L) ->
    done (T, H, L)
    \/ deadlocked (T, H, L)
    \/ (exists cfg', step (T, H, L) cfg')
    \/ forbidden (T, H, L).
Proof.
  introv Hulp Hwfc.
  lets (Hfin & Hterm): Hwfc.
  lets (l & Hcov): finite_inv_list_covers Hfin.
  forwards Hres: (progress_aux T H L l Hulp Hwfc).
  destruct Hres as [Hall | [Hstep | Hforb]].
  - (* every thread in [dom T] is terminated or inert (via the cover [l]) *)
    asserts Hdi: (forall t, t \indom T ->
                            terminated (T, H, L) t \/ inert (T, H, L) t).
    { introv Hin. applys* Hall. }
    destruct (classic (exists t, t \indom T /\ inert (T, H, L) t)) as [Hi | Hni].
    + (* some thread is inert: deadlocked *)
      right. left. split*.
    + (* no inert thread: every thread is terminated, i.e. done *)
      left. introv Hin. forwards* [Ht | Hinrt]: Hdi Hin.
      false*.
  - right. right. left. exact Hstep.
  - right. right. right. exact Hforb.
Qed.
