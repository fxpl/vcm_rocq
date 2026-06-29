From Vcm Require Import Common.
From Vcm Require Import SharedMemory.

Import SharedMemory.

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

(* Progress, modulo deadlock.

   Assuming (i) the thread domain is finite and (ii) progress for the underlying
   sequential language (with effect-enabledness folded in), every configuration
   is in exactly one of three situations: it is [done] (all threads have
   terminated), it is [deadlocked] (every thread is terminated or inert, and at
   least one is inert), or it can take one more [step].

   Proof sketch (by induction over the -- finite -- thread domain):
     - [state_new] threads can always [StepStart].
     - running [te_ret r] threads can always [StepEnd].
     - running [te_exp e] threads can [step_ul] (premise) to an enabled effect;
       reads/writes/spawns/unlocks then fire (reads hit [dom H], unlocks hold
       the lock, spawns use [exists_fresh_tid]); joins/locks fire unless blocked,
       in which case -- if *every* reduction is blocked -- the thread is inert.
     - [state_terminated] threads contribute to [done].
   If no thread can step, then there are no [new] threads and no running
   [te_ret] threads, every running [te_exp] thread is inert, hence the
   configuration is [done] (no inert threads) or [deadlocked] (some inert). *)
(* [thread] is inhabited, so we can read a binding out of a domain membership. *)
#[local] Instance inhab_sm_thread : Inhab thread.
Proof. apply (Inhab_of_val (state_new, te_ret ret_race)). Qed.

(* The heart of progress: keep the whole map [T] (and [H], [L]) fixed and induct
   over a *list of thread ids* [l]. The induction hypothesis is then about the
   same whole configuration, restricted to the threads named in [l] -- so
   [step]/[terminated]/[inert] always range over all of [T]. Either every thread
   named in [l] is terminated-or-inert, or some thread can take a step. *)
Lemma progress_aux :
  forall T H L (l : list tid),
    finite T ->
    ul_progress (T, H, L) ->
    wf_cfg (T, H, L) ->
    (forall t, mem t l -> t \indom T ->
       terminated (T, H, L) t \/ inert (T, H, L) t)
    \/ (exists cfg', step (T, H, L) cfg').
Proof.
  introv Hfin Hulp Hwfc. induction l as [| a l IH].
  - left. introv Hmem. inverts Hmem.
  - destruct IH as [Hall | Hstep]; [| right; exact Hstep].
    destruct (classic (a \indom T)) as [Hain | Hanotin].
    + asserts Hbth: (binds T a (T[a])).
      { applys binds_of_indom_read Hain. reflexivity. }
      destruct (T[a]) as (st & e).
      destruct st.
      * (* state_new: StepStart always fires *)
        right. exists. applys StepStart Hbth.
      * (* state_running *)
        destruct e as [e | r].
        -- (* still computing: use [ul_progress], split on whether some
              reduction is non-blocked *)
           forwards (Hex & Henab): Hulp Hbth.
           destruct (classic (exists K a0, step_ul e K a0 /\ ~ blocked T L a0))
             as [(K & a0 & Hul & Hnbl) | Hnone].
           ++ (* a non-blocked, hence enabled, reduction fires *)
              forwards Henab': Henab Hul.
              right. destruct a0; unfold enabled, blocked in *.
              ** (* spawn: pick a fresh tid *)
                 forwards (t' & Ht'): exists_fresh_tid Hfin.
                 exists. applys StepSpawn Hbth Hul Ht'.
              ** (* join: not blocked => target terminated *)
                 rew_logic in Hnbl. destruct Hnbl as (r & Hr).
                 exists. applys StepJoin Hbth Hul Hr.
              ** (* read: enabled => target var allocated *)
                 asserts Hbv: (binds H x (H[x])).
                 { applys binds_of_indom_read Henab'. reflexivity. }
                 exists. applys StepRead Hbth Hul Hbv.
              ** (* write *)
                 exists. applys StepWrite Hbth Hul.
              ** (* lock: not blocked => free or never-acquired *)
                 rew_logic in Hnbl. exists. applys StepLock Hbth Hul Hnbl.
              ** (* unlock: enabled => thread holds the lock *)
                 exists. applys StepRelease Hbth Hul Henab'.
           ++ (* every reduction is blocked: [a] is inert *)
              asserts Hib: (forall K0 a0, step_ul e K0 a0 -> blocked T L a0).
              { introv Hul0. destruct (classic (blocked T L a0)) as [Hb | Hnb]; auto.
                false Hnone. exists K0 a0. auto. }
              left. introv Hmem Hin. rew_listx in Hmem. destruct Hmem as [-> | Hmeml].
              ** right. exists e. splits; [ exact Hbth | exact Hex | exact Hib ].
              ** applys Hall Hmeml Hin.
        -- (* returned a value: StepEnd fires *)
           right. exists. applys StepEnd Hbth.
      * (* state_terminated *)
        destruct e as [e | r].
        -- (* terminated but still carrying [te_exp]: impossible by [wf_cfg] *)
           forwards (r & Hr): Hwfc Hbth. inverts Hr.
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
    finite T ->
    ul_progress (T, H, L) ->
    wf_cfg (T, H, L) ->
    done (T, H, L)
    \/ deadlocked (T, H, L)
    \/ (exists cfg', step (T, H, L) cfg').
Proof.
  introv Hfin Hulp Hwfc.
  lets (l & Hcov): finite_inv_list_covers Hfin.
  forwards~ [Hall | Hstep]: (progress_aux T H L l Hfin Hulp Hwfc).
  (* every thread in [dom T] is terminated or inert (via the cover [l]) *)
  asserts Hdi: (forall t, t \indom T ->
                          terminated (T, H, L) t \/ inert (T, H, L) t).
  { introv Hin. applys* Hall. }
  destruct (classic (exists t, t \indom T /\ inert (T, H, L) t)) as [Hi | Hni].
  - (* some thread is inert: deadlocked *)
    right. left. split*.
  - (* no inert thread: every thread is terminated, i.e. done *)
    left. introv Hin. forwards* [Ht | Hinrt]: Hdi Hin.
    false*.
Qed.

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

(* [wf_cfg] is preserved by [step]: the only rule that produces a terminated
   thread is [StepEnd], which gives it a [te_ret]; every other rule leaves a
   thread running or new, and untouched threads are covered by the hypothesis. *)
Lemma step_preserves_wf_cfg :
  forall cfg cfg',
    wf_cfg cfg ->
    step cfg cfg' ->
    wf_cfg cfg'.
Proof.
  introv Hwf Hstep.
  inverts Hstep; simpl in *; introv Hb;
    forwards* [(-> & Heq) | (_ & Hb')]: binds_update_inv' Hb.
  - (* StepEnd *)
    inverts* Heq.
  - (* StepSpawn: second update update *)
    forwards* [(-> & Heq) | (_ & Hb2)]: binds_update_inv' Hb'.
Qed.
