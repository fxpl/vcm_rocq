From Vcm Require Import Common.
From Vcm Require Import Log.

(* Appending an event to a log that already starts with the root start keeps it
   starting with the root start.  The [mem] hypothesis only serves to show the
   log is non-empty. *)
Lemma wf_log_init_head_snoc : forall lg e t0,
    (lg <> nil -> exists l, lg = event_start t_root :: l) ->
    mem (event_start t0) lg ->
    exists l, lg & e = event_start t_root :: l.
Proof.
  introv Hhead Hmem.
  forwards (l & Hlg): Hhead. { intro Hc. subst lg. forwards*: mem_nil_inv Hmem. }
  exists (l & e). rewrite Hlg. rew_list~.
Qed.

(* The root start event is present in any non-empty well-formed log. *)
Lemma wf_log_nonempty_init :
  forall log, wf_log log -> log <> nil -> mem (event_start t_root) log.
Proof.
  introv Hwf Hne. destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hhead & _).
  forwards (l & ->): Hhead Hne. rew_listx~.
Qed.

Lemma wf_log_read_last :
  forall lg t i v,
    mem (event_start t) lg ->
    ~mem (event_end t) lg ->
    wf_log lg ->
    wf_log (lg & event_read t i v).
Proof.
  introv Hstart Hend Hwf.
  lets (Hspawns & Hstarts & Hspawn & Hjoin & Hstart' & Hend' & Hlock & _ & Hrootsp): Hwf.
  splits 9.
  - introv Heq (t1' & Hmem).
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
    + replaces (l1 ++ event_spawn t1 t2 :: l2' & e)
          with ((l1 ++ event_spawn t1 t2 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
      apply Hspawns in Heq'.
      apply Heq'. exists t1'.
      rew_listx in Hmem.
      rew_listx.
      branches; auto_star.
  - introv Heq Hmem.
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
    + replaces (l1 ++ event_start t0 :: l2' & e)
          with ((l1 ++ event_start t0 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
      apply Hstarts in Heq'.
      apply Heq'.
      rew_listx in Hmem.
      rew_listx.
      branches; auto_star.
  - introv Heq.
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
    + replaces (l1 ++ event_start t2 :: l2' & e)
          with ((l1 ++ event_start t2 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
  - introv Heq.
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
    + replaces (l1 ++ event_join t1 t2 :: l2' & e)
          with ((l1 ++ event_join t1 t2 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
  - introv Heq Hthread Hneq.
    destruct (last_case l2) as [-> | (e' & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
      unpack. subst. simpls*.
    + replaces (l1 ++ e :: l2' & e')
          with ((l1 ++ e :: l2') & e')
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
  - introv Heq.
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + rew_listx*.
    + replaces (l1 ++ event_end t0 :: l2' & e)
          with ((l1 ++ event_end t0 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
      rew_listx. splits*.
      asserts Hmem': (mem (event_end t0) lg).
      { subst. rew_listx*. }
      asserts* Hneq: (t <> t0).
      simpls*.
  - (* locks *) introv. rew_listx. cases_if*. rew_list*.
  - (* init *) intros _.
    lets (_ & _ & _ & _ & _ & _ & _ & Hinit & _): Hwf.
    applys wf_log_init_head_snoc Hinit Hstart.
  - (* root never spawned *) intros t1 Hmem. rew_listx in Hmem.
    destruct Hmem as [Hmem | Hmem]; (applys Hrootsp Hmem || inverts Hmem).
Qed.

Lemma wf_lock_log_snoc_lock : forall xs t l,
    wf_lock_log xs ->
    (xs = nil \/ exists t' xs', xs = xs' & event_unlock t' l) ->
    wf_lock_log (xs & event_lock t l).
Proof.
  introv Hwf Hfree. induction Hwf.
  - rew_list. apply WfLockSingle.
  - destruct Hfree as [|( t' & xs' & Heq)]; [congruence|].
    destruct xs' as [| x [| y xs']]; rew_list in Heq; inverts Heq; congruence.
  - rew_list. apply WfLockUnlock.
    apply IHHwf.
    destruct Hfree as [Hnil | (t' & xs' & Heq)]; [congruence|].
    destruct (last_case log) as [-> | (x & log'' & ->)]; autos.
    replaces (event_lock t1 l0 :: event_unlock t1 l0 :: log'' & x)
        with ((event_lock t1 l0 :: event_unlock t1 l0 :: log'') & x)
          in Heq.
    { rew_list~. }
    apply last_eq_last_inv in Heq as [_ ->].
    right. exists t' log''. rew_list~.
Qed.

(* The last entry of a lock's touch-filter is a lock or unlock of that lock. *)
Lemma filter_touches_lock_last_inv : forall l lg xs' x,
    LibList.filter (fun e => touches_lock l e) lg = xs' & x ->
    (exists t', x = event_lock t' l) \/ (exists t', x = event_unlock t' l).
Proof.
  introv Heq.
  asserts Hmem: (mem x (LibList.filter (fun e => touches_lock l e) lg)).
  { rewrite Heq. apply mem_last_r. }
  forwards (_ & Htl): mem_filter_inv Hmem.
  destruct x; simpls; try contradiction.
  - left. exists t. congruence.
  - right. exists t. congruence.
Qed.

(* Appending a lock event to a well-formed log keeps it well formed, given the
   acquiring thread is running and the lock's touch-filter is empty or ends in an
   unlock.  Both lock step rules (free and never-touched) produce the same log. *)
Lemma wf_log_snoc_lock : forall lg t l,
    wf_log lg ->
    mem (event_start t) lg ->
    ~ mem (event_end t) lg ->
    (LibList.filter (fun e => touches_lock l e) lg = nil \/
     exists t'' lg'', LibList.filter (fun e => touches_lock l e) lg = lg'' & event_unlock t'' l) ->
    wf_log (lg & event_lock t l).
Proof.
  introv Hwf Hsmem Hlnmem Hlfree.
  lets (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & _ & Hrootsp): Hwf.
  splits 9.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
    rew_listx. rew_listx in Hmem'. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros contra. apply~ (Hustart l1 l2' t0).
    rew_listx. rew_listx in contra. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hspawn.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hjoin.
  + introv Heq <- Hneq.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. simpl. exact Hsmem.
    * apply~ Hstart.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    rew_listx. splits.
    * apply~ Hend.
    * simpl. intros ->. apply Hlnmem. rew_listx*.
  + (* locks *) introv. rew_listx.
    cases_if as Heql.
    * unfold touches_lock in Heql. subst. rew_list.
      apply wf_lock_log_snoc_lock.
      { apply~ Hlock. }
      { destruct Hlfree as [Hnil | (t'' & lg'' & Hfilt)].
        - left. exact Hnil.
        - right. exists t'' lg''. exact Hfilt. }
    * rew_list. apply~ Hlock.
  + (* init *) intros _.
    lets (_ & _ & _ & _ & _ & _ & _ & Hinit & _): Hwf.
    applys wf_log_init_head_snoc Hinit Hsmem.
  + (* root never spawned *) intros t1 Hmem. rew_listx in Hmem.
    destruct Hmem as [Hmem | Hmem]; (applys Hrootsp Hmem || inverts Hmem).
Qed.

Lemma wf_lock_log_snoc_unlock : forall xs xs' t l,
    wf_lock_log (LibList.filter (fun e : event => touches_lock l e) xs) ->
    LibList.filter (fun e : event => touches_lock l e) xs = xs' & event_lock t l ->
    wf_lock_log (LibList.filter (fun e : event => touches_lock l e) xs & event_unlock t l).
Proof.
  introv Hwf Heq. gen xs'. induction Hwf; intros.
  - destruct xs'; rew_listx in Heq; congruence.
  - destruct xs' as [| x [| y xs']]; rew_list in Heq; inverts Heq; try congruence.
    rew_list. apply WfLockUnlock. apply WfLockEmpty.
  - rew_list. apply WfLockUnlock.
    destruct (last_case log) as [-> | (y & log'' & ->)].
    + replaces (event_lock t1 l0 :: event_unlock t1 l0 :: nil)
          with ((event_lock t1 l0 :: nil) & event_unlock t1 l0) in Heq.
      { rew_list~. }
      apply last_eq_last_inv in Heq as [_ Hcontra]. congruence.
    + replaces (event_lock t1 l0 :: event_unlock t1 l0 :: log'' & y)
          with ((event_lock t1 l0 :: event_unlock t1 l0 :: log'') & y) in Heq.
      { rew_list~. }
      apply last_eq_last_inv in Heq as [_ ->].
      apply (IHHwf log''). rew_list~.
Qed.

(* The [wf_log_*_last] family below records, once and for all, what each kind of
   event requires of the existing log in order to preserve well-formedness when
   appended. Together with [wf_log_read_last] and [wf_log_snoc_lock] above they
   cover every event a step can emit, so the per-model [step_preserves_wf_log]
   proofs collapse to a single application each. The recurring shape is: most of
   the nine [wf_log] conjuncts are preserved by *any* event that is not of the
   kind they constrain (decided by [last_eq_middle_inv] on the appended event),
   and only the conjunct matching the event's own kind needs real work. *)

(* Appending a write by a running thread preserves well-formedness; a write is
   not a spawn/start/join/end and touches no lock, so every conjunct is generic. *)
Lemma wf_log_write_last : forall lg t x v,
    wf_log lg ->
    mem (event_start t) lg ->
    ~ mem (event_end t) lg ->
    wf_log (lg & event_write t x v).
Proof.
  introv Hwf Hsmem Hnmem.
  lets (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & _ & Hroot): Hwf.
  splits 9.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
    rew_listx. rew_listx in Hmem'. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros contra. apply~ (Hustart l1 l2' t0).
    rew_listx. rew_listx in contra. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hspawn.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hjoin.
  + introv Heq <- Hneq.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. simpl. exact Hsmem.
    * apply~ Hstart.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    rew_listx. splits.
    * apply~ Hend.
    * simpl. intros ->. apply Hnmem. rew_listx*.
  + introv. rew_listx.
    cases_if~. rew_list~.
  + intros _.
    lets (_ & _ & _ & _ & _ & _ & _ & Hinit & _): Hwf.
    applys wf_log_init_head_snoc Hinit Hsmem.
  + introv Hmem'.
    rew_listx in Hmem'. branches; auto_star.
Qed.

(* Appending an end by a running thread: only the "no events after end" conjunct
   does real work, recording that the ending thread had not already ended. *)
Lemma wf_log_end_last : forall lg t,
    wf_log lg ->
    mem (event_start t) lg ->
    ~ mem (event_end t) lg ->
    wf_log (lg & event_end t).
Proof.
  introv Hwf Hsmem Hnmem.
  lets (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & _ & Hroot): Hwf.
  splits 9.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
    rew_listx. rew_listx in Hmem'. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros contra. apply~ (Hustart l1 l2' t0).
    rew_listx. rew_listx in contra. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hspawn.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hjoin.
  + introv Heq <- Hneq.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. simpl. exact Hsmem.
    * apply~ Hstart.
  + introv Heq.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. rew_listx~.
    * rew_listx. splits.
      -- apply~ Hend.
      -- simpl. intros ->. apply Hnmem. rew_listx*.
  + introv. rew_listx.
    cases_if~. rew_list~.
  + intros _.
    lets (_ & _ & _ & _ & _ & _ & _ & Hinit & _): Hwf.
    applys wf_log_init_head_snoc Hinit Hsmem.
  + introv Hmem'.
    rew_listx in Hmem'. branches; auto_star.
Qed.

(* Appending a spawn of a *fresh* thread [t2] (no prior spawn targets it and it
   is not the root): the "unique spawns" and "root never spawned" conjuncts do
   the work. *)
Lemma wf_log_spawn_last : forall lg t1 t2,
    wf_log lg ->
    mem (event_start t1) lg ->
    ~ mem (event_end t1) lg ->
    (~ exists t0, mem (event_spawn t0 t2) lg) ->
    t2 <> t_root ->
    wf_log (lg & event_spawn t1 t2).
Proof.
  introv Hwf Hsmem Hnmem Hnospawn Htneq.
  lets (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & _ & Hroot): Hwf.
  splits 9.
  + introv Heq.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. rew_listx~.
    * intros (t1' & Hmem''). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem''.
      branches; autos.
      match goal with H : event_spawn _ _ = event_spawn _ _ |- _ => inverts H end.
      false Hnospawn. exists t0. rew_listx~.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros contra. apply~ (Hustart l1 l2' t).
    rew_listx. rew_listx in contra. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hspawn.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hjoin.
  + introv Heq <- Hneq.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. simpl. exact Hsmem.
    * apply~ Hstart.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    rew_listx. splits.
    * apply~ Hend.
    * simpl. intros ->. apply Hnmem. rew_listx*.
  + introv. rew_listx.
    cases_if~. rew_list~.
  + intros _.
    lets (_ & _ & _ & _ & _ & _ & _ & Hinit & _): Hwf.
    applys wf_log_init_head_snoc Hinit Hsmem.
  + introv Hmem'.
    rew_listx in Hmem'.
    destruct Hmem' as [Hmem' | Heq]; [ applys Hroot Hmem' | inverts Heq; congruence ].
Qed.

(* Appending a join by a running thread of an *ended* thread [t2]: only the
   "join after end" conjunct does work, witnessed by [t2] having ended. *)
Lemma wf_log_join_last : forall lg t1 t2,
    wf_log lg ->
    mem (event_start t1) lg ->
    ~ mem (event_end t1) lg ->
    mem (event_end t2) lg ->
    wf_log (lg & event_join t1 t2).
Proof.
  introv Hwf Hsmem Hnmem Htended.
  lets (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & _ & Hroot): Hwf.
  splits 9.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
    rew_listx. rew_listx in Hmem'. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros contra. apply~ (Hustart l1 l2' t).
    rew_listx. rew_listx in contra. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hspawn.
  + introv Heq.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. rew_listx~.
    * apply* Hjoin.
  + introv Heq <- Hneq.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. simpl. exact Hsmem.
    * apply~ Hstart.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    rew_listx. splits.
    * apply~ Hend.
    * simpl. intros ->. apply Hnmem. rew_listx*.
  + introv. rew_listx.
    cases_if~. rew_list~.
  + intros _.
    lets (_ & _ & _ & _ & _ & _ & _ & Hinit & _): Hwf.
    applys wf_log_init_head_snoc Hinit Hsmem.
  + introv Hmem'.
    rew_listx in Hmem'. branches; auto_star.
Qed.

(* Appending an unlock by a running thread whose lock's touch-filter currently
   ends in a matching lock: only the lock conjunct does work. *)
Lemma wf_log_unlock_last : forall lg t l lg'',
    wf_log lg ->
    mem (event_start t) lg ->
    ~ mem (event_end t) lg ->
    LibList.filter (fun e => touches_lock l e) lg = lg'' & event_lock t l ->
    wf_log (lg & event_unlock t l).
Proof.
  introv Hwf Hsmem Hnmem Hlheld.
  lets (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & _ & Hroot): Hwf.
  splits 9.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
    rew_listx. rew_listx in Hmem'. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros contra. apply~ (Hustart l1 l2' t0).
    rew_listx. rew_listx in contra. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hspawn.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hjoin.
  + introv Heq <- Hneq.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. simpl. exact Hsmem.
    * apply~ Hstart.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    rew_listx. splits.
    * apply~ Hend.
    * simpl. intros ->. apply Hnmem. rew_listx*.
  + introv. rew_listx.
    cases_if as Heql.
    * unfold touches_lock in Heql. subst. rew_list.
      apply* wf_lock_log_snoc_unlock.
    * rew_list. apply~ Hlock.
  + intros _.
    lets (_ & _ & _ & _ & _ & _ & _ & Hinit & _): Hwf.
    applys wf_log_init_head_snoc Hinit Hsmem.
  + introv Hmem'.
    rew_listx in Hmem'. branches; auto_star.
Qed.

(* Appending a start of [t]: [t] must either have been spawned or be the root,
   must not have already started, and -- if it is the root -- the log must be
   empty (the root starts first). The unique-starts, spawn-before-start and
   "first event is root start" conjuncts do the work. *)
Lemma wf_log_start_last : forall lg t,
    wf_log lg ->
    ((exists t1, mem (event_spawn t1 t) lg) \/ t = t_root) ->
    ~ mem (event_start t) lg ->
    (t = t_root -> lg = nil) ->
    wf_log (lg & event_start t).
Proof.
  introv Hwf Hsrc Hnmem Hrootnil.
  lets (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & _ & Hroot): Hwf.
  splits 9.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros (t1' & Hmem'). apply~ Huspawn.
    exists t1'.
    rew_listx. rew_listx in Hmem'.
    branches; autos.
  + introv Heq.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. rew_list~.
    * intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra.
      branches; autos.
      match goal with H : event_start _ = event_start _ |- _ => inverts H end.
      false Hnmem. rew_listx~.
  + introv Heq.
    forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    inverts* contra.
  + introv Heq.
    forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
  + introv Heq <- Hneq.
    forwards* [(<- & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
  + introv Heq.
    forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    rew_listx. splits*.
    simpl. intros ->.
    forwards~ Hmem': (Hstart l1 l2' (event_end t0) t0).
    false Hnmem. rew_listx*.
  + introv. rew_listx.
    cases_if~. rew_list~.
  + intros _.
    lets (_ & _ & _ & _ & _ & _ & _ & Hinit & _): Hwf.
    destruct (classic (lg = nil)) as [-> | Hne].
    * destruct Hsrc as [(t1 & Hmem) | ->]; [forwards*: mem_nil_inv Hmem|].
      exists (@nil event). rew_list~.
    * forwards (l' & Hlg): Hinit Hne.
      exists (l' & event_start t). rewrite Hlg. rew_list~.
  + introv Hmem'.
    rew_listx in Hmem'. branches; auto_star.
Qed.

Lemma unique_spawn_snoc :
  forall lg e t2,
    length (LibList.filter (fun e => exists t1, e = event_spawn t1 t2) lg) <= 1 ->
    ~(exists t1 t2, e = event_spawn t1 t2) ->
    length (LibList.filter (fun e => exists t1, e = event_spawn t1 t2) (lg & e)) <= 1.
Proof.
  introv Hlen Hnex.
  induction lg; rew_listx in *.
  - cases_if~. rew_list~.
  - cases_if~. rew_list in *. cases_if~; rew_list in *; autos~.
    false Hnex. unpack. substs*.
Qed.

Lemma conflict_free_nil :
  conflict_free nil.
Proof.
  introv Hnth1 Hnth2 Hacc Hlt.
  inverts Hnth1.
Qed.

Lemma hb_lt :
  forall log m n,
    hb log m n ->
    m < n.
Proof.
  introv Hhb.
  induction* Hhb.
Qed.

(* [hb] is monotone under extending the log on the right: an ordering that holds
   in a prefix still holds once more events are appended.  ([LogFacts] only has
   the inverse, [hb_app_inv].)  Needed to lift the [play_log] induction's
   prefix-[hb] to the extended log. *)
Lemma hb_weaken_snoc :
  forall (lg : log) E m n, hb lg m n -> hb (lg & E) m n.
Proof.
  introv Hhb. induction Hhb.
  - applys HbPo; [ applys* Nth_app_l | applys* Nth_app_l | assumption | assumption ].
  - applys HbLock; [ applys* Nth_app_l | applys* Nth_app_l | assumption ].
  - applys HbSpawn; [ applys* Nth_app_l | applys* Nth_app_l | assumption ].
  - applys HbJoin; [ applys* Nth_app_l | applys* Nth_app_l | assumption ].
  - forwards H0': Nth_app_l H0.
    forwards H1': Nth_app_l H1.
    applys HbVolatile H H0' H1' H2.
  - applys* HbTrans.
Qed.

Lemma hb_app_inv :
  forall l1 l2 m n,
    hb (l1 ++ l2) m n ->
    n < length l1 ->
    hb l1 m n.
Proof.
  introv Hhb Hlt.
  induction Hhb.
  - rew_listx in H1.
    forwards* Hdisj1: Nth_app_inv m.
    inverts Hdisj1; [| unpack; nat_math].
    forwards* Hdisj2: Nth_app_inv n.
    inverts Hdisj2; [| unpack; nat_math].
    applys* HbPo.
  - rew_listx in H1.
    forwards* Hdisj1: Nth_app_inv m.
    inverts Hdisj1; [| unpack; nat_math].
    forwards* Hdisj2: Nth_app_inv n.
    inverts Hdisj2; [| unpack; nat_math].
    applys* HbLock.
  - forwards* Hdisj1: Nth_app_inv m.
    forwards* Hdisj2: Nth_app_inv n.
    inverts Hdisj1; [| unpack; nat_math].
    inverts Hdisj2; [| unpack; nat_math].
    applys* HbSpawn.
  - forwards* Hdisj1: Nth_app_inv m.
    forwards* Hdisj2: Nth_app_inv n.
    inverts Hdisj1; [| unpack; nat_math].
    inverts Hdisj2; [| unpack; nat_math].
    applys* HbJoin.
  - forwards* Hdisj1: Nth_app_inv m.
    forwards* Hdisj2: Nth_app_inv n.
    inverts Hdisj1; [| unpack; nat_math].
    inverts Hdisj2; [| unpack; nat_math].
    applys* HbVolatile.
  - hint hb_lt.
    asserts* Hlt': (k < n).
    applys* HbTrans.
Qed.

Lemma conflict_free_last_inv :
  forall lg e,
    conflict_free (lg & e) ->
    conflict_free lg.
Proof.
  introv Hcf.
  introv Hnth1 Hnth2 Hacc Hlt.
  hint Nth_app_l.
  asserts* Hnth1': (LibList.Nth m (lg & e) (event_write t1 x v1)).
  asserts* Hnth2': (LibList.Nth n (lg & e) e2).
  forwards* Hhb: Hcf Hnth1' Hnth2' Hacc.
  applys* hb_app_inv.
  applys* Nth_inbound.
Qed.

Lemma hb_Nth_l :
  forall log m n,
    hb log m n ->
    exists e, LibList.Nth m log e.
Proof.
  introv Hhb. induction Hhb; eauto.
Qed.

Lemma hb_Nth_r :
  forall log m n,
    hb log m n ->
    exists e, LibList.Nth n log e.
Proof.
  introv Hhb. induction Hhb; eauto.
Qed.

(* If [hb log m n] and the event at [n] is a write [event_write t x v], the
   LAST hop of the derivation reaching [n] must be [HbPo] (same thread as [n],
   i.e. thread [t]): no other constructor's target side can match a write's
   shape ([HbLock]/[HbSpawn]/[HbJoin] need [event_lock]/[event_start]/
   [event_join], [HbVolatile] needs [event_read]). So there is always some
   position [q < n] on thread [t] with either [m = q] or [hb log m q] --
   [m]'s own edge into [n] "passes through" [t]'s own program order. Used to
   turn [conflict_free]'s abstract [hb log m n] (for [n] a volatile write)
   into a concrete, log-position witness on the WRITER's own thread that a
   [CH]-lookup can act on. *)
Lemma hb_last_write_same_thread_witness :
  forall log m n t x v,
    hb log m n ->
    LibList.Nth n log (event_write t x v) ->
    exists q eq, q < n /\ LibList.Nth q log eq /\ get_thread eq = t /\ (m = q \/ hb log m q).
Proof.
  introv Hhb. gen t x v.
  induction Hhb as
    [ p q e1 e2 HN1 HN2 Heq Hlt
    | q p t1 t2 l HNu HNl Hlt
    | p q t1 t2 HNs HNst Hlt
    | p q t1 t2 HNe HNj Hlt
    | p q t1 t2 x' v' v'' Hxvol HNw HNr Hlt
    | p q k Hpk IHpk Hkq IHkq ];
    introv HNen.
  - (* HbPo: [e2] is the write, so [get_thread e1 = get_thread e2 = t] *)
    forwards Heq2: Nth_functional HN2 HNen. subst e2.
    cbn [get_thread] in Heq.
    exists p e1. splits; [ exact Hlt | exact HN1 | exact Heq | left; reflexivity ].
  - (* HbLock: target is [event_lock t2 l], contradicting the write shape *)
    forwards Heq2: Nth_functional HNl HNen. false.
  - (* HbSpawn: target is [event_start t2] *)
    forwards Heq2: Nth_functional HNst HNen. false.
  - (* HbJoin: target is [event_join t1 t2] *)
    forwards Heq2: Nth_functional HNj HNen. false.
  - (* HbVolatile: target is [event_read t2 x' v''] *)
    forwards Heq2: Nth_functional HNr HNen. false.
  - (* HbTrans: recurse on the [k -> n] half, which targets the SAME [n] *)
    forwards (q1 & eq1 & Hqlt & HNq & Hgq & Hdisj): IHkq t x v HNen.
    exists q1 eq1. splits; [ exact Hqlt | exact HNq | exact Hgq | ].
    destruct Hdisj as [-> | Hhbkq].
    + right. exact Hpk.
    + right. applys HbTrans Hpk Hhbkq.
Qed.

(* If [m] is an event of thread [t] and [t] performs no [is_commit_event] event at
   any index [>= m], then every event [t] happens-before lies on thread [t].
   Reason: every cross-thread hb edge has an [is_commit_event] source, and a chain
   leaving [m] can only first cross threads via such a [t]-event at index [>= m]
   (all base edges strictly increase the index). *)
Lemma hb_preserves_thread :
  forall lg m n,
    hb lg m n ->
    forall t em en,
      LibList.Nth m lg em ->
      get_thread em = t ->
      (forall p ep, m <= p -> LibList.Nth p lg ep -> get_thread ep = t -> ~ is_commit_event ep) ->
      LibList.Nth n lg en ->
      get_thread en = t.
Proof.
  introv Hhb.
  induction Hhb as
    [ m n ea eb HNa HNb Heq Hlt
    | n m lt1 lt2 ll HNsrc HNtgt Hlt
    | m n st1 st2 HNsrc HNtgt Hlt
    | m n jt1 jt2 HNsrc HNtgt Hlt
    | m n vt1 vt2 vx vv vv' Hvol HNsrc HNtgt Hlt
    | m n mid Hmk IHmk Hkn IHkn ];
    introv Hm Hgt Hns Hn.
  - (* HbPo: same thread *)
    forwards Heqa: Nth_functional Hm HNa.
    forwards Heqb: Nth_functional Hn HNb.
    congruence.
  - (* HbLock: source [event_unlock lt1 ll] is a sync_out of t *)
    forwards Heq: Nth_functional Hm HNsrc. subst em.
    false (Hns m (event_unlock lt1 ll)); [ nat_math | assumption | assumption | simpl; exact I ].
  - (* HbSpawn: source [event_spawn st1 st2] is a sync_out of t *)
    forwards Heq: Nth_functional Hm HNsrc. subst em.
    false (Hns m (event_spawn st1 st2)); [ nat_math | assumption | assumption | simpl; exact I ].
  - (* HbJoin: source [event_end jt2] is a sync_out of t *)
    forwards Heq: Nth_functional Hm HNsrc. subst em.
    false (Hns m (event_end jt2)); [ nat_math | assumption | assumption | simpl; exact I ].
  - (* HbVolatile: source [event_write vt1 vx vv] is a sync_out of t, since
       [vx] is volatile *)
    forwards Heq: Nth_functional Hm HNsrc. subst em.
    false (Hns m (event_write vt1 vx vv)); [ nat_math | assumption | assumption | simpl; exact Hvol ].
  - (* HbTrans: chain through the intermediate index [mid] *)
    forwards (ek & Hek): hb_Nth_r Hmk.
    forwards Hgek: IHmk Hm Hgt Hns Hek.
    asserts Hns': (forall p ep, mid <= p -> LibList.Nth p lg ep -> get_thread ep = t -> ~ is_commit_event ep).
    { introv Hle HN Hg. forwards Hlt': hb_lt Hmk.
      apply Hns with (p := p); [ nat_math | exact HN | exact Hg ]. }
    applys IHkn Hek Hgek Hns' Hn.
Qed.

(* Extending a "no commit event of [t] at index >= m" property by one event:
   it survives appending any event that is not a commit event of [t]. *)
Lemma no_commit_event_snoc :
  forall (lg : log) E m t,
    (forall p ep, m <= p -> LibList.Nth p lg ep -> get_thread ep = t -> ~ is_commit_event ep) ->
    (get_thread E = t -> ~ is_commit_event E) ->
    (forall p ep, m <= p -> LibList.Nth p (lg & E) ep -> get_thread ep = t -> ~ is_commit_event ep).
Proof.
  introv Hbase HE. introv Hle HN Hg.
  forwards [HN' | (Hpe & Hee)]: Nth_last_inv HN.
  - applys* Hbase.
  - subst ep. applys* HE.
Qed.

(* Membership is preserved when an element is appended at the very end. *)
Lemma mem_app_snoc_r : forall (x E : event) l1 l2,
  mem x (l1 ++ l2) -> mem x (l1 ++ (l2 & E)).
Proof.
  introv H. rewrite mem_app_eq in *. rewrite mem_last_eq. tauto.
Qed.

(* Dropping the last element of a well-formed lock log keeps it well-formed. *)
Lemma wf_lock_log_drop_last :
  forall ll, wf_lock_log ll -> forall xs y, ll = xs & y -> wf_lock_log xs.
Proof.
  introv H. induction H as [ | t l | t1 l ll0 Hwf0 IH ]; introv Heq.
  - false. applys nil_eq_last_inv Heq.
  - assert (Hrw: event_lock t l :: nil = nil & event_lock t l) by (rew_list; reflexivity).
    rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq. subst xs. constructor.
  - destruct (last_case ll0) as [Hnil | (z & ll' & Hsnoc)].
    + subst ll0.
      assert (Hrw: event_lock t1 l :: event_unlock t1 l :: nil
                 = (event_lock t1 l :: nil) & event_unlock t1 l) by (rew_list; reflexivity).
      rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq. subst xs. constructor.
    + subst ll0.
      assert (Hrw: event_lock t1 l :: event_unlock t1 l :: (ll' & z)
                 = (event_lock t1 l :: event_unlock t1 l :: ll') & z) by (rew_list; reflexivity).
      rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq. subst xs.
      apply WfLockUnlock. apply (IH ll' z). reflexivity.
Qed.

(* An unlock at the end of a well-formed lock log is preceded by the matching lock. *)
Lemma wf_lock_log_unlock_prev :
  forall ll, wf_lock_log ll ->
    forall xs t l, ll = xs & event_unlock t l ->
    exists pre, xs = pre & event_lock t l.
Proof.
  introv H. induction H as [ | t0 l0 | t1 l0 ll0 Hwf0 IH ]; introv Heq.
  - false. applys nil_eq_last_inv Heq.
  - assert (Hrw: event_lock t0 l0 :: nil = nil & event_lock t0 l0) by (rew_list; reflexivity).
    rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq. discriminate Hy.
  - destruct (last_case ll0) as [Hnil | (z & ll' & Hsnoc)].
    + subst ll0.
      assert (Hrw: event_lock t1 l0 :: event_unlock t1 l0 :: nil
                 = (event_lock t1 l0 :: nil) & event_unlock t1 l0) by (rew_list; reflexivity).
      rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq.
      inverts Hy. subst xs. exists (@nil event). rew_list. reflexivity.
    + subst ll0.
      assert (Hrw: event_lock t1 l0 :: event_unlock t1 l0 :: (ll' & z)
                 = (event_lock t1 l0 :: event_unlock t1 l0 :: ll') & z) by (rew_list; reflexivity).
      rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq. subst xs.
      forwards (pre & Hpre): (>> IH ll' t l).
      { rewrite Hy. reflexivity. }
      exists (event_lock t1 l0 :: event_unlock t1 l0 :: pre). rewrite Hpre. rew_list. reflexivity.
Qed.

(* wf_log is preserved by dropping the last event. *)
Lemma wf_log_last_inv :
  forall log E, wf_log (log & E) -> wf_log log.
Proof.
  introv Hwf. unfold wf_log in *.
  lets (Huspawn & Hustart & Hstartsp & Hjoinend & Hstartby & Hendby & Hlock & _ & Hrootsp): Hwf.
  splits 9.
  - introv Heq. intros (t1' & Hm).
    forwards Hno: (>> Huspawn l1 (l2 & E) t1 t2).
    { rewrite Heq. rew_list~. }
    apply Hno. exists t1'. applys mem_app_snoc_r. exact Hm.
  - introv Heq. intro Hm.
    forwards Hno: (>> Hustart l1 (l2 & E) t).
    { rewrite Heq. rew_list~. }
    apply Hno. applys mem_app_snoc_r. exact Hm.
  - introv Heq.
    forwards~ Hex: (>> Hstartsp l1 (l2 & E) t2).
    rewrite Heq. rew_list~.
  - introv Heq.
    forwards~ Hm: (>> Hjoinend l1 (l2 & E) t1 t2).
    rewrite Heq. rew_list~.
  - introv Heq Hgt Hne.
    forwards* Hm: (>> Hstartby l1 (l2 & E) e t).
    rewrite Heq. rew_list*.
  - introv Heq.
    forwards HF: (>> Hendby l1 (l2 & E) t).
    { rewrite Heq. rew_list~. }
    rewrite Forall_last_eq in HF. destruct~ HF as (HF & _).
  - (* locks *) intro l.
    forwards Hwll: Hlock l.
    rewrite filter_last in Hwll.
    cases_if as Ht.
    + applys wf_lock_log_drop_last Hwll. rew_list~.
    + rew_list~ in Hwll.
  - (* init *) intros Hne.
    lets (_ & _ & _ & _ & _ & _ & _ & Hinit & _): Hwf.
    destruct log as [| e0 log']; [false Hne; reflexivity|].
    forwards (l & Hl): Hinit. { rew_list. discriminate. }
    rew_list in Hl. inverts Hl. exists log'. reflexivity.
  - (* root never spawned *) intros t1 Hmem.
    apply (Hrootsp t1). rewrite mem_last_eq. auto.
Qed.

Lemma spawned_thread_no_prior_event :
  forall log t1 t2 m em,
    wf_log (log & event_spawn t1 t2) ->
    LibList.Nth m log em ->
    get_thread em <> t2.
Proof.
  introv Hwf HN.
  forwards Hmem: Nth_mem HN.
  forwards (l1 & l2 & Heq): mem_inv_middle Hmem.
  unfold wf_log in Hwf.
  lets (Huspawn & Hustart & Hstartsp & Hjoinend & Hstartby & Hendby & Hlock & _ & Hrootsp): Hwf.
  intro Hgt.
  assert (Hmemstart: mem (event_start t2) log).
  {
    destruct (classic (em = event_start t2)) as [Hes | Hes].
    - rewrite~ <- Hes.
    - assert (Heq2: log & event_spawn t1 t2 = l1 ++ em :: (l2 & event_spawn t1 t2))
        by (rewrite Heq; rew_list~).
      forwards~ Hms: (>> Hstartby l1 (l2 & event_spawn t1 t2) em t2).
      rewrite Heq. rewrite~ mem_app_eq.
  }
  forwards (a & b & Heqs): mem_inv_middle Hmemstart.
  assert (Heq3: log & event_spawn t1 t2 = a ++ event_start t2 :: (b & event_spawn t1 t2))
    by (rewrite Heqs; rew_list~).
  forwards [(tsp & Hmemsp) | Hroot]: Hstartsp Heq3.
  - (* start preceded by a spawn: contradicts unique spawn *)
    assert (Heq4: log & event_spawn t1 t2 = log ++ event_spawn t1 t2 :: nil)
      by rew_list~.
    forwards Hnospawn: Huspawn Heq4.
    apply Hnospawn. exists tsp. rew_list.
    rewrite Heqs. rewrite~ mem_app_eq.
  - (* start preceded by an init: t2 = t_root, but t2 is spawned *)
    assert (Hmi: mem (event_start t2) (log & event_spawn t1 t2)).
    { rewrite Heqs. rew_listx~. }
    forwards (c & d & Heqc): mem_inv_middle Hmi.
    rewrite Hroot in *.
    apply (Hrootsp t1). apply mem_last_r.
Qed.

(* wf bookkeeping: an event appended after [t2] has ended is not [t2] acting nor
   a (re-)spawn of [t2]. (From "threads end by ending" + "unique spawns".) *)
Lemma event_after_end_snoc :
  forall log E m t2,
    wf_log (log & E) ->
    LibList.Nth m log (event_end t2) ->
    get_thread E <> t2 /\ (forall t1, E <> event_spawn t1 t2).
Proof.
  introv Hwf HN.
  forwards Hmem: Nth_mem HN.
  forwards (l1 & l2 & Heq): mem_inv_middle Hmem.
  unfold wf_log in Hwf.
  lets (Huspawn & Hustart & Hstartsp & Hjoinend & Hstartby & Hendby & Hlock & _ & Hrootsp): Hwf.
  assert (Heq2: log & E = l1 ++ event_end t2 :: (l2 & E))
    by (rewrite Heq; rew_list~).
  splits.
  - forwards HForall: Hendby Heq2.
    applys Forall_mem_inv HForall. rewrite~ mem_last_eq.
  - introv Heqsp.
    forwards~ Hmemstart: (>> Hstartby l1 (l2 & E) (event_end t2) t2).
    forwards (a & b & Heql1): mem_inv_middle Hmemstart.
    assert (Heq3: log & E = a ++ event_start t2 :: (b ++ event_end t2 :: (l2 & E))).
    { rewrite Heq2. rewrite Heql1. rew_list~. }
    forwards [(tsp & Hmemsp) | Hminit]: Hstartsp Heq3.
    + assert (Heq4: log & E = log ++ event_spawn t1 t2 :: nil)
        by (rewrite Heqsp; rew_list~).
      forwards Hnospawn: Huspawn Heq4.
      apply Hnospawn. exists tsp. rew_list.
      rewrite Heq, Heql1. rewrite mem_app_eq. left. rewrite* mem_app_eq.
    + assert (Hmi: mem (event_start t2) (log & E)).
      { rewrite Heq3. rew_listx~. }
      apply (Hrootsp t1). rewrite Heqsp. subst. apply mem_last_r.
Qed.

(* wf bookkeeping: before [t2] has started, no event is [t2] acting nor a
   re-spawn of [t2]. (From "threads start by starting" + "unique spawns".) *)
Lemma event_after_spawn_snoc :
  forall log E m t1 t2,
    wf_log (log & E) ->
    LibList.Nth m log (event_spawn t1 t2) ->
    ~ LibList.mem (event_start t2) (log & E) ->
    get_thread E <> t2 /\ (forall t1', E <> event_spawn t1' t2).
Proof.
  introv Hwf HN Hnstart.
  forwards Hmem: Nth_mem HN.
  forwards (l1 & l2 & Heq): mem_inv_middle Hmem.
  unfold wf_log in Hwf.
  lets (Huspawn & Hustart & Hstartsp & Hjoinend & Hstartby & Hendby & Hlock & _ & Hrootsp): Hwf.
  splits.
  - intro Hgt.
    destruct (classic (E = event_start t2)) as [HE | HE].
    + apply Hnstart. rewrite mem_last_eq. right. rewrite HE. reflexivity.
    + forwards~ Hms: (>> Hstartby log (@nil event) E t2).
      apply Hnstart. rewrite~ mem_last_eq.
  - introv Heqsp.
    assert (Heq4: log & E = log ++ event_spawn t1' t2 :: nil)
      by (rewrite Heqsp; rew_list~).
    forwards Hnospawn: Huspawn Heq4.
    apply Hnospawn. exists t1. rew_list.
    rewrite Heq. rewrite mem_app_eq. right. rewrite~ mem_cons_eq.
Qed.

(* wf bookkeeping: a thread's start event is unique. *)
Lemma start_not_in_prefix :
  forall log t2,
    wf_log (log & event_start t2) ->
    ~ LibList.mem (event_start t2) log.
Proof.
  introv Hwf. unfold wf_log in Hwf.
  destruct Hwf as (_ & Hustart & _).
  assert (Heq: log & event_start t2 = log ++ event_start t2 :: nil)
    by (rew_list~).
  forwards Hns: Hustart Heq.
  rew_list in Hns. exact Hns.
Qed.

(* wf_lock_log bookkeeping (assumed): an unlock of [l] is immediately preceded, in
   the [l]-filter, by the matching [event_lock t l]. *)
Lemma unlock_prev_lock :
  forall log t l,
    wf_log (log & event_unlock t l) ->
    exists pre, LibList.filter (fun e => touches_lock l e) log = pre & event_lock t l.
Proof.
  introv Hwf. unfold wf_log in Hwf.
  destruct Hwf as (_ & _ & _ & _ & _ & _ & Hlock & _).
  forwards Hwll: Hlock l.
  rewrite filter_last in Hwll.
  cases_if as Ht.
  applys wf_lock_log_unlock_prev Hwll. rew_list~.
Qed.

(* The last element of the i-write filter is the last i-write in the log, as a
   position with the maximality property. *)
Lemma last_write_position :
  forall log x lw tw vw,
    LibList.filter (fun e => writes_variable x e) log = lw & event_write tw x vw ->
    exists m, LibList.Nth m log (event_write tw x vw) /\
              (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m).
Proof.
  induction log as [ | e log' IH ]; introv Hfilter.
  - rew_listx in Hfilter. false. applys nil_eq_last_inv Hfilter.
  - rew_listx in Hfilter. cases_if as HP.
    + (* writes_variable x e *)
      destruct (last_case (LibList.filter (fun e0 => writes_variable x e0) log'))
        as [Hnil | (x' & lw' & Hsnoc')].
      * (* no x-write in log': e is the last x-write, at index 0 *)
        rewrite Hnil in Hfilter.
        change (e :: nil) with (nil & e) in Hfilter.
        forwards (Hlweq & Hex): last_eq_last_inv Hfilter.
        exists 0. split.
        -- rewrite <- Hex. apply Nth_zero.
        -- introv HNk. forwards [(Hk0 & Hxe) | (mm & Hkm & HNmm)]: Nth_cons_inv HNk.
           ++ subst. nat_math.
           ++ exfalso.
              asserts Hmemf:
                (mem (event_write tk x vk) (LibList.filter (fun e0 => writes_variable x e0) log')).
              { applys mem_filter; [ applys Nth_mem HNmm | reflexivity ]. }
              rewrite Hnil in Hmemf. rewrite mem_nil_eq in Hmemf. exact Hmemf.
      * (* filter log' nonempty; its last element is event_write tw x vw *)
        asserts Hsnoc2:
          (LibList.filter (fun e0 => writes_variable x e0) log' = lw' & event_write tw x vw).
        { rewrite Hsnoc' in Hfilter.
          change (e :: (lw' & x')) with ((e :: lw') & x') in Hfilter.
          forwards (Hlweq & Hxeq): last_eq_last_inv Hfilter.
          rewrite Hsnoc'. rewrite Hxeq. reflexivity. }
        forwards (m' & HNm' & Hmax'): IH Hsnoc2.
        exists (S m'). split.
        -- apply Nth_succ. exact HNm'.
        -- introv HNk. forwards [(Hk0 & Hxe) | (mm & Hkm & HNmm)]: Nth_cons_inv HNk.
           ++ subst. nat_math.
           ++ forwards Hle: Hmax' HNmm. nat_math.
    + (* ~ writes_variable x e *)
      forwards (m' & HNm' & Hmax'): IH Hfilter.
      exists (S m'). split.
      -- apply Nth_succ. exact HNm'.
      -- introv HNk. forwards [(Hk0 & Hxe) | (mm & Hkm & HNmm)]: Nth_cons_inv HNk.
         ++ subst. exfalso. apply HP. reflexivity.
         ++ forwards Hle: Hmax' HNmm. nat_math.
Qed.

Lemma get_uncommitted'_has_sync :
  forall log t acc,
    Exists is_sync_event log ->
    get_uncommitted' t log acc = get_uncommitted' t log nil.
Proof.
  introv Hex.
  gen acc.
  induction Hex; intros; simpls; cases_if~.
Qed.

Lemma get_uncommitted'_no_sync :
  forall log t acc,
    ~Exists is_sync_event log ->
    get_uncommitted' t log acc = acc ++ log.
Proof.
  intros log.
  induction log; introv Hnex; simpls; rew_list~.
  cases_if~.
  - false Hnex. constructors*.
  - rew_listx in Hnex. rew_logic in Hnex. unpack.
    rewrite~ IHlog. rew_list~.
Qed.

Lemma get_uncommited_inv :
  forall log t,
    exists log', log = log' ++ get_uncommitted t log.
Proof.
  intros log t.
  unfolds get_uncommitted.
  induction log; simpls.
  - exists* (@nil event).
  - unpack. destruct (classic (Exists is_sync_event log)).
    + rewrite~ get_uncommitted'_has_sync. exists (a :: log'). rew_list*.
    + cases_if.
      * rewrite~ get_uncommitted'_no_sync. exists (a :: nil). rew_list*.
      * rewrite~ get_uncommitted'_no_sync. exists (@nil event). rew_list*.
Qed.

Example nil_log_wf : wf_log nil.
Proof.
  splits 9; rew_list.
  - introv Heq.
    forwards: nil_eq_middle_inv; rew_list*.
  - introv Heq.
    forwards: nil_eq_middle_inv; rew_list*.
  - introv Heq.
    forwards: nil_eq_middle_inv; rew_list*.
  - introv Heq.
    forwards: nil_eq_middle_inv; rew_list*.
  - introv Heq.
    forwards: nil_eq_middle_inv; rew_list*.
  - introv Heq.
    forwards: nil_eq_middle_inv; rew_list*.
  - intros. rew_listx. constructor.
  - introv Hne. false* Hne.
  - introv contra.
    inverts contra as Hmem.
Qed.

Lemma no_thin_air_nil : no_thin_air nil.
Proof. intros n t x v HN. inverts HN. Qed.

(* Structural half of the invariant: appending one event preserves the
   sourcedness of every read already in the log. Both the "not hb-after" and the
   "no intervening x-write" clauses survive because hb only points forward
   ([hb_lt]) and [hb_app_inv] shows the new (last) event cannot slip between two
   earlier positions. *)
Lemma sourced_read_snoc :
  forall log e n,
    n < length log ->
    sourced_read log n ->
    sourced_read (log & e) n.
Proof.
  introv Hlt Hread.
  introv Hnth.
  asserts Hnth': (LibList.Nth n log (event_read t x v)).
  {
    forwards* [Hnth' | (m & contra & _)]: Nth_app_inv Hnth.
  }
  forwards~ (m & t' & Hmth & Hnhb & Hnex): Hread Hnth'.
  exists m t'. splits.
  - applys* Nth_app_l.
  - intros contra. apply Hnhb.
    forwards~ Hlt': Nth_inbound Hmth.
    applys* hb_app_inv.
  - introv (m' & t'' & v' & Hneq & Hmth' & Hhb & Hhb').
    apply Hnex.
    asserts Hlt': (m' < length log).
    {
      forwards*: hb_lt Hhb'.
    }
    forwards [Hmth'' | (contra & _)]: Nth_last_inv Hmth'; [|nat_math].
    forwards~ Hhb'': hb_app_inv Hhb.
    forwards~ Hhb''': hb_app_inv Hhb'.
    exists m' t'' v'.
    splits*.
Qed.

(* Appending a non-read event preserves the whole invariant: old reads by
   [sourced_read_snoc], and the new last position is not a read (vacuous). *)
Lemma no_thin_air_snoc_nonread :
  forall log e,
    (forall t x v, e <> event_read t x v) ->
    no_thin_air log ->
    no_thin_air (log & e).
Proof.
  introv Hneq Hnt.
  introv Hnth.
  forwards* [Hnth' | (Heq & ->)]: Nth_last_inv Hnth.
  forwards Hlt: Nth_inbound Hnth'.
  apply* sourced_read_snoc.
Qed.
