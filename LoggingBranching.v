From Vcm Require Import Common.
From Vcm Require Import Branching.
From Vcm Require Import Log.

Import Branching.
Import Log.

Definition deltas := map tid staging_area.
Definition commits := map tid commit.
Definition lcommits := map lid commit.

Inductive play_event : event -> (deltas * commits * graph * lcommits) -> (deltas * commits * graph * lcommits) -> Prop :=
| PlayRead :
  forall D TC G LC t i v,
    play_event (event_read t i v) (D, TC, G, LC) (D, TC, G, LC)
| PlayWrite :
  forall D TC G LC t i v d,
    binds D t d ->
    play_event (event_write t i v) (D, TC, G, LC) (D[t := d[i := v]], TC, G, LC)
| PlayStart :
  forall D TC G LC t,
    play_event (event_start t) (D, TC, G, LC) (D, TC, G, LC)
| PlayEnd :
  forall D TC G LC t c c' d,
    binds TC t c ->
    commit_fresh G c' ->
    binds D t d ->
    play_event (event_end t) (D, TC, G, LC) (D[t := empty], TC[t := c'], graph_commit G c c' d, LC)
| PlaySpawn :
  forall D TC G LC t1 t2 c c' d,
    binds TC t1 c ->
    commit_fresh G c' ->
    binds D t1 d ->
    play_event (event_spawn t1 t2) (D, TC, G, LC) (D[t1 := empty][t2 := empty], TC[t1 := c'][t2 := c'], graph_commit G c c' d, LC)
| PlayJoin :
  forall D TC G LC t1 t2 c1 c2 c',
    binds TC t1 c1 ->
    binds TC t2 c2 ->
    commit_fresh G c' ->
    play_event (event_join t1 t2) (D, TC, G, LC) (D, TC[t1 := c'], graph_merge G c2 c1 c', LC)
| PlayLock :
  forall D TC G LC t l c1 c2 c',
    binds TC t c1 ->
    binds LC l c2 ->
    commit_fresh G c' ->
    play_event (event_lock t l) (D, TC, G, LC) (D, TC[t := c'], graph_merge G c2 c1 c', LC)
| PlayUnlock :
  forall D TC G LC t l c c' d,
    binds TC t c ->
    commit_fresh G c' ->
    binds D t d ->
    play_event (event_unlock t l) (D, TC, G, LC) (D[t := empty], TC[t := c'], graph_commit G c c' d, LC[l := c'])
.

Inductive play_log : log -> (deltas * commits * graph * lcommits) -> (deltas * commits * graph * lcommits) -> Prop :=
| PlayNil :
  forall D TC G LC,
    play_log nil (D, TC, G, LC) (D, TC, G, LC)
| PlaySnoc :
  forall E log D D' D'' TC TC' TC'' G G' G'' LC LC' LC'',
    play_log log (D, TC, G, LC) (D', TC', G', LC') ->
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    play_log (log & E) (D, TC, G, LC) (D'', TC'', G'', LC'')
.

Definition is_sync_event (E : event) :=
  match E with
  | event_spawn t _
  | event_join t _
  | event_lock t _
  | event_unlock t _
  | event_start t
  | event_end t => True
  | _ => False
  end.

Fixpoint get_uncommitted' (t : tid) (l : log) (acc : log) :=
  match l with
  | nil => acc
  | E :: log' => get_uncommitted' t log' (If is_sync_event E then nil else acc & E)
  end.

Definition get_uncommitted (t : tid) (log : log) :=
  get_uncommitted' t log nil.

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

Fixpoint find_write (log : log) (i : loc) : option val :=
  match log with
  | nil => None
  | event_write t j v :: log' =>
      match find_write log' i with
      | None => If i = j then Some v else None
      | Some v' => Some v'
      end
  | _ :: log' => find_write log' i
  end.

Lemma find_write_none :
  forall log i,
    LibList.filter (writes_location i) log = nil ->
    find_write log i = None.
Proof.
  introv Hfilter.
  induction log as [|a log IH]; simpls.
  - reflexivity.
  - rew_listx in Hfilter.
    cases_if~.
    simpls. rewrite~ IH.
    destruct~ a. cases_if*.
Qed.

Lemma find_write_writes_location :
  forall log log' i v t,
    LibList.filter (writes_location i) log = log' & event_write t i v ->
    find_write log i = Some v.
Proof.
  introv Hfilter.
  gen log'. induction log as [|a log IH]; intros; simpls.
  - rew_listx in Hfilter. false. apply* nil_eq_last_inv.
  - rew_listx in Hfilter. cases_if.
    + destruct a; simpls*. destruct log'; rew_list in Hfilter.
      * inverts Hfilter. rewrite~ find_write_none. case_if*.
      * inverts Hfilter.
        rewrite* (IH log').
    + rewrite* (IH log').
      destruct* a.
Qed.

Lemma find_write_get_uncommitted :
  forall log t i v,
    find_write (get_uncommitted t log) i = Some v ->
    exists log' t, LibList.filter (writes_location i) log = log' & event_write t i v.
Proof.
  introv Hfind.
  induction log; simpls*.
  (* TODO: probably need to prove something more general about get_uncommitted' *)
Admitted.

Definition describes (log : log) (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      (* Spawned threads exist *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log) <-> t2 \indom T)
      /\
      (* Spawned threads that have not started are new *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log) <-> exists e h ts, binds T t2 (state_new, e, h, ts))
      /\
      (* Ended threads are ended *)
      (forall t,
          mem (event_end t) log <-> exists e h ts, binds T t ((state_terminated, e, h, ts)))
      /\
      (* Started threads that are not ended are running *)
      (forall t,
          mem (event_start t) log /\ ~mem (event_end t) log <-> exists e d h, binds T t (state_running, e, d, h))
      /\
      (* Locked locks are locked *)
      (forall t l,
          (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t l) <-> exists h, binds L l (ls_held t, h))
      /\
      (* Unlocked locks are unlocked (or untouched) *)
      (forall l,
          (log = nil \/ (exists t log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t l)) <-> exists h, binds L l (ls_free, h))
      /\
      (* Replaying the log produces the commit graph, staging areas and lock/thread commits *)
      (exists D TC LC,
          play_log log (empty, empty, (empty, empty), empty) (D, TC, G, LC) /\
            (forall t, t \indom T -> exists ts e, binds T t (ts, e, D[t], TC[t])) /\
            (forall l, l \indom L -> exists ls, binds L l (ls, LC[l])) /\
            (forall t, t \indom T -> t \indom D) /\
            (forall t, t \indom T -> t \indom TC) /\
            (forall l, l \indom L -> l \indom LC))

(*      (* Deltas are uncommitted writes *)
      (forall t ts e d h,
          binds T t (ts, e, d, h) -> d = find_write (get_uncommitted t log)
      )*)
  end.

Inductive step : (cfg * log) -> (cfg * log) -> Prop :=
| StepStart : forall T G L t e d h log,
    binds T t (state_new, e, d, h) ->
    step ((T, G, L), log) ((T[t := (state_running, e, d, h)], G, L), log & event_start t)
| StepEnd : forall T T' G G' L t r d h h' log,
    binds T t (state_running, te_ret r, d, h) ->
    commit_fresh G h' ->
    do_commit t h' T G = (T', G') ->
    step ((T, G, L), log) ((T'[t := (state_terminated, te_ret r, empty, h')], G', L), log & event_end t)
| StepReadLocal : forall T G L t e d h K i v log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read i) ->
    binds d i v ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K (ret_val v)), d, h)], G, L), log & event_read t i v)
| StepReadGlobal : forall T G L t e d h K i v log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read i) ->
    i \notindom d ->
    is_latest_value G h i v ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K (ret_val v)), d, h)], G, L), log & event_read t i v)
| StepWrite : forall T G L t e d h K i v log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_write i v) ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K void), d[i := v], h)], G, L), log & event_write t i v)
| StepSpawn : forall T T' G G' L t (t' : tid) e d h h' K e' log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    commit_fresh G h' ->
    push_thread t t' h' (T[t := (state_running, te_exp (K t'), d, h)][t' := (state_new, te_exp e', empty, 0)]) G = (T', G') ->
    step ((T, G, L), log) ((T', G', L), log & event_spawn t t')
| StepJoin : forall T T' G G' L t t' e d h h' h'' K r log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, h') ->
    conflict_free_merge d h h' G ->
    commit_fresh G h'' ->
    pull_thread t t' h'' T G = (T', G') ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step ((T, G, L), log) ((T'[t := (state_running, te_exp (K r), d, h'')], G', L), log & event_join t t')
| StepLock : forall T T' G G' L t e d h h' h'' K l log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    binds L l (ls_free, h') ->
    conflict_free_merge d h h' G ->
    commit_fresh G h'' ->
    pull_lock t l h'' T G L = (T', G') ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step ((T, G, L), log) ((T'[t := (state_running, te_exp (K void), d, h'')], G', L[l := (ls_held t, h')]), log & event_lock t l)
| StepRelease : forall T T' G G' (L L' : locks) t e d h h' h'' K l log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t, h') ->
    commit_fresh G h'' ->
    push_lock t l h'' T G L = (T', G', L') ->
    binds T' t (state_running, te_exp e, empty, h'') ->
    step ((T, G, L), log) ((T'[t := (state_running, te_exp (K void), empty, h'')], G', L'[l := (ls_free, h'')]), log & event_unlock t l)
.

Hint Constructors step Branching.step : vcm.

Theorem step_equiv :
  forall cfg cfg' log,
    (exists log', step (cfg, log) (cfg', log')) <-> Branching.step cfg cfg'.
Proof.
  introv. split; introv Hstep.
  - destruct Hstep as (log' & Hstep). inverts* Hstep.
  - inverts* Hstep.
    + exists. applys* StepReadLocal.
    + exists. applys* StepReadGlobal.
    + exists. applys* StepSpawn.
    + exists. applys* StepJoin.
Qed.

Theorem step_preserves_wf_log :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    wf_log log'.
Proof.
  introv Hwf Hdesc Hstep.
  destruct Hwf as (Huspawn & Hustart & Huend & Hspawn & Hjoin & Hstart & Hend & Hlock).
  inversion Hstep; substs; clear Hstep.
  - (* StepStart: log' = log & event_start t *)
    destruct Hdesc as (_ & Hdstart & _).
    asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t) log /\ ~mem (event_start t) log).
    { apply* Hdstart. }
    splits.
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
        branches; autos. inverts H0.
        false Hnmem. rew_listx~.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra.
      branches; autos.
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
  - (* StepEnd: log' = log & event_end t *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_list. exact Henmem.
      * intros contra. apply~ (Huend l1 l2' t0).
        rew_listx. rew_listx in contra.
        branches; autos.
        inverts H.
        false Henmem. rew_listx*.
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
        -- simpl. intros ->. apply Henmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepReadLocal: log' = log & event_read t i v *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
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
      intros contra. apply~ (Huend l1 l2' t0).
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
      * simpl. intros ->. apply Hrnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepReadGlobal: log' = log & event_read t i v *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
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
      intros contra. apply~ (Huend l1 l2' t0).
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
      * simpl. intros ->. apply Hrnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepWrite: log' = log & event_write t i v *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hwnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
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
      intros contra. apply~ (Huend l1 l2' t0).
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
      * simpl. intros ->. apply Hwnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepSpawn: log' = log & event_spawn t t' *)
    destruct Hdesc as (Hdspawned & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hsnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Hnospawn: (~exists t1, mem (event_spawn t1 t') log).
    { intros (t1 & Hmem').
      match goal with Hni : t' \notindom T |- _ => apply Hni end.
      apply (Hdspawned t'). exists t1. exact Hmem'. }
    splits.
    + introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_listx~.
      * intros (t1' & Hmem''). apply~ Huspawn. exists t1'.
        rew_listx. rew_listx in Hmem''.
        branches; autos.
        match goal with H : event_spawn _ _ = event_spawn _ _ |- _ => inverts H end.
        false Hnospawn. exists t1. rew_listx~.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
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
      * simpl. intros ->. apply Hsnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepJoin: log' = log & event_join t t' *)
    destruct Hdesc as (_ & _ & Hdend & Hdrunning & _).
    asserts (Hsmem & Hjnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts Htended: (mem (event_end t') log).
    { apply (Hdend t'). eauto. }
    splits.
    + (* Unique spawns: event_join is not a spawn *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + (* Unique starts: event_join is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Unique ends: event_join is not an end *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Spawn before start: event_join is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + (* Join after end: event_join t t' appended — need event_end t' in prefix *)
      introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_listx~.
      * apply* Hjoin.
    + (* Start before non-start *)
      introv Heq <- Hneq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + (* No events after end for that thread *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hjnmem. rew_listx*.
    + (* Lock filter unchanged: touches_lock l (event_join t t') = False *)
      introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepLock: log' = log & event_lock t l *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _ & Hdunlock & _).
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts Hlfree: (log = nil \/ exists t'' log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_unlock t'' l).
    { apply (Hdunlock l). eauto. }
    splits.
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
      intros contra. apply~ (Huend l1 l2' t0).
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
    + (* wf_lock_log: for l0 = l, filter grows by event_lock t l *)
      introv. rew_listx.
      cases_if as Heql.
      * unfold touches_lock in Heql. subst. rew_list.
        apply wf_lock_log_snoc_lock.
        { apply~ Hlock. }
        { destruct Hlfree as [Hnil | (t'' & log'' & Hfilt)].
          - left. subst. rew_listx~.
          - right. exists t'' log''. exact Hfilt. }
      * rew_list. apply~ Hlock.
  - (* StepRelease: log' = log & event_unlock t l *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & Hdlock & _).
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts (log'' & Hlheld): (exists log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_lock t l).
    { apply (Hdlock t l). eauto. }
    splits.
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
      intros contra. apply~ (Huend l1 l2' t0).
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
      * simpl. intros ->. apply Hrnmem. rew_listx*.
    + (* wf_lock_log: for l0 = l, filter grows by event_unlock t l *)
      introv. rew_listx.
      cases_if as Heql.
      * unfold touches_lock in Heql. subst. rew_list.
        apply* wf_lock_log_snoc_unlock.
      * rew_list. apply~ Hlock.
Qed.

Hint Resolve inhab_thread : vcm.

Lemma inhab_vlock : Inhab (lock_state * commit).
  constructor. exists (ls_free, 0). tauto.
Qed.

Hint Resolve inhab_vlock : vcm.

Ltac rew_dom :=
  repeat
  match goal with
  | H : context[dom ?M[?k := ?v]] |- _ =>
      replace (dom M[k := v]) with (union (dom M) (single k)) in H;
      [| solve[symmetry; apply dom_update] ]
  | _ : _ |- context[dom ?M[?k := ?v]] =>
      replace (dom M[k := v]) with (union (dom M) (single k));
      [| solve[symmetry; apply dom_update] ]
  end.

Theorem step_preserves_describes :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    describes log' cfg'.
Proof.
  introv Hwf Hdesc Hstep.
  destruct Hwf as (Huspawn & Hustart & Huend & Hspawn & Hjoin & Hstart & Hend & Hlock).
  inversion Hstep; substs; clear Hstep.
  - (* StepStart: log' = log & event_start t, T' = T[t := running] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay).
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv (t3 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply (Hdspawned t2). eauto. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply (Hdspawned t2). autos. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply (Hdspawned t). autos. }
           exists. rew_listx*.
    + (* 2. New threads *)
      intros t2. splits.
      * introv (t1 & Hmem & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & h' & ts' & Hbinds): (exists e' h' ts', binds T t2 (state_new, e', h', ts')).
        { apply (Hdnew t2). exists t1. splits.
          - rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence].
          - intros contra. apply Hnmem. rew_listx*. }
        exists e' h' ts'.
        apply~ binds_update_neq.
      * introv (e' & h' & ts' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t2) log /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists e' h' ts'. forwards~: binds_update_neq_inv Hbinds. }
        exists t1. rew_listx. splits.
        -- left. assumption.
        -- intros contra. rew_listx in contra. destruct contra; [apply Hnmem; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t0 (state_terminated, e2, h2, ts2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2 ts2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- asserts Hmem': (mem (event_start t0) log).
           { rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [assumption|congruence]. }
           asserts Hnend: (~mem (event_end t0) log).
           { intros contra. apply Hnmem. rew_listx*. }
           asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
           { apply (Hdrunning t0). split; assumption. }
           exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              asserts (e3 & h3 & ts3 & Hbinds'): (exists e3 h3 ts3, binds T t (state_terminated, e3, h3, ts3)).
              { apply (Hdend t). exact contra. }
              forwards*: binds_inj Hbinds'.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (t1 & Hmem & _): (exists t1, mem (event_spawn t1 t) nil /\ ~mem (event_start t) nil).
        { apply (Hdnew t). exists e d h. assumption. }
        exact (mem_nil_inv Hmem).
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC).
      exists D TC LC. splits*.
      * (* play_log (log & event_start t) ... = (D, TC, G, LC): PlayStart is a no-op *)
        applys PlaySnoc Hplay. apply PlayStart.
      * (* Thread deltas: staging areas and commits unchanged by StepStart *)
        intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- (* t is now running; D[t] and TC[t] come from pre-step binds *)
           asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (ts' & e'' & Hbinds'): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds'.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = h). { congruence. }
           rewrite Hd, Htc. exists state_running e. apply binds_update_same.
        -- (* t0 ≠ t: unchanged *)
           forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists ts' e''. apply~ binds_update_neq.
      * introv Hmem.
        asserts*: (t \indom D).
        rew_dom.
        rew_set in Hmem. branches; auto_star.
      * introv Hmem.
        asserts*: (t \indom TC).
        rew_dom.
        rew_set in Hmem. branches; auto_star.
  - (* StepEnd: log' = log & event_end t, T' = T'[t := terminated] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay).
    unfolds do_commit. simpl in H5.
    asserts Ht: (T[t] = (state_running, te_ret r, d, h)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_ret r, d, h) in H5.
    inverts H5.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv (t1 & Hmem).
        rew_listx in Hmem. branches; [| congruence].
        asserts* Hin: (t2 \indom T). { apply* Hdspawned. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). exists (te_ret r) d h. assumption. }
      intros t2. splits.
      * introv (t1 & Hmem & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). exists t1. splits.
          - assumption.
          - intros contra. apply Hnmem. rew_listx*. }
        exists e2 h2 ts2.
        apply~ binds_update_neq.
        apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards~ Hbinds'': binds_update_neq_inv Hbinds'.
        asserts (t1 & Hmemsp & Hnmemst): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        exists t1. rew_listx. splits.
        -- left. assumption.
        -- intros contra. rew_listx in contra. destruct contra; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). exists (te_ret r) d h. assumption. }
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq].
        -- asserts Hneq: (t0 <> t).
           { intros ->. exact (Henmem Hmem). }
           asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t0 (state_terminated, e2, h2, ts2)).
           { apply (Hdend t0). exact Hmem. }
           exists e2 h2 ts2. apply~ binds_update_neq. apply~ binds_update_neq.
        -- inverts Heq. exists (te_ret r) (empty : staging_area) h'. apply binds_update_same.
      * introv (e2 & h2 & ts2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds. rew_listx*.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
           rew_listx. left. apply (Hdend t0). exists e2 h2 ts2. exact Hbinds2.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hneq: (t0 <> t).
        { intros ->. apply Hnmem. rew_listx*. }
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        exists e2 d2 h2. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds2. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & _): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply (Hdrunning t). eauto. }
        exact (mem_nil_inv Hmem).
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = h). { congruence. }
      exists (D[t := empty]) (TC[t := h']) LC. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayEnd _ _ _ _ _ h h' d); auto.
        -- apply HdomTC in Htin. erewrite* binds_eq_indom_read.
        -- apply HdomD in Htin. erewrite* binds_eq_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: (D[t := empty][t] = empty). { rew_map*. }
           asserts Htc_new: (TC[t := h'][t] = h'). { rew_map*. }
           rewrite Hd_new, Htc_new.
           exists state_terminated (te_ret r). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           forwards~ Hin2: indom_update_inv Hin1.
           destruct Hin2 as [->|Hin2]. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin2.
           asserts Hd0: (D[t := empty][t0] = D[t0]). { rew_map*. }
           asserts Htc0: (TC[t := h'][t0] = TC[t0]). { rew_map*. }
           rewrite Hd0, Htc0.
           exists ts' e''. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv Hmem.
        asserts*: (t \indom D).
        rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
      * introv Hmem.
        asserts*: (t \indom TC).
        rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
  - (* StepReadLocal: log' = log & event_read t i v, T' = T[t := running K(v)] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay).
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv (t3 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply (Hdspawned t2). eauto. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply (Hdspawned t2). autos. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply (Hdspawned t). autos. }
           exists. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (t1 & Hmem & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). exists t1.
          constructor. assumption. intros contra. apply Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmemsp & Hnmemst): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        exists t1. rew_listx. constructor.
        -- left. assumption.
        -- intros contra. rew_listx in contra. destruct contra; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t0 (state_terminated, e2, h2, ts2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2 ts2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & _): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply (Hdrunning t). eauto. }
        exact (mem_nil_inv Hmem).
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC).
      exists D TC LC. splits*.
      * applys PlaySnoc Hplay. apply PlayRead.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = h). { congruence. }
           rewrite Hd, Htc.
           exists state_running (te_exp (K (ret_val v))). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists ts' e''. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem.
        branches; auto_star.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem.
        branches; auto_star.
  - (* StepReadGlobal: log' = log & event_read t i v, T' = T[t := running K(v)] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay).
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv (t3 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply (Hdspawned t2). eauto. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply (Hdspawned t2). autos. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply (Hdspawned t). autos. }
           exists. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (t1 & Hmem & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). exists t1.
          constructor. assumption. intros contra. apply Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmemsp & Hnmemst): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        exists t1. rew_listx. constructor.
        -- left. assumption.
        -- intros contra. rew_listx in contra. destruct contra; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t0 (state_terminated, e2, h2, ts2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2 ts2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & _): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply (Hdrunning t). eauto. }
        exact (mem_nil_inv Hmem).
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC).
      exists D TC LC. splits*.
      * applys PlaySnoc Hplay. apply PlayRead.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = h). { congruence. }
           rewrite Hd, Htc.
           exists state_running (te_exp (K (ret_val v))). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists ts' e''. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. branches; auto_star.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. branches; auto_star.
  - (* StepWrite: log' = log & event_write t i v, T' = T[t := running K(void)] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay).
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv (t3 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply (Hdspawned t2). eauto. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply (Hdspawned t2). autos. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply (Hdspawned t). autos. }
           exists. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (t1 & Hmem & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). exists t1.
          constructor. assumption. intros contra. apply Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmemsp & Hnmemst): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        exists t1. rew_listx. constructor.
        -- left. assumption.
        -- intros contra. rew_listx in contra. destruct contra; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t0 (state_terminated, e2, h2, ts2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2 ts2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & _): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply (Hdrunning t). eauto. }
        exact (mem_nil_inv Hmem).
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds.  }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = h). { congruence. }
      exists (D[t := d[i := v]]) TC LC. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayWrite _ _ _ _ _ _ _ d).
        asserts* Hmem: (t \indom T).
        erewrite* binds_eq_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: ((D[t := d[i:=v]])[t] = d[i:=v]). { rew_map*. }
           rewrite Hd_new, Htc.
           exists state_running (te_exp (K void)). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin'.
           asserts Hd0: ((D[t := d[i:=v]])[t0] = D[t0]). { rew_map*. }
           rewrite Hd0.
           exists ts' e''. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. branches; auto_star.
  - (* StepSpawn: log' = log & event_spawn t t', T' = T'[t := ...][t' := new] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay).
    asserts* Hneq: (t' <> t).
    unfolds push_thread, do_commit. simpl in H7.
    rewrite~ read_update_neq in H7. rewrite~ read_update_same in H7.
    rewrite~ read_update_neq in H7. rewrite~ read_update_same in H7.
    inverts H7.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      asserts Hdom: (dom (T[t:=(state_running, te_exp (K t'), d, h)]
                      [t':=(state_new, te_exp e', \{}, 0)]
                      [t:=(state_running, te_exp (K t'), \{}, h')]
                      [t':=(state_new, te_exp e', \{}, h')]) =
                    (union (union (dom T) (single t')) (single t))).
                    { rewrite (dom_update t' (state_new, te_exp e', \{}, h')
                                             (T[t:=(state_running, te_exp (K t'), d, h)]
                                               [t':=(state_new, te_exp e', \{}, 0)]
                                               [t:=(state_running, te_exp (K t'), \{}, h')])).
                      rewrite dom_update. rewrite dom_update. rewrite dom_update.
                      rew_set. intros x. rew_set. splits*. }
      replace (dom (T[t:=(state_running, te_exp (K t'), d, h)]
                      [t':=(state_new, te_exp e', \{}, 0)]
                      [t:=(state_running, te_exp (K t'), \{}, h')]
                      [t':=(state_new, te_exp e', \{}, h')])) with
               (union (union (dom T) (single t')) (single t)).
      rew_set.
      splits.
      * introv (t1 & Hmem).
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [|inverts Heq; autos*].
        asserts* Hin: (t2 \indom T). { apply* Hdspawned. }
        autos.
      * intros Hin. repeat branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst. exists t. rew_listx*.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
    + (* 2. New threads *)
      asserts Hnospawn: (~exists t1, mem (event_spawn t1 t') log).
      { intros (t1 & Hmem). apply H5. apply (Hdspawned t'). eauto. }
      asserts Hnostart: (~mem (event_start t') log).
      { intros Hmemst.
        false Hnospawn.
        asserts (l1 & l2 & ->): (exists l1 l2, log = l1 ++ event_start t' :: l2).
        { apply~ mem_inv_middle. }
        forwards* (t1 & Hmem): Hspawn.
        exists t1. rew_listx*. }
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (t1 & Hmem & Hnmem).
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq].
        -- asserts Hneq2: (t2 <> t').
           { intros ->. false Hnospawn. eauto. }
           asserts Hneq3: (t2 <> t).
           { intros ->. false Hnmem. rew_listx*. }
           asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
           { apply (Hdnew t2). exists t1. constructor.
             - assumption.
             - intros contra. apply Hnmem. rew_listx*. }
           exists e2 h2 ts2.
           apply~ binds_update_neq. apply~ binds_update_neq.
           apply~ binds_update_neq. apply~ binds_update_neq.
        -- inverts Heq.
           exists (te_exp e') (empty : staging_area) h'. apply binds_update_same.
      * introv (e2 & h2 & ts2 & Hbinds).
        destruct (classic (t2 = t')) as [->|Hneq2].
        -- exists t. constructor.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq].
              ** false Hnostart. exact contra.
              ** congruence.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           destruct (classic (t2 = t)) as [->|Hneq3].
           ++ apply binds_update_same_inv in Hbinds1. congruence.
           ++ forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
              forwards~ Hbinds3: binds_update_neq_inv Hbinds2.
              forwards~ Hbinds4: binds_update_neq_inv Hbinds3.
              asserts (t1 & Hmemsp & Hnmemst): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
              { apply (Hdnew t2). exists e2 h2 ts2. exact Hbinds4. }
              exists t1. constructor.
              ** rew_listx*.
              ** intros contra. rew_listx in contra. destruct contra as [contra|Heq].
                 --- apply Hnmemst. exact contra.
                 --- congruence.
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t0 (state_terminated, e2, h2, ts2)).
        { apply (Hdend t0). exact Hmem. }
        asserts Hneq': (t0 <> t').
        { intros ->. false* H5. }
        exists e2 h2 ts2.
        apply~ binds_update_neq. apply~ binds_update_neq.
        apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           destruct (classic (t0 = t)) as [->|Hneq2].
           ++ apply binds_update_same_inv in Hbinds1. congruence.
           ++ forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
              forwards~ Hbinds3: binds_update_neq_inv Hbinds2.
              forwards~ Hbinds4: binds_update_neq_inv Hbinds3.
              rew_listx. left. apply (Hdend t0). exists e2 h2 ts2. exact Hbinds4.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        asserts Hneq': (t0 <> t').
        { intros ->. false* H5. }
        destruct (classic (t0 = t)) as [->|Hneq2].
        -- exists (te_exp (K t')) (empty : staging_area) h'.
           apply~ binds_update_neq. apply binds_update_same.
        -- exists e2 d2 h2.
           apply~ binds_update_neq. apply~ binds_update_neq.
           apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           destruct (classic (t0 = t)) as [->|Hneq2].
           ++ apply binds_update_same_inv in Hbinds1.
              asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
              { apply (Hdrunning t). eauto. }
              split.
              ** rew_listx*.
              ** intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
                 exact (Hnend contra).
           ++ forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
              forwards~ Hbinds3: binds_update_neq_inv Hbinds2.
              forwards~ Hbinds4: binds_update_neq_inv Hbinds3.
              asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
              { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds4. }
              split.
              ** rew_listx*.
              ** intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
                 exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & _): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply (Hdrunning t). eauto. }
        exact (mem_nil_inv Hmem).
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = h). { congruence. }
      exists (D[t := empty][t' := empty]) (TC[t := h'][t' := h']) LC. splits*.
      * applys PlaySnoc Hplay.
        apply (PlaySpawn _ _ _ _ _ _ h h' d); auto.
        -- apply HdomTC in Htin. erewrite* binds_eq_indom_read.
        -- apply HdomD in Htin. erewrite* binds_eq_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- asserts Hd_t': ((D[t := empty][t' := empty])[t'] = empty).
           { rewrite read_update_same. auto. }
           asserts Htc_t': ((TC[t := h'][t' := h'])[t'] = h').
           { rewrite read_update_same. auto. }
           rewrite Hd_t', Htc_t'.
           exists state_new (te_exp e'). apply binds_update_same.
        -- destruct (classic (t0 = t)) as [->|Hneq2].
           ++ asserts Hd_t: ((D[t := empty][t' := empty])[t] = empty).
              { rewrite~ read_update_neq. rewrite read_update_same. auto. }
              asserts Htc_t: ((TC[t := h'][t' := h'])[t] = h').
              { rewrite~ read_update_neq. rewrite read_update_same. auto. }
              rewrite Hd_t, Htc_t.
              exists state_running (te_exp (K t')).
              apply~ binds_update_neq. apply binds_update_same.
           ++ forwards~ Hin1: indom_update_inv Hin.
              destruct Hin1 as [->|Hin1]. { congruence. }
              forwards~ Hin2: indom_update_inv Hin1.
              destruct Hin2 as [->|Hin2]. { congruence. }
              forwards~ Hin3: indom_update_inv Hin2.
              destruct Hin3 as [->|Hin3]. { congruence. }
              forwards~ Hin4: indom_update_inv Hin3.
              destruct Hin4 as [->|Hin4]. { congruence. }
              asserts Hd0: ((D[t := empty][t' := empty])[t0] = D[t0]).
              { rewrite~ read_update_neq. rewrite~ read_update_neq. }
              asserts Htc0: ((TC[t := h'][t' := h'])[t0] = TC[t0]).
              { rewrite~ read_update_neq. rewrite~ read_update_neq. }
              rewrite Hd0, Htc0.
              forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin4.
              exists ts' e''.
              apply~ binds_update_neq. apply~ binds_update_neq.
              apply~ binds_update_neq. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. rew_set. repeat (branches; auto).
      * introv Hmem.
        rew_dom.
        rew_set in Hmem.
        rew_set. repeat (branches; auto).
  - (* StepJoin: log' = log & event_join t t', T' = T[t := running K(r)] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay).
    asserts* Hneq: (t' <> t).
    unfolds pull_thread, do_merge.
    asserts Ht': (T[t'] = (state_terminated, te_ret r, empty, h')).
    { apply* read_of_binds. }
    rewrite Ht' in H8.
    asserts Ht: (T[t] = (state_running, te_exp e, d, h)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_exp e, d, h) in H8.
    inverts H8.
    apply binds_update_same_inv in H9. inverts H9.
    rewrite~ update_update.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv (t3 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply (Hdspawned t2). eauto. }
        autos.
      * intros Hin.
        asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
        { apply (Hdspawned t2). autos. }
        branches.
        -- exists. rew_listx*.
        -- subst. exists. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (t1 & Hmem & Hnmem).
        asserts Hneq2: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). exists t1.
          constructor. assumption. intros contra. apply Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq2: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmemsp & Hnmemst): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        exists t1. rew_listx. constructor.
        -- left. assumption.
        -- intros contra. rew_listx in contra. destruct contra; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t0 (state_terminated, e2, h2, ts2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        apply binds_update_inv in Hbinds.
        cases_if.
        rew_listx. left. apply (Hdend t0). exists* e2 h2 ts2.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq'].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & _): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply (Hdrunning t). eauto. }
        exact (mem_nil_inv Hmem).
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      asserts Htin': (t' \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards (ts_old' & e_old' & Hbinds_delta'): Hdelta t' Htin'.
      forwards* Heq: binds_inj H3 Hbinds_delta.
      forwards* Heq': binds_inj H5 Hbinds_delta'.
      exists D (TC[t := h'']) LC. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayJoin _ _ _ _ _ _ h h' h''); auto.
        -- inverts Heq.
           apply HdomTC in Htin.
           applys* binds_of_indom_read.
        -- inverts Heq'.
           applys* binds_of_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq_t0].
        -- asserts Hd_t: (D[t] = d). { congruence. }
           asserts Htc_t: ((TC[t := h''])[t] = h''). { rewrite read_update_same. auto. }
           rewrite Hd_t, Htc_t.
           exists state_running (te_exp (K r)). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           asserts Htc0: ((TC[t := h''])[t0] = TC[t0]). { rewrite~ read_update_neq. }
           rewrite Htc0.
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin1.
           exists ts' e''. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. branches; auto_star.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. rew_set.
        branches; auto_star.
  - (* StepLock: log' = log & event_lock t l, T' = T[t := ...], L' = L[l := held t] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay).
    unfolds pull_lock, do_merge.
    asserts Hl: (L[l] = (ls_free, h')).
    { apply* read_of_binds. }
    replace (L[l]) with (ls_free, h') in H8.
    asserts Ht: (T[t] = (state_running, te_exp e, d, h)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_exp e, d, h) in H8.
    inverts H8.
    apply binds_update_same_inv in H9. inverts H9.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv (t3 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply* (Hdspawned t2). }
        auto.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply (Hdspawned t2). autos. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply (Hdspawned t). autos. }
           exists. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (t1 & Hmem & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). exists t1.
          constructor. assumption. intros contra. apply Hnmem. rew_listx*. }
        exists e2 h2 ts2. repeat apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards~ Hbinds'': binds_update_neq_inv Hbinds'.
        asserts (t1 & Hmemsp & Hnmemst): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply (Hdnew t2). exists* e2 h2 ts2. }
        exists t1. rew_listx. constructor*.
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t0 (state_terminated, e2, h2, ts2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2 ts2. repeat apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        rewrite~ update_update in Hbinds.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2 ts2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. repeat apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        rewrite~ update_update in Hbinds.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: filter grows by event_lock t l, l now held *)
        unfold touches_lock in Hcase. subst. rew_list. split.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. inverts Heq.
           exists h'. apply binds_update_same.
        -- intros (h2 & Hbinds).
           apply binds_update_same_inv in Hbinds.
           inverts Hbinds.
           exists~ (LibList.filter (fun e => touches_lock l e) log).
      * (* l0 ≠ l: filter and L unchanged *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv (log' & Hfilt).
           forwards ((h2 & Hbinds) & Hbinds'): (Hdlock t0 l0). { exists log'. exact Hfilt. }
           exists h2. apply~ binds_update_neq.
        -- intros (h2 & Hbinds).
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           apply (Hdlock t0 l0). exists h2. exact Hbinds'.
    + (* 6. Unlocked locks *)
      asserts (Hsmem & _): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: l now held, both sides false *)
        unfold touches_lock in Hcase. subst. rew_list. split.
        -- introv [Hnil | (t0 & log' & Hfilt)].
           ++ false (last_eq_nil_inv Hnil).
           ++ apply last_eq_last_inv in Hfilt. destruct~ Hfilt as [_ Heq].
        -- introv (h2 & Hbinds).
           apply binds_update_same_inv in Hbinds. congruence.
      * (* l0 ≠ l: filter and L unchanged *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv [Hnil | (t0 & log' & Hfilt)].
           ++ false (last_eq_nil_inv Hnil).
           ++ forwards (h2 & Hbinds): (proj1 (Hdunlock l0)). { right. exists t0 log'. exact Hfilt. }
              exists h2. apply~ binds_update_neq.
        -- intros (h2 & Hbinds).
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           forwards [Hnil | (t0 & log' & Hfilt)]: (proj2 (Hdunlock l0)). { exists h2. exact Hbinds'. }
           ++ subst. false (mem_nil_inv Hsmem).
           ++ right. exists t0 log'. exact Hfilt.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta Htin.
      forwards~ Heq: binds_inj Hbinds_delta H3.
      asserts Hlin: (l \indom L). { apply* indom_of_binds. }
      forwards (ls & Hbinds_l): Hlocks Hlin.
      forwards~ Heq': binds_inj Hbinds_l H5.
      rewrite~ update_update.
      exists D (TC[t := h'']) LC. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayLock _ _ _ _ _ _ h h' h''); auto.
        -- inverts Heq.
           apply* binds_of_indom_read.
        -- inverts Heq'.
           apply* binds_of_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq_t0].
        -- asserts~ Hd_t: (D[t] = d).
           rewrite read_update_same.
           rewrite Hd_t.
           exists state_running (te_exp (K void)). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           asserts Htc0: ((TC[t := h''])[t0] = TC[t0]). { rewrite~ read_update_neq. }
           rewrite Htc0.
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin1.
           exists ts' e''. apply~ binds_update_neq.
      * intros l0 Hin.
        destruct (classic (l0 = l)) as [->|Hneq_l].
        -- forwards* HleqL: binds_inj Hbinds_l.
           asserts~ HLC_l: (LC[l] = h').
           rewrite HLC_l. exists (ls_held t). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           forwards (ls0' & Hbinds_l'): Hlocks l0 Hin1.
           exists ls0'. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom. rew_set in Hmem. branches; auto_star.
      * introv Hmem. rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
      * introv Hmem. rew_dom.
        rew_set in Hmem. branches; auto_star.
  - (* StepRelease: log' = log & event_unlock t l, T' = T[t := ...], L' = L'[l := free] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay).
    unfolds push_lock, do_commit.
    asserts Ht: (T[t] = (state_running, te_exp e, d, h)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_exp e, d, h) in H7.
    asserts Hl: (L[l] = (ls_held t, h')).
    { apply* read_of_binds. }
    replace (L[l]) with (ls_held t, h') in H7.
    inverts H7.
    rewrite~ update_update.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv (t3 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply* (Hdspawned t2). }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply (Hdspawned t2). autos. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply (Hdspawned t). autos. }
           exists. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (t1 & Hmem & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). exists t1.
          constructor. assumption. intros contra. apply Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmemsp & Hnmemst): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        exists t1. rew_listx. constructor.
        -- left. assumption.
        -- intros contra. rew_listx in contra. destruct contra; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t0 (state_terminated, e2, h2, ts2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2 ts2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: filter gains event_unlock; l now free → locked is false *)
        unfold touches_lock in Hcase. subst. rew_list. split.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- intros (h2 & Hbinds).
           apply binds_update_same_inv in Hbinds. congruence.
      * (* l0 ≠ l: two layers of update, both at l ≠ l0 *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv (log' & Hfilt).
           forwards (h2 & Hbinds): (proj1 (Hdlock t0 l0)). { exists log'. exact Hfilt. }
           exists h2. apply~ binds_update_neq. apply~ binds_update_neq.
        -- intros (h2 & Hbinds).
           forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
           apply (Hdlock t0 l0). exists h2. exact Hbinds2.
    + (* 6. Unlocked locks *)
      asserts (Hsmem & _): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      rewrite~ update_update.
      intros l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: filter gains event_unlock t l; l now free → unlocked is true *)
        unfold touches_lock in Hcase. subst. rew_list. split.
        -- introv [Hnil | (t0 & log' & Hfilt)].
           ++ false (last_eq_nil_inv Hnil).
           ++ exists h''. apply binds_update_same.
        -- intros (h2 & Hbinds).
           right. exists t (LibList.filter (fun e => touches_lock l e) log). reflexivity.
      * (* l0 ≠ l: two layers of update, both at l ≠ l0 *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv [Hnil | (t0 & log' & Hfilt)].
           ++ false (last_eq_nil_inv Hnil).
           ++ forwards (h2 & Hbinds): (proj1 (Hdunlock l0)). { right. exists t0 log'. exact Hfilt. }
              exists h2. apply~ binds_update_neq.
        -- intros (h2 & Hbinds).
           forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           forwards [Hnil | (t0 & log' & Hfilt)]: (proj2 (Hdunlock l0)). { exists h2. exact Hbinds1. }
           ++ subst. false (mem_nil_inv Hsmem).
           ++ right. exists t0 log'. exact Hfilt.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC).
      apply binds_update_same_inv in H8. inverts H8.
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta Htin.
      forwards~ Heq: binds_inj  H3 Hbinds_delta.
      asserts Hlin: (l \indom L). { apply* indom_of_binds. }
      forwards (ls & Hbinds_l): Hlocks Hlin.
      forwards~ Heq': binds_inj H5 Hbinds_l.
      exists (D[t := empty]) (TC[t := h'']) (LC[l := h'']). splits*.
      * applys PlaySnoc Hplay.
        apply (PlayUnlock _ _ _ _ _ _ h h'' d); auto.
        -- inverts Heq.
           apply* binds_of_indom_read.
        -- inverts Heq.
           apply* binds_of_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq_t0].
        -- repeat rewrite read_update_same.
           exists state_running (te_exp (K void)). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           repeat rewrite~ read_update_neq.
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin1.
           exists ts' e''. apply~ binds_update_neq.
      * intros l0 Hin.
        destruct (classic (l0 = l)) as [->|Hneq_l].
        -- rewrite read_update_same.
           exists (ls_free). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           forwards~ Hin2: indom_update_inv Hin1.
           destruct~ Hin2 as [->|Hin2].
           forwards (ls0' & Hbinds_l'): Hlocks l0 Hin2.
           rewrite~ read_update_neq.
           exists ls0'. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom. rew_set in Hmem. rew_set.
        branches; auto.
      * introv Hmem.
        rew_dom. rew_set in Hmem. rew_set.
        branches; auto.
      * introv Hmem.
        rew_dom. rew_set in Hmem. rew_set.
        branches; auto_star.
Qed.
