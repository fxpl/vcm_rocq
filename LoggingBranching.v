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
  forall D TC C P LC t c c' d,
    binds TC t c ->
    c' \notindom C ->
    binds D t d ->
    play_event (event_end t) (D, TC, (C, P), LC) (D[t := empty], TC[t := c'], (C[c' := d], \{(c, c')} \u P), LC)
| PlaySpawn :
  forall D TC C P LC t1 t2 c c' d,
    binds TC t1 c ->
    c' \notindom C ->
    binds D t1 d ->
    play_event (event_spawn t1 t2) (D, TC, (C, P), LC) (D[t1 := empty][t2 := empty], TC[t1 := c'][t2 := c'], (C[c' := d], \{(c, c')} \u P), LC)
| PlayJoin :
  forall D TC C P LC t1 t2 c1 c2 c',
    binds TC t1 c1 ->
    binds TC t2 c2 ->
    c' \notindom C ->
    play_event (event_join t1 t2) (D, TC, (C, P), LC) (D, TC[t1 := c'], (C[c' := empty], \{(c1, c')} \u \{(c2, c')} \u P), LC)
| PlayLock :
  forall D TC C P LC t l c1 c2 c',
    binds TC t c1 ->
    binds LC l c2 ->
    c' \notindom C ->
    play_event (event_lock t l) (D, TC, (C, P), LC) (D, TC[t := c'], (C[c' := empty], \{(c1, c')} \u \{(c2, c')} \u P), LC)
| PlayUnlock :
  forall D TC C P LC t l c c' d,
    binds TC t c ->
    c' \notindom C ->
    binds D t d ->
    play_event (event_unlock t l) (D, TC, (C, P), LC) (D[t := empty], TC[t := c'], (C[c' := d], \{(c, c')} \u P), LC[l := c'])
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
            (forall l, l \indom L -> exists ls, binds L l (ls, LC[l])))

(*      (* Deltas are uncommitted writes *)
      (forall t ts e d h,
          binds T t (ts, e, d, h) -> d = find_write (get_uncommitted t log)
      )*)
  end.

Inductive step : (cfg * log) -> (cfg * log) -> Prop :=
| StepStart : forall T G L t e d h log,
    binds T t (state_new, e, d, h) ->
    step ((T, G, L), log) ((T[t := (state_running, e, d, h)], G, L), log & event_start t)
| StepEnd : forall T C P L t r d h h' log,
    binds T t (state_running, te_ret r, d, h) ->
    commit_fresh (C, P) h' ->
    step ((T, (C, P), L), log) ((T[t := (state_terminated, te_ret r, empty, h')], (C[h' := d], \{(h, h')} \u P), L), log & event_end t)
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
| StepSpawn : forall T T' G G' L t (t' : tid) e d h K e' log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    push_thread t t' (T[t := (state_running, te_exp (K t'), d, h)][t' := (state_new, te_exp e', empty, 0)], G, L) (T', G', L) ->
    step ((T, G, L), log) ((T', G', L), log & event_spawn t t')
| StepJoin : forall T T' G G' L t t' e d h h' h'' K r log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, h') ->
    pull_thread t t' (T, G, L) (T', G', L) ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K r), d, h'')], G', L), log & event_join t t')
| StepLock : forall T T' G G' L t e d h h' K l log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    binds L l (ls_free, h') ->
    pull_lock t l (T, G, L) (T', G', L) ->
    binds T' t (state_running, te_exp e, d, h') ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K void), d, h')], G', L[l := (ls_held t, h')]), log & event_lock t l)
| StepRelease : forall T T' G G' (L L' : locks) t e d h h' h'' K l log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t, h'') ->
    push_lock t l (T, G, L) (T', G', L') ->
    binds T' t (state_running, te_exp e, empty, h') ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K void), empty, h')], G', L'[l := (ls_free, h')]), log & event_unlock t l)
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
Admitted.

Theorem step_preserves_describes :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    describes log' cfg'.
Admitted.

