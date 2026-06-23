From Vcm Require Import Common.
From Vcm Require Import Linear.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.

Import Linear.
Import Log.
Import LogFacts.

Definition describes (log : log) (cfg : cfg) : Prop :=
  match cfg with
  | (T, H, L) =>
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
          mem (event_start t) log /\ ~mem (event_end t) log <-> exists e h ts, binds T t (state_running, e, h, ts))
      /\
      (* Locked locks are locked *)
      (forall t l,
          (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t l) <-> binds L l (ls_held t))
      /\
      (* Unlocked locks are unlocked or untouched *)
      (forall l,
          (log = nil \/ exists t log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t l) <-> binds L l ls_free)
      /\
      (* TODO: Each location in the heap consists of pushed values *)
      (* TODO: Do we need timestamps in the events or can we reconstruct them? We should probably define play_event like for branching and "run it backwards" to see what the latest value is *)
      True
      /\
      (* TODO: Each staging area contains unpushed writes *)
      True
  end.

(* TODO: Do we need something about timestamps? *)

Inductive step : (cfg * log) -> (cfg * log) -> Prop :=
| StepStart : forall T T' H L L' t e h ts log,
    binds T t (state_new, e, empty, 0) ->
    pull t (T, H, L) (T', H, L') ->
    binds T' t (state_new, e, h, ts) ->
    step ((T, H, L), log) ((T'[t := (state_running, e, h, ts)], H, L), log & event_start t)
| StepEnd : forall T T' H H' L t r h ts ts' log,
    binds T t (state_running, te_ret r, h, ts) ->
    push t (T, H, L) (T', H', L) ->
    binds T' t (state_running, te_ret r, empty, ts') ->
    step ((T, H, L), log) ((T[t := (state_terminated, te_ret r, empty, ts')], H, L), log & event_end t)
| StepReadLocal : forall T H L t e h ts K i v log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_read i) ->
    binds h i v ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K (ret_val v)), h, ts)], H, L), log & event_read t i v)
| StepReadGlobal : forall T H L t e h ts K i v log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_read i) ->
    i \notindom h ->
    is_latest_value H i v ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K (ret_val v)), h, ts)], H, L), log & event_read t i v)
| StepWrite : forall T H L t e h ts K i v log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_write i v) ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void), h[i := v], ts)], H, L), log & event_write t i v)
| StepSpawn : forall T T' H H' L t (t' : tid) e h ts ts' K e' log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_spawn e') ->
    push t (T, H, L) (T', H', L) ->
    t' \notindom T' ->
    binds T' t (state_running, te_exp e, empty, ts') ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K t'), empty, ts')][t' := (state_new, te_exp e', empty, 0)], H', L), log & event_spawn t t')
| StepJoin : forall T T' H L t t' e h h' ts ts' ts'' K r log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, h', ts') ->
    pull t (T, H, L) (T', H, L) ->
    binds T' t (state_running, te_exp e, h, ts'') ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K r), h, ts'')], H, L), log & event_join t t')
| StepLock : forall T T' H L t e h ts ts' K l log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_lock l) ->
    binds L l ls_free ->
    pull t (T, H, L) (T', H, L) ->
    binds T' t (state_running, te_exp e, h, ts') ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void), h, ts')], H, L[l := ls_held t]), log & event_lock t l)
| StepRelease : forall T T' H H' (L : locks) t e h ts ts' K l log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t) ->
    push t (T, H, L) (T', H', L) ->
    binds T' t (state_running, te_exp e, empty, ts') ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void), empty, ts')], H', L[l := ls_free]), log & event_unlock t l)
.

Hint Constructors step Linear.step : vcm.

Theorem step_equiv :
  forall cfg cfg' log,
    (exists log', step (cfg, log) (cfg', log')) <-> Linear.step cfg cfg'.
Proof.
  introv. split; introv Hstep.
  - destruct Hstep as (log' & Hstep). inverts* Hstep.
  - inverts* Hstep.
    + exists. applys* StepReadLocal.
    + exists. applys* StepReadGlobal.
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

