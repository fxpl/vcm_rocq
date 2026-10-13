From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Branching.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.

Import Graph.
Import GraphFacts.
Import Branching.
Import Log.
Import LogFacts.

(* Branching augmented with an execution log ([Log.v]) recording every step
   as an event. [play_log] replays a log back into a commit graph and set of
   branches on its own, independently of any live configuration, and
   [describes] characterises a configuration by requiring it to be exactly
   what replaying its own log produces. *)

Definition deltas := map tid diff.
Definition commits := map tid commit.
Definition lcommits := map lid commit.
Definition init_play_cfg : deltas * commits * graph * lcommits * volatiles :=
  (empty[t_root := empty], empty[t_root := root_commit], graph_root root_commit, empty, empty).

(* A never-touched lock's commit pointer defaults to [root_commit] (mirrors
   [Branching.lock_read]'s default). *)
Definition lc_read (LC : lcommits) (l : lid) : commit :=
  read_default _ root_commit LC l.

Inductive play_event : event -> (deltas * commits * graph * lcommits * volatiles) -> (deltas * commits * graph * lcommits * volatiles) -> Prop :=
| PlayRead :
  forall D TC G LC VC t x v,
    x \notin Volatiles ->
    play_event (event_read t x v) (D, TC, G, LC, VC) (D, TC, G, LC, VC)
| PlayReadVolatile :
  (* a volatile read is a pull, matching [Branching.StepReadVolatile]: merge
     [x]'s stored commit into the acting thread's branch. *)
  forall D TC G LC VC t x v c c',
    x \in Volatiles ->
    binds TC t c ->
    commit_fresh G c' ->
    play_event (event_read t x v) (D, TC, G, LC, VC)
      (D, TC[t := c'], graph_merge G (vc_read VC x) c c', LC, VC)
| PlayWrite :
  forall D TC G LC VC t x v d,
    x \notin Volatiles ->
    binds D t d ->
    play_event (event_write t x v) (D, TC, G, LC, VC) (D[t := d[x := v]], TC, G, LC, VC)
| PlayWriteVolatile :
  (* a volatile write is a pull then push, matching
     [Branching.StepWriteVolatile]: merge [x]'s stored commit in, then
     immediately commit the whole diff (with the new write folded in) and
     record the fresh commit as [x]'s new stored commit. *)
  forall D TC G LC VC t x v d c c' c'',
    x \in Volatiles ->
    binds D t d ->
    binds TC t c ->
    commit_fresh G c' ->
    commit_fresh (graph_merge G (vc_read VC x) c c') c'' ->
    play_event (event_write t x v) (D, TC, G, LC, VC)
      (D[t := empty], TC[t := c''],
       graph_commit (graph_merge G (vc_read VC x) c c') c' c'' (d[x := v]),
       LC, VC[x := c''])
| PlayStart :
  forall D TC G LC VC t,
    play_event (event_start t) (D, TC, G, LC, VC) (D, TC, G, LC, VC)
| PlayEnd :
  forall D TC G LC VC t c c' d,
    binds TC t c ->
    commit_fresh G c' ->
    binds D t d ->
    play_event (event_end t) (D, TC, G, LC, VC) (D[t := empty], TC[t := c'], graph_commit G c c' d, LC, VC)
| PlaySpawn :
  forall D TC G LC VC t1 t2 c c' d,
    binds TC t1 c ->
    commit_fresh G c' ->
    binds D t1 d ->
    play_event (event_spawn t1 t2) (D, TC, G, LC, VC) (D[t1 := empty][t2 := empty], TC[t1 := c'][t2 := c'], graph_commit G c c' d, LC, VC)
| PlayJoin :
  forall D TC G LC VC t1 t2 c1 c2 c',
    binds TC t1 c1 ->
    binds TC t2 c2 ->
    commit_fresh G c' ->
    play_event (event_join t1 t2) (D, TC, G, LC, VC) (D, TC[t1 := c'], graph_merge G c2 c1 c', LC, VC)
| PlayLock :
  forall D TC G LC VC t l c1 c',
    binds TC t c1 ->
    commit_fresh G c' ->
    play_event (event_lock t l) (D, TC, G, LC, VC) (D, TC[t := c'], graph_merge G (lc_read LC l) c1 c', LC, VC)
| PlayUnlock :
  forall D TC G LC VC t l c c' d,
    binds TC t c ->
    commit_fresh G c' ->
    binds D t d ->
    play_event (event_unlock t l) (D, TC, G, LC, VC) (D[t := empty], TC[t := c'], graph_commit G c c' d, LC[l := c'], VC)
.

(* [play_log] additionally produces a commit history [CH], a list parallel to the
   log: [CH[k]] is the commit pointer of [get_thread (event k)] right after event
   k. This records, per event, the commit the acting thread is at, which lets us
   relate the log's happens-before order to the commit graph's ancestry. *)
Inductive play_log : log -> (deltas * commits * graph * lcommits * volatiles) -> (deltas * commits * graph * lcommits * volatiles) -> list commit -> Prop :=
| PlayNil :
  forall D TC G LC VC,
    play_log nil (D, TC, G, LC, VC) (D, TC, G, LC, VC) nil
| PlaySnoc :
  forall E log D D' D'' TC TC' TC'' G G' G'' LC LC' LC'' VC VC' VC'' CH,
    play_log log (D, TC, G, LC, VC) (D', TC', G', LC', VC') CH ->
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    play_log (log & E) (D, TC, G, LC, VC) (D'', TC'', G'', LC'', VC'') (CH & TC''[get_thread E])
.

Definition describes (log : log) (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L, V) =>
      (* Spawned threads exist *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root <-> t2 \indom T)
      /\
      (* Spawned threads that have not started are new *)
      (forall t2,
          ((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root) /\ ~mem (event_start t2) log <-> exists e d c, binds T t2 (state_new, e, d, c))
      /\
      (* Ended threads are ended, with empty staging areas *)
      (forall t,
          mem (event_end t) log <-> exists e c, binds T t ((state_terminated, e, empty_diff, c)))
      /\
      (* Started threads that are not ended are running *)
      (forall t,
          mem (event_start t) log /\ ~mem (event_end t) log <-> exists e d c, binds T t (state_running, e, d, c))
      /\
      (* Locked locks are locked *)
      (forall t l,
          (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t l) <-> exists c, binds L l (ls_held t, c))
      /\
      (* A lock is free exactly when its last touch is an unlock.  A never-touched
         lock is not in [L] at all (so neither this nor the locked clause binds it). *)
      (forall l,
          (exists t log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t l) <-> exists h, binds L l (ls_free, h))
      /\
      (* Replaying the log produces the commit graph, staging
         areas, lock/thread/volatile commits. *)
      (exists D TC LC VC CH,
          play_log log init_play_cfg (D, TC, G, LC, VC) CH /\
            (forall t, t \indom T -> exists ts e, binds T t (ts, e, D[t], TC[t])) /\
            (forall l, l \indom L -> exists ls, binds L l (ls, lc_read LC l)) /\
            VC = V /\
            (forall t, t \indom T -> t \indom D) /\
            (forall t, t \indom T -> t \indom TC) /\
            (forall l, l \indom LC -> l \indom L))
  end.

Inductive step : (cfg * log) -> (cfg * log) -> Prop :=
| StepStart : forall T G L V t e d c log,
    binds T t (state_new, e, d, c) ->
    step ((T, G, L, V), log) ((T[t := (state_running, e, d, c)], G, L, V), log & event_start t)
| StepEnd : forall T T' G G' L V t r d c c' log,
    binds T t (state_running, te_ret r, d, c) ->
    commit_fresh G c' ->
    do_commit t c' T G = (T', G') ->
    step ((T, G, L, V), log) ((T'[t := (state_terminated, te_ret r, empty, c')], G', L, V), log & event_end t)
| StepReadLocal : forall T G L V t e d c K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \notin Volatiles ->
    binds d x v ->
    step ((T, G, L, V), log) ((T[t := (state_running, K (ret_val v), d, c)], G, L, V), log & event_read t x v)
| StepReadGlobal : forall T G L V t e d c K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \notin Volatiles ->
    x \notindom d ->
    is_latest_value G c x v ->
    step ((T, G, L, V), log) ((T[t := (state_running, K (ret_val v), d, c)], G, L, V), log & event_read t x v)
| StepReadVolatile : forall T T' G G' L V t e d c c'' K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \in Volatiles ->
    conflict_free_merge d c (vc_read V x) G ->
    commit_fresh G c'' ->
    pull_volatile t x c'' T G V = (T', G') ->
    binds T' t (state_running, te_exp e, d, c'') ->
    is_latest_value G' c'' x v ->
    step ((T, G, L, V), log) ((T'[t := (state_running, K (ret_val v), d, c'')], G', L, V), log & event_read t x v)
| StepWrite : forall T G L V t e d c K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_write x v) ->
    x \notin Volatiles ->
    step ((T, G, L, V), log) ((T[t := (state_running, K void, d[x := v], c)], G, L, V), log & event_write t x v)
| StepWriteVolatile : forall T T' T'' G G' G'' L V V' t e d c c' c'' K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_write x v) ->
    x \in Volatiles ->
    conflict_free_merge d[x := v] c (vc_read V x) G ->
    commit_fresh G c' ->
    pull_volatile t x c' T G V = (T', G') ->
    binds T' t (state_running, te_exp e, d, c') ->
    commit_fresh G' c'' ->
    push_volatile t x c'' (T'[t := (state_running, te_exp e, d[x := v], c')]) G' V = (T'', G'', V') ->
    step ((T, G, L, V), log) ((T''[t := (state_running, K void, empty, c'')], G'', L, V'), log & event_write t x v)
| StepSpawn : forall T T' G G' L V t (t' : tid) e d c c' K e' log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    commit_fresh G c' ->
    push_thread t t' c' (T[t := (state_running, K t', d, c)][t' := (state_new, te_exp e', empty, 0)]) G = (T', G') ->
    step ((T, G, L, V), log) ((T', G', L, V), log & event_spawn t t')
| StepJoin : forall T T' G G' L V t t' e d c c' c'' K r log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, c') ->
    conflict_free_merge d c c' G ->
    commit_fresh G c'' ->
    pull_thread t t' c'' T G = (T', G') ->
    binds T' t (state_running, te_exp e, d, c'') ->
    step ((T, G, L, V), log) ((T'[t := (state_running, K r, d, c'')], G', L, V), log & event_join t t')
| StepLock : forall T T' G G' L V t e d c c' c'' K l log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_lock l) ->
    lock_read L l = (ls_free, c') ->
    conflict_free_merge d c c' G ->
    commit_fresh G c'' ->
    pull_lock t l c'' T G L = (T', G') ->
    binds T' t (state_running, te_exp e, d, c'') ->
    step ((T, G, L, V), log) ((T'[t := (state_running, K void, d, c'')], G', L[l := (ls_held t, c')], V), log & event_lock t l)
| StepRelease : forall T T' G G' (L L' : locks) V t e d c c' c'' K l log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t, c') ->
    commit_fresh G c'' ->
    push_lock t l c'' T G L = (T', G', L') ->
    binds T' t (state_running, te_exp e, empty, c'') ->
    step ((T, G, L, V), log) ((T'[t := (state_running, K void, empty, c'')], G', L'[l := (ls_free, c'')], V), log & event_unlock t l)
(* Failed conflict checks (see [Branching.step]): the thread receives the
   exception [ret_race] and keeps its staging area and commit; the graph and
   the log do not change. A conflict implies that the log (extended with the
   attempted write, for a volatile write) is not race free (see
   [branching_join_conflict_sound] and friends). The equivalence theorems are
   about steps that extend the log, which excludes these. *)
| StepReadVolatileConflict : forall T G L V t e d c K x log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \in Volatiles ->
    ~ conflict_free_merge d c (vc_read V x) G ->
    step ((T, G, L, V), log) ((T[t := (state_running, K ret_race, d, c)], G, L, V), log)
| StepWriteVolatileConflict : forall T G L V t e d c K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_write x v) ->
    x \in Volatiles ->
    ~ conflict_free_merge d[x := v] c (vc_read V x) G ->
    step ((T, G, L, V), log) ((T[t := (state_running, K ret_race, d, c)], G, L, V), log)
| StepJoinConflict : forall T G L V t t' e d c c' K r log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, c') ->
    ~ conflict_free_merge d c c' G ->
    step ((T, G, L, V), log) ((T[t := (state_running, K ret_race, d, c)], G, L, V), log)
| StepLockConflict : forall T G L V t e d c c' K l log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_lock l) ->
    lock_read L l = (ls_free, c') ->
    ~ conflict_free_merge d c c' G ->
    step ((T, G, L, V), log) ((T[t := (state_running, K ret_race, d, c)], G, L, V), log)
.

Hint Constructors step Branching.step : vcm.

Definition wf_cfg (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L, V) =>
      wf_graph G /\
      graph_indom G root_commit /\
      (forall t ts e d c, binds T t (ts, e, d, c) -> graph_indom G c) /\
      (forall l ls c, binds L l (ls, c) -> graph_indom G c) /\
      (forall x c, binds V x c -> graph_indom G c)
  end.

(* Initial configuration consists of a single thread with an
arbitrary expression *)
Definition init_cfg (e : exp) : cfg :=
  (empty[t_root := (state_new, te_exp e, empty_diff, root_commit)],
   graph_root root_commit,
   empty,
   empty).
