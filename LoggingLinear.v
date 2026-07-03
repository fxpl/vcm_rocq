From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import Linear.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.

Import Linear.
Import Log.
Import LogFacts.

(* Replaying the log reconstructs the single-branch commit graph.  Compared with
   LoggingBranching's [play_event], the play state carries the GLOBAL HEAD [g] (a
   commit) in place of the per-lock commits [LC]:
     - pushes (end / spawn / unlock) commit the actor's diff *onto [g]*, producing
       a fresh commit [g'] that becomes the new head and the actor's commit;
     - pulls (start / join / lock) fast-forward the actor's commit to [g] and
       leave the graph (and head) unchanged -- there is no merge;
     - lock events need no special handling for the graph (locks carry no commit),
       so a single [PlayLock] rule suffices; [StepLock]/[StepRelease] read the
       lock state via the total [lock_read] (defaulting to [ls_free]). *)

Definition deltas := map tid diff.
Definition commits := map tid commit.
Definition init_play_cfg : deltas * commits * graph * commit :=
  (empty[t_root := empty], empty[t_root := root_commit], graph_root root_commit, root_commit).

Inductive play_event :
  event -> (deltas * commits * graph * commit) -> (deltas * commits * graph * commit) -> Prop :=
| PlayRead : forall D TC G g t x v,
    x \notin Volatiles ->
    play_event (event_read t x v) (D, TC, G, g) (D, TC, G, g)
| PlayReadVolatile : forall D TC G g t x v,
    (* a volatile read is a pull: fast-forward the actor's commit to [g],
       matching [Linear.StepReadVolatile] *)
    x \in Volatiles ->
    play_event (event_read t x v) (D, TC, G, g) (D, TC[t := g], G, g)
| PlayWrite : forall D TC G g t x v d,
    x \notin Volatiles ->
    binds D t d ->
    play_event (event_write t x v) (D, TC, G, g) (D[t := d[x := v]], TC, G, g)
| PlayWriteVolatile : forall D TC G g g' t x v d,
    (* a volatile write is a pull then push: fold the write into the diff and
       commit it immediately onto [g], matching [Linear.StepWriteVolatile] *)
    x \in Volatiles ->
    binds D t d ->
    commit_fresh G g' ->
    play_event (event_write t x v) (D, TC, G, g)
      (D[t := empty], TC[t := g'], graph_commit G g g' (d[x := v]), g')
| PlayStart : forall D TC G g t,
    play_event (event_start t) (D, TC, G, g) (D, TC[t := g], G, g)
| PlayEnd : forall D TC G g g' t d,
    binds D t d ->
    commit_fresh G g' ->
    play_event (event_end t) (D, TC, G, g) (D[t := empty], TC[t := g'], graph_commit G g g' d, g')
| PlaySpawn : forall D TC G g g' t1 t2 d,
    binds D t1 d ->
    commit_fresh G g' ->
    (* the spawned thread [t2] starts at the head [g'] as a
       placeholder, mirroring [global_commit] in [StepSpawn] *)
    play_event (event_spawn t1 t2) (D, TC, G, g)
      (D[t1 := empty][t2 := empty], TC[t1 := g'][t2 := g'], graph_commit G g g' d, g')
| PlayJoin : forall D TC G g t1 t2,
    play_event (event_join t1 t2) (D, TC, G, g) (D, TC[t1 := g], G, g)
| PlayLock : forall D TC G g t l,
    play_event (event_lock t l) (D, TC, G, g) (D, TC[t := g], G, g)
| PlayUnlock : forall D TC G g g' t l d,
    binds D t d ->
    commit_fresh G g' ->
    play_event (event_unlock t l) (D, TC, G, g) (D[t := empty], TC[t := g'], graph_commit G g g' d, g')
.

(* As in LoggingBranching, [CH] is a list parallel to the log: [CH[k]] is the
   commit pointer of the thread acting at event [k] right after it, which links
   the log's happens-before order to the graph's ancestry. *)
Inductive play_log :
  log -> (deltas * commits * graph * commit) -> (deltas * commits * graph * commit) -> list commit -> Prop :=
| PlayNil : forall D TC G g,
    play_log nil (D, TC, G, g) (D, TC, G, g) nil
| PlaySnoc : forall E log D D' D'' TC TC' TC'' G G' G'' g g' g'' CH,
    play_log log (D, TC, G, g) (D', TC', G', g') CH ->
    play_event E (D', TC', G', g') (D'', TC'', G'', g'') ->
    play_log (log & E) (D, TC, G, g) (D'', TC'', G'', g'') (CH & TC''[get_thread E])
.

Definition describes (log : log) (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, g, L) =>
      (* Spawned and inited threads exist *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root <-> t2 \indom T)
      /\
      (* Spawned/inited threads that have not started are new *)
      (forall t2,
          ((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root) /\ ~mem (event_start t2) log <-> exists e d c, binds T t2 (state_new, e, d, c))
      /\
      (* Ended threads are ended, with empty diffs *)
      (forall t,
          mem (event_end t) log <-> exists e c, binds T t (state_terminated, e, empty_diff, c))
      /\
      (* Started threads that are not ended are running *)
      (forall t,
          mem (event_start t) log /\ ~mem (event_end t) log <-> exists e d c, binds T t (state_running, e, d, c))
      /\
      (* Locked locks are locked *)
      (forall t l,
          (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t l) <-> binds L l (ls_held t))
      /\
      (* A lock is free exactly when its last touch is an unlock.  A never-touched
         lock is absent from [L] (so [StepLockFresh] introduces it). *)
      (forall l,
          (exists t log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t l) <-> binds L l ls_free)
      /\
      (* Replaying the log produces the commit graph [G] and the global head [g];
         each thread's diff and commit are the replayed [D[t]] and [TC[t]]. *)
      (exists D TC CH,
          play_log log init_play_cfg (D, TC, G, g) CH /\
            (forall t, t \indom T -> exists st e, binds T t (st, e, D[t], TC[t])) /\
            (forall t, t \indom T -> t \indom D) /\
            (forall t, t \indom T -> t \indom TC))
  end.

(* The single-branch well-formedness of a configuration, transferred from
   LoggingBranching's [wf_cfg] and strengthened with the linear-history property:
     - the commit graph is well-formed and TOTALLY ORDERED (a single chain);
     - the global head [g] is in the graph and is its maximum (every commit is an
       ancestor of [g]), so any thread can fast-forward to it;
     - every thread's commit lives in the graph.
   Locks no longer carry a commit, so (unlike Branching) there is no lock clause. *)
Definition wf_cfg (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, g, L) =>
      wf_graph G /\
      total_order G /\
      graph_indom G g /\
      (forall c, graph_indom G c -> ancestor G c g) /\
      (forall t st e d c, binds T t (st, e, d, c) -> graph_indom G c)
  end.

(* The initial configuration: a single new root thread whose commit is the graph
   root, an empty single-commit graph whose head is that root, and no locks. *)
Definition init_cfg (e : exp) : cfg :=
  (empty[t_root := (state_new, te_exp e, empty_diff, root_commit)],
   graph_root root_commit,
   root_commit,
   empty).

Inductive step : (cfg * log) -> (cfg * log) -> Prop :=
| StepStart : forall T G g L t e d c log,
    binds T t (state_new, e, d, c) ->
    step ((T, G, g, L), log) ((T[t := (state_running, e, d, g)], G, g, L), log & event_start t)
| StepEnd : forall T T' G G' g g' L t r d c log,
    binds T t (state_running, te_ret r, d, c) ->
    lin_conflict_free d c g G ->
    commit_fresh G g' ->
    global_commit t g g' T G = (T', G') ->
    step ((T, G, g, L), log) ((T'[t := (state_terminated, te_ret r, empty, g')], G', g', L), log & event_end t)
| StepReadLocal : forall T G g L t e d c K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \notin Volatiles ->
    binds d x v ->
    step ((T, G, g, L), log) ((T[t := (state_running, K (ret_val v), d, c)], G, g, L), log & event_read t x v)
| StepReadGlobal : forall T G g L t e d c K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \notin Volatiles ->
    x \notindom d ->
    is_latest_value G c x v ->
    step ((T, G, g, L), log) ((T[t := (state_running, K (ret_val v), d, c)], G, g, L), log & event_read t x v)
| StepReadVolatile : forall T G g L t e d c K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \in Volatiles ->
    lin_conflict_free d c g G ->
    is_latest_value G g x v ->
    step ((T, G, g, L), log) ((T[t := (state_running, K (ret_val v), d, g)], G, g, L), log & event_read t x v)
| StepWrite : forall T G g L t e d c K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_write x v) ->
    x \notin Volatiles ->
    step ((T, G, g, L), log) ((T[t := (state_running, K void, d[x := v], c)], G, g, L), log & event_write t x v)
| StepWriteVolatile : forall T T' G G' g g' L t e d c K x v log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_write x v) ->
    x \in Volatiles ->
    lin_conflict_free (d[x := v]) c g G ->
    commit_fresh G g' ->
    global_commit t g g' (T[t := (state_running, te_exp e, d[x := v], c)]) G = (T', G') ->
    step ((T, G, g, L), log) ((T'[t := (state_running, K void, empty, g')], G', g', L), log & event_write t x v)
| StepSpawn : forall T T' G G' g g' L t (t' : tid) e d c K e' log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    lin_conflict_free d c g G ->
    commit_fresh G g' ->
    global_commit t g g' (T[t := (state_running, K t', d, c)][t' := (state_new, te_exp e', empty, g')]) G = (T', G') ->
    step ((T, G, g, L), log) ((T', G', g', L), log & event_spawn t t')
| StepJoin : forall T G g L t t' e d c c' K r log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, c') ->
    lin_conflict_free d c g G ->
    step ((T, G, g, L), log) ((T[t := (state_running, K r, d, g)], G, g, L), log & event_join t t')
| StepLock : forall T G g L t e d c K l log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_lock l) ->
    lock_read L l = ls_free ->
    lin_conflict_free d c g G ->
    step ((T, G, g, L), log) ((T[t := (state_running, K void, d, g)], G, g, L[l := ls_held t]), log & event_lock t l)
| StepRelease : forall T T' G G' g g' (L : locks) t e d c K l log,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_unlock l) ->
    lock_read L l = ls_held t ->
    lin_conflict_free d c g G ->
    commit_fresh G g' ->
    global_commit t g g' T G = (T', G') ->
    step ((T, G, g, L), log) ((T'[t := (state_running, K void, empty, g')], G', g', L[l := ls_free]), log & event_unlock t l)
.

Hint Constructors step LoggingLinear.step : vcm.
