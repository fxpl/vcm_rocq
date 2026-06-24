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
| PlayLockFresh :
  (* A never-acquired lock ([l] not in [LC]) has no prior commit to merge with;
     it just records the locker's current commit so [LC] tracks [L]. *)
  forall D TC G LC t l,
    t \indom TC ->
    l \notindom LC ->
    play_event (event_lock t l) (D, TC, G, LC) (D, TC, G, LC[l := TC[t]])
| PlayInit :
  forall D TC G LC t,
    commit_fresh G root_commit ->
    play_event (event_init t) (D, TC, G, LC) (D[t := empty], TC[t := root_commit], graph_root G root_commit, LC)
.

(* [play_log] additionally produces a commit history [CH], a list parallel to the
   log: [CH[k]] is the commit pointer of [get_thread (event k)] right after event
   k. This records, per event, the commit the acting thread is at, which lets us
   relate the log's happens-before order to the commit graph's ancestry. *)
Inductive play_log : log -> (deltas * commits * graph * lcommits) -> (deltas * commits * graph * lcommits) -> list commit -> Prop :=
| PlayNil :
  forall D TC G LC,
    play_log nil (D, TC, G, LC) (D, TC, G, LC) nil
| PlaySnoc :
  forall E log D D' D'' TC TC' TC'' G G' G'' LC LC' LC'' CH,
    play_log log (D, TC, G, LC) (D', TC', G', LC') CH ->
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    play_log (log & E) (D, TC, G, LC) (D'', TC'', G'', LC'') (CH & TC''[get_thread E])
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

Definition describes (log : log) (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      (* Spawned threads exist *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log <-> t2 \indom T)
      /\
      (* Spawned threads that have not started are new *)
      (* TODO: Order of exists variables are wrong *)
      (forall t2,
          ((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log) /\ ~mem (event_start t2) log <-> exists e h ts, binds T t2 (state_new, e, h, ts))
      /\
      (* Ended threads are ended, with empty staging areas *)
      (forall t,
          mem (event_end t) log <-> exists e h, binds T t ((state_terminated, e, empty_staging_area, h)))
      /\
      (* Started threads that are not ended are running *)
      (forall t,
          mem (event_start t) log /\ ~mem (event_end t) log <-> exists e d h, binds T t (state_running, e, d, h))
      /\
      (* Locked locks are locked *)
      (forall t l,
          (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t l) <-> exists h, binds L l (ls_held t, h))
      /\
      (* A lock is free exactly when its last touch is an unlock.  A never-touched
         lock is not in [L] at all (so neither this nor the locked clause binds it). *)
      (forall l,
          (exists t log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t l) <-> exists h, binds L l (ls_free, h))
      /\
      (* Replaying the log produces the commit graph, staging areas and lock/thread commits *)
      (exists D TC LC CH,
          play_log log (empty, empty, empty_graph, empty) (D, TC, G, LC) CH /\
            (forall t, t \indom T -> exists ts e, binds T t (ts, e, D[t], TC[t])) /\
            (forall l, l \indom L -> exists ls, binds L l (ls, LC[l])) /\
            (forall t, t \indom T -> t \indom D) /\
            (forall t, t \indom T -> t \indom TC) /\
            (forall l, l \indom L -> l \indom LC) /\
            (forall l, l \indom LC -> l \indom L))
      /\
      (* The log has the initialisation event *)
      (exists t, mem (event_init t) log)
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
| StepLockFresh : forall T G L t e d h K l log,
    (* A never-acquired lock has no prior critical section to merge with. *)
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    l \notindom L ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K void), d, h)], G, L[l := (ls_held t, h)]), log & event_lock t l)
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

Definition wf_cfg (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      wf_graph G /\
      (forall t ts e d c, binds T t (ts, e, d, c) -> graph_indom G c) /\
      (forall l ls c, binds L l (ls, c) -> graph_indom G c)
  end.
