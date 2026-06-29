From Vcm Require Import Common.

Inductive event :=
| event_spawn (t1 t2 : tid)
| event_join (t1 t2 : tid)
| event_read (t : tid) (x : var) (v : val)
| event_write (t : tid) (x : var) (v : val)
| event_lock (t : tid) (l : lid)
| event_unlock (t : tid) (l : lid)
| event_start (t : tid)
| event_end (t : tid)
.

Definition get_thread (e : event) :=
  match e with
  | event_spawn t _
  | event_join t _
  | event_read t _ _
  | event_write t _ _
  | event_lock t _
  | event_unlock t _
  | event_start t
  | event_end t => t
  end.

Definition touches_lock (l : lid) (e : event) :=
  match e with
  | event_lock _ l'
  | event_unlock _ l' => l = l'
  | _ => False
  end.

Definition writes_variable (x : var) (e : event) :=
  match e with
  | event_write _ y _ => x = y
  | _ => False
  end.

Definition is_write (e : event) :=
  match e with
  | event_write _ _ _ => True
  | _ => False
  end.

(* An event reads or writes a variable. *)
Definition accesses_variable (x : var) (e : event) :=
  match e with
  | event_read _ y _
  | event_write _ y _ => x = y
  | _ => False
  end.

Definition log := list event.

Inductive hb (log : log) : nat -> nat -> Prop :=
| HbPo : forall m n e1 e2,
    (* Events are ordered within a thread *)
    LibList.Nth m log e1 ->
    LibList.Nth n log e2 ->
    get_thread e1 = get_thread e2 ->
    m < n ->
    hb log m n
| HbLock : forall n m t1 t2 l,
    (* All lock events of a lock are ordered after preceding unlock events *)
    LibList.Nth m log (event_unlock t1 l) ->
    LibList.Nth n log (event_lock t2 l) ->
    m < n ->
    hb log m n
| HbSpawn : forall m n t1 t2,
    (* The spawn event of a thread is before its start event *)
    LibList.Nth m log (event_spawn t1 t2) ->
    LibList.Nth n log (event_start t2) ->
    m < n ->
    hb log m n
| HbJoin : forall m n t1 t2,
    (* The end event of a thread is before its join event(s) *)
    LibList.Nth m log (event_end t2) ->
    LibList.Nth n log (event_join t1 t2) ->
    m < n ->
    hb log m n
| HbTrans : forall m n k,
    (* Transitivity *)
    hb log m k ->
    hb log k n ->
    hb log m n
.

Inductive wf_lock_log : log -> Prop :=
| WfLockEmpty :
  wf_lock_log nil
| WfLockSingle :
  forall t l,
    wf_lock_log (event_lock t l :: nil)
| WfLockUnlock :
  forall t1 l log,
    wf_lock_log log ->
    wf_lock_log (event_lock t1 l :: event_unlock t1 l :: log)
.

Definition wf_log (log : log) : Prop :=
  (* Unique spawns *)
  (forall l1 l2 t1 t2,
      log = l1 ++ event_spawn t1 t2 :: l2 ->
      (~exists t1', mem (event_spawn t1' t2) (l1 ++ l2)))
  /\
  (* Unique starts *)
  (forall l1 l2 t,
      log = l1 ++ event_start t :: l2 ->
      (~mem (event_start t) (l1 ++ l2)))
  /\
  (* Threads start after spawning, or are initialised (the root) *)
  (forall l1 l2 t2,
      log = l1 ++ event_start t2 :: l2 ->
      (exists t1, mem (event_spawn t1 t2) l1) \/ t2 = t_root)
  /\
  (* Threads are joined after ending *)
  (forall l1 l2 t1 t2,
      log = l1 ++ event_join t1 t2 :: l2 ->
      mem (event_end t2) l1)
  /\
  (* Threads start by starting (the init event needs no prior start) *)
  (forall l1 l2 e t,
      log = l1 ++ e :: l2 ->
      get_thread e = t ->
      e <> event_start t ->
      mem (event_start t) l1)
  /\
  (* Threads end by ending *)
  (forall l1 l2 t,
      log = l1 ++ event_end t :: l2 ->
      LibList.Forall (fun e => get_thread e <> t) l2)
  /\
  (* Locks are locked and unlocked, in that order, by the same thread *)
  (forall l,
      wf_lock_log (LibList.filter (fun e => touches_lock l e) log)
  )
  /\
  (* A non-empty log starts with the root thread's start event.  This both
     places the root start first and guarantees it is present at all. *)
  (log <> nil -> exists l, log = event_start t_root :: l)
  /\
  (* The root thread is never spawned *)
  (forall t1, ~ mem (event_spawn t1 t_root) log)
.

(* A write to [x] happens-before any later access (read or write) of [x]. This
   rules out both write-write and (stale) read-write races on a variable. *)
Definition conflict_free (log : log) : Prop :=
  forall m n t1 x v1 e2,
    LibList.Nth m log (event_write t1 x v1) ->
    LibList.Nth n log e2 ->
    accesses_variable x e2 ->
    m < n ->
    hb log m n
.

(* The events that commit a thread's delta, making its local changes visible to
   other threads ("sync out"). These are exactly the source events of every
   cross-thread happens-before edge. *)
Definition is_commit_event (e : event) : Prop :=
  match e with
  | event_unlock _ _
  | event_spawn _ _
  | event_end _ => True
  | _ => False
  end.

(* The events that merge other threads' changes in without committing the
   thread's own delta. These keep the delta intact. *)
Definition is_merge_event (e : event) : Prop :=
  match e with
  | event_lock _ _
  | event_join _ _ => True
  | _ => False
  end.
