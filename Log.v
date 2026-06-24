From Vcm Require Import Common.

Inductive event :=
| event_spawn (t1 t2 : tid)
| event_join (t1 t2 : tid)
| event_read (t : tid) (i : loc) (v : val)
| event_write (t : tid) (i : loc) (v : val)
| event_lock (t : tid) (l : lid)
| event_unlock (t : tid) (l : lid)
| event_start (t : tid)
| event_end (t : tid)
| event_init (t : tid)
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
  | event_end t
  | event_init t => t
  end.

Definition touches_lock (l : lid) (e : event) :=
  match e with
  | event_lock _ l'
  | event_unlock _ l' => l = l'
  | _ => False
  end.

Definition writes_location (i : loc) (e : event) :=
  match e with
  | event_write _ j _ => i = j
  | _ => False
  end.

Definition is_write (e : event) :=
  match e with
  | event_write _ _ _ => True
  | _ => False
  end.

(* An event reads or writes location [i]. *)
Definition accesses_location (i : loc) (e : event) :=
  match e with
  | event_read _ j _
  | event_write _ j _ => i = j
  | _ => False
  end.

Definition log := list event.

(*
Inductive hb (log : log) : event -> event -> Prop :=
| HbPo : forall l1 l2 t e1 e2,
    (* Events are adjacent when projecting the program order of a thread *)
    l1 ++ e1 :: e2 :: l2 = LibList.filter (fun e => get_thread e = t) log ->
    hb log e1 e2
| HbLock : forall l1 l2 t1 t2 l,
    (* Events unlock l/lock l are adjacent when projecting the events of a lock *)
    l1 ++ event_unlock t1 l :: event_lock t2 l :: l2 =
      LibList.filter (fun e => touches_lock l e) log ->
    hb log (event_unlock t1 l) (event_lock t2 l)
| HbSpawn : forall l1 l2 t1 t2,
    (* The spawn event of a thread is before its start event *)
    (* TODO: No need to split list. Well-formedness will ensure they are ordered *)
    log = l1 ++ l2 ->
    mem (event_spawn t1 t2) l1 ->
    mem (event_start t2) l2 ->
    hb log (event_spawn t1 t2) (event_start t2)
| HbJoin : forall l1 l2 t1 t2,
    (* The end event of a thread is before its join event(s) *)
    log = l1 ++ l2 ->
    mem (event_end t2) l1 ->
    mem (event_join t1 t2) l2 ->
    hb log (event_end t2) (event_join t1 t2)
| HbTrans: forall e1 e2 e3,
    (* Transitivity *)
    hb log e1 e2 ->
    hb log e2 e3 ->
    hb log e1 e3
.
*)

Inductive hb (log : log) : nat -> nat -> Prop :=
| HbPo : forall m n t e1 e2,
    (* Events are ordered within a thread *)
    LibList.Nth m log e1 ->
    LibList.Nth n log e2 ->
    get_thread e1 = t ->
    get_thread e2 = t ->
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

  (* Alternative formulation based on length*)
  (* forall t2, length (LibList.filter (fun e => exists t1, e = event_spawn t1 t2) log) <= 1 x*)
  /\
  (* Unique starts *)
  (forall l1 l2 t,
      log = l1 ++ event_start t :: l2 ->
      (~mem (event_start t) (l1 ++ l2)))
  /\
  (* Unique ends *)
  (forall l1 l2 t,
      log = l1 ++ event_end t :: l2 ->
      (~mem (event_end t) (l1 ++ l2)))
  /\
  (* Threads start after spawning, or are initialised (the root) *)
  (forall l1 l2 t2,
      log = l1 ++ event_start t2 :: l2 ->
      (exists t1, mem (event_spawn t1 t2) l1) \/ mem (event_init t2) l1)
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
      e <> event_init t ->
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
  (* The init event initialises the root thread and is the very first event *)
  (forall l1 l2 t,
      log = l1 ++ event_init t :: l2 ->
      t = t_root /\ l1 = nil)
  /\
  (* The root thread is never spawned *)
  (forall t1, ~ mem (event_spawn t1 t_root) log)
.

(*
Definition conflict_free (log : log) : Prop :=
  forall l1 l2 t1 t2 i v1 v2,
    log = l1 ++ l2 ->
    mem (event_write t1 i v1) l1 ->
    mem (event_write t2 i v2) l2 ->
    (* mem e l2 -> *)
    (* (e = event_write t2 i v2 \/ e = event_read t2 i v2) -> *)
    hb log (event_write t1 i v1) (event_write t2 i v2)
.
*)

(* A write to [i] happens-before any later access (read or write) of [i]. This
   rules out both write-write and (stale) read-write races on a location. *)
Definition conflict_free (log : log) : Prop :=
  forall m n t1 i v1 e2,
    LibList.Nth m log (event_write t1 i v1) ->
    LibList.Nth n log e2 ->
    accesses_location i e2 ->
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

(* The log that describes the initial configuration *)
Definition init_log := event_init t_root::nil.
