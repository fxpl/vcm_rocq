From Vcm Require Import Common.

Definition thread := (thread_state * thread_exp)%type.

Definition threads := (map tid thread).
Definition heap := map var val.
Definition locks := map lid lock_state.
Definition cfg := (threads * heap * locks)%type.

(* Locks default to free: a never-acquired lock reads as [ls_free], the same
   as an explicitly-freed one. This makes [lock_read] a total read, unlike
   [Inhab]'s opaque [arbitrary], so it can be shown equal to [ls_free] when
   the lock is unbound ([read_default_notindom]). *)
Definition lock_read (L : locks) (l : lid) : lock_state :=
  read_default inhab_lock_state ls_free L l.

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T H L t e,
    binds T t (state_new, e) ->
    step (T, H, L) (T[t := (state_running, e)], H, L)
| StepEnd : forall (T : threads) H L t r,
    binds T t (state_running, te_ret r) ->
    step (T, H, L) (T[t := (state_terminated, te_ret r)], H, L)
| StepRead : forall (T : threads) H L t e K x v,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_read x) ->
    binds H x v ->
    step (T, H, L) (T[t := (state_running, K (ret_val v))], H, L)
| StepWrite : forall (T : threads) (H : heap) L t e K x v,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_write x v) ->
    step (T, H, L) (T[t := (state_running, K void)], H[x := v], L)
| StepSpawn : forall (T : threads) H L (t t' : tid) e K e',
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    step (T, H, L) (T[t := (state_running, K t')][t' := (state_new, te_exp e')], H, L)
| StepJoin : forall (T : threads) H L t t' e K r,
    (* This means multiple threads can join the same thread *)
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r) ->
    step (T, H, L) (T[t := (state_running, K r)], H, L)
| StepLock : forall (T : threads) H (L : locks) t e K l,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_lock l) ->
    lock_read L l = ls_free ->
    step (T, H, L) (T[t := (state_running, K void)], H, L[l := ls_held t])
| StepRelease : forall (T : threads) H (L : locks) t e K l,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_unlock l) ->
    lock_read L l = ls_held t ->
    step (T, H, L) (T[t := (state_running, K void)], H, L[l := ls_free])
.

(* ===================================================================== *)
(* Progress (modulo deadlock)                                            *)
(* ===================================================================== *)

(* An effect is *enabled* in the current heap [H] / locks [L] for thread [t]
   when its non-blocking precondition holds: a read must target an allocated
   variable and an unlock a lock the thread holds. Writes, spawns, joins and
   locks have no such precondition (for a join/lock, whether it can actually
   fire is the *blocking* question below). Folding enabledness into the
   underlying-language progress premise rules out the two ways a thread could
   get genuinely *stuck* without being deadlocked: reading an unallocated
   variable, or unlocking a lock it does not hold. *)
Definition enabled (H : heap) (L : locks) (t : tid) (a : eff) : Prop :=
  match a with
  | eff_read x   => x \indom H
  | eff_unlock l => lock_read L l = ls_held t
  | _ => True
  end.

(* A *blocking* effect: joining a thread that has not terminated, or acquiring a
   lock that is currently held. These are the legitimate sources of deadlock
   (locks default to free, so there is no "never acquired" case). *)
Definition blocked (T : threads) (L : locks) (a : eff) : Prop :=
  match a with
  | eff_join t'  => ~ exists r, binds T t' (state_terminated, te_ret r)
  | eff_lock l   => lock_read L l <> ls_free
  | _ => False
  end.

(* Progress for the underlying sequential language, with effect-enabledness
   folded in: every running, still-computing thread can take a [step_ul], and
   every step it can take is enabled. A thread never reduces to a [te_ret] on
   its own -- it becomes [te_ret] only as a side-effect of the concurrent
   semantics, i.e. when its continuation hands one back. *)
Definition ul_progress (cfg : cfg) : Prop :=
  match cfg with
  | (T, H, L) =>
      forall t e,
        binds T t (state_running, te_exp e) ->
        (exists K a, step_ul e K a) /\
        (forall K a, step_ul e K a -> enabled H L t a)
  end.

(* A thread has terminated. *)
Definition terminated (cfg : cfg) (t : tid) : Prop :=
  match cfg with
  | (T, _, _) => exists r, binds T t (state_terminated, te_ret r)
  end.

(* A running thread is *inert* when it is still computing, can take a step, but
   every step it can take is blocked (a join on a non-terminated thread, or a
   lock on a held lock). *)
Definition inert (cfg : cfg) (t : tid) : Prop :=
  match cfg with
  | (T, _, L) =>
      exists e,
        binds T t (state_running, te_exp e) /\
        (exists K a, step_ul e K a) /\
        (forall K a, step_ul e K a -> blocked T L a)
  end.

(* Well-formedness: a terminated thread always carries a return value (it became
   terminated only via [StepEnd], whose continuation handed one back). This rules
   out the otherwise-stuck [(state_terminated, te_exp _)] thread in progress. *)
Definition wf_cfg (cfg : cfg) : Prop :=
  match cfg with
  | (T, _, _) => forall t e, binds T t (state_terminated, e) -> exists r, e = te_ret r
  end.

(* The configuration is *done* when every thread has terminated. *)
Definition done (cfg : cfg) : Prop :=
  match cfg with
  | (T, _, _) => forall t, t \indom T -> terminated cfg t
  end.

(* The configuration is *deadlocked* when every thread is terminated or inert,
   and at least one thread is inert (so [deadlocked] is disjoint from [done]). *)
Definition deadlocked (cfg : cfg) : Prop :=
  match cfg with
  | (T, _, _) =>
      (forall t, t \indom T -> terminated cfg t \/ inert cfg t) /\
      (exists t, t \indom T /\ inert cfg t)
  end.
