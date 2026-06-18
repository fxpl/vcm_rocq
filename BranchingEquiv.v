From Vcm Require Import Common.
From Vcm Require Import SharedMemory.
From Vcm Require Import Log.
From Vcm Require Import LoggingSharedMemory.
From Vcm Require Import Branching.
From Vcm Require Import LoggingBranching.

Import Log.

Definition same_expressions (cfgSh : SharedMemory.cfg) (cfgB : Branching.cfg) :=
  match cfgSh, cfgB with
  | (TSh, _, _), (TB, _, _) =>
      forall t st e,
        binds TSh t (st, e) <-> exists d h, binds TB t (st, e, d, h)
  end.

Lemma same_expressions_same_domain :
  forall Tsh H Lsh TB G LG,
    same_expressions (Tsh, H, Lsh) (TB, G, LG) ->
    dom Tsh = dom TB.
Proof.
  introv Hexp.
  simpls. unfolds SharedMemory.threads, Branching.threads.
  do 2 rewrite dom_eq_set_of_binds.
  apply set_st_eq.
  intros t. splits.
  - introv ((st & e) & Hbinds).
    apply Hexp in Hbinds as (d & h & Hbinds').
    exists*.
  - introv ((((st & e) & d ) & h) & Hbinds).
    exists (st, e). apply* Hexp.
Qed.

Lemma conflict_free_last_local_write :
  forall log D TC G LC t i v,
    conflict_free log ->
    play_log log (\{}, \{}, (\{}, \{}), \{}) (D, TC, G, LC) ->
    t \indom D ->
    binds D[t] i v ->
    exists log', LibList.filter (fun e => writes_location i e) log = log' & event_write t i v.
Proof.
  introv Hcf Hplay Hdom Hdelta.
  hint conflict_free_last_inv.
  hint inhab_val.
  inductions Hplay.
  - forwards*: indom_empty_inv.
  - inverts H.
    + (* PlayRead*)
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayWrite *)
      destruct (classic (t = t0)).
      * subst. rewrite read_update_same in Hdelta.
        destruct (classic (i = i0)).
        -- subst.
           forwards ->: binds_update_same_inv Hdelta.
           exists. rew_listx*. cases_if*.
        -- forwards~ Hdelta': binds_update_neq_inv Hdelta.
           asserts Hbinds: (binds D'[t0] i v).
           {
             forwards : read_of_binds H2.
             subst*.
           }
           forwards* (log' & Hfilter): IHHplay.
           exists log'.
           rew_listx. cases_if. rew_list*.
      * rewrite~ read_update_neq in Hdelta.
        rew_dom. rew_set in Hdom. branches; [|congruence].
        forwards* (log' & Hfilter): IHHplay.
        exists log'.
        rew_listx. cases_if as Hwrites.
        -- simpl in Hwrites. subst. false.
           (* There is at least one write by t to i0 in log (by Hfilter).
              This write is in the delta of t (by Hdelta), so it has not been committed.
              The log is conflict free (by Hcf) so the write by t to i0
              happens before the write by t0 to i0.
              But since t <> t0 and the write is uncommitted, the happens before
              relation is a contradiction.
            *)
           asserts Hmem: (mem (event_write t i0 v) (LibList.filter (fun e => writes_location i0 e) log)).
           {
             rewrite Hfilter. rew_listx*.
           }
           asserts Hmem1: (mem (event_write t i0 v) (log & event_write t0 i0 v0)).
           {
             forwards (Hmem' & _): mem_filter_inv Hmem.
             rew_listx~.
           }
           forwards (m & Hmth): mem_Nth Hmem1.
           asserts Hneq: (m <> length log).
           {
             intros contra. subst.
             forwards [contra | (k & Heq & Hnth)]: Nth_app_inv Hmth.
             - forwards*: Nth_inbound contra.
             - asserts* Heq': (k = 0).
               subst.
               forwards* [(_ & contra) | (? & contra)]: Nth_cons_inv Hnth.
           }
           asserts Hlt: (m < length log).
           {
             forwards Hlt: Nth_inbound Hmth.
             rew_list* in Hlt.
           }
           asserts Hnth: (LibList.Nth (length log) (log & event_write t0 i0 v0) (event_write t0 i0 v0)).
           {
             applys* Nth_app_r'.
           }
           forwards Hhb: Hcf Hmth Hnth Hlt.
           clears Hneq Hlt.
           admit. (* After event m, t may not have another write
           of i0, a start or end event, a spawn event, or an
           unlock event. There cannot be a join of t0 since it has
           not ended, and any locks taken by t are still held.
           Since there are no possible synchronisation events *)
        -- rew_list*.
    + (* PlayStart *)
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayEnd *)
      asserts Hneq: (t <> t0).
      {
        intros contra.
        subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta).
        forwards*: indom_empty_inv.
      }
      rewrite~ read_update_neq in Hdelta.
      rew_dom. rew_set in Hdom. inverts Hdom; [|congruence].
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlaySpawn *)
      asserts Hneq2: (t <> t2).
      {
        intros contra.
        subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta).
        forwards*: indom_empty_inv.
      }
      rewrite~ read_update_neq in Hdelta.
      asserts Hneq1: (t <> t1).
      {
        intros contra.
        subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta).
        forwards*: indom_empty_inv.
      }
      rewrite~ read_update_neq in Hdelta.
      rew_dom. rew_set in Hdom. repeat (branches; [|congruence]).
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayJoin *)
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayLock*)
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayUnlock*)
      asserts Hneq: (t <> t0).
      {
        intros contra.
        subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta).
        forwards*: indom_empty_inv.
      }
      rewrite~ read_update_neq in Hdelta.
      rew_dom. rew_set in Hdom. inverts Hdom; [|congruence].
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
Admitted.

Lemma is_latest_value_commit_fresh :
  forall G c c' d h i v,
    commit_fresh G c' ->
    h <> c' ->
    is_latest_value (graph_commit G c c' d) i v h ->
    is_latest_value G i v h.
Proof.
  Admitted.

Lemma conflict_free_last_global_write :
  forall log D TC G LC t i v h,
    conflict_free log ->
    play_log log (\{}, \{}, (\{}, \{}), \{}) (D, TC, G, LC) ->
    i \notindom (D[t]) ->
    t \indom TC ->
    TC[t] = h ->
    is_latest_value G i v h ->
    exists t' log', LibList.filter (fun e => writes_location i e) log = log' & event_write t' i v.
Proof.
  introv Hcf Hplay Hndom Hdom HTC Hval.
  hint conflict_free_last_inv.
  hint inhab_val.
  inductions Hplay.
  - forwards*: indom_empty_inv.
  - inverts H.
    + (* PlayRead*)
      forwards* (t' & log' & Hfilter): IHHplay.
      exists t' log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayWrite *)
      destruct (classic (t = t0)).
      * subst. rewrite read_update_same in *.
        destruct (classic (i = i0)).
        -- subst.
           rew_dom. false Hndom.
           rew_set. auto.
        -- rew_dom.
           asserts Hndom': (i \notindom D'[t0]).
           {
             intros contra. apply Hndom.
             forwards: read_of_binds H2.
             subst. rew_set. auto.
           }
           forwards* (t' & log' & Hfilter): IHHplay.
           exists t' log'.
           rew_listx. cases_if. rew_list*.
      * rewrite~ read_update_neq in Hndom.
        forwards* (t' & log' & Hfilter): IHHplay.
        exists t' log'.
        rew_listx. cases_if as Hwrites.
        -- simpl in Hwrites. subst. false.
           asserts Hmem: (mem (event_write t' i0 v) (LibList.filter (fun e => writes_location i0 e) log)).
           {
             rewrite Hfilter. rew_listx*.
           }
           asserts Hmem1: (mem (event_write t' i0 v) (log & event_write t0 i0 v0)).
           {
             forwards (Hmem' & _): mem_filter_inv Hmem.
             rew_listx~.
           }
           forwards (m & Hmth): mem_Nth Hmem1.
           asserts Hneq: (m <> length log).
           {
             admit.
           }
           asserts Hlt: (m < length log).
           {
             forwards Hlt: Nth_inbound Hmth.
             rew_list* in Hlt.
           }
           asserts Hnth: (LibList.Nth (length log) (log & event_write t0 i0 v0) (event_write t0 i0 v0)).
           {
             applys* Nth_app_r'.
           }
           forwards Hhb: Hcf Hmth Hnth Hlt.
           clears Hneq Hlt.
           admit.
        -- rew_list*.
    + (* PlayStart *)
      forwards* (t' & log' & Hfilter): IHHplay.
      exists t' log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayEnd: thread t0 ends, committing staging area d as fresh commit c'.
         Pre-state: (D, TC, (C, P), LC).
         Constructor hypotheses (names may vary): binds TC t0 c, c' \notindom C, binds D t0 d. *)
      destruct (classic (t = t0)) as [-> | Hne].
      * (* t = t0: HTC reduces to c' = h *)
        rewrite read_update_same in HTC. subst.
        admit.
      * (* t ≠ t0: rewrite post-state hypotheses back to the pre-state *)
        rewrite~ read_update_neq in HTC.
        rewrite~ read_update_neq in Hndom.
        rew_dom. rew_set in Hdom. branches; [| congruence].
        asserts Hval' : (is_latest_value G' i v h).
        { applys~ is_latest_value_commit_fresh c c' d.
          (* Surely all commits in TC is also in C *)
          admit.
        }
        forwards* (t'' & log'' & Hfilter): IHHplay.
        exists t'' log''. rew_listx. cases_if. rew_list*.
    + (* PlaySpawn *)
      admit.
    + (* PlayJoin *)
      admit.
    + (* PlayLock*)
      admit.
    + (* PlayUnlock*)
      admit.
Admitted.

Theorem branching_equiv :
  forall log log' cfgSh cfgB,
    wf_log log ->
    match cfgB with
    | (_, G, _) => wf_graph G
    end ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingBranching.describes log cfgB ->
    same_expressions cfgSh cfgB ->
    conflict_free log' ->
      (exists cfgSh', LoggingSharedMemory.step (cfgSh, log) (cfgSh', log')) <->
      (exists cfgB', LoggingBranching.step (cfgB, log) (cfgB', log')).
Proof.
  introv Hwf HwfG HdescSh HdescB Hexp Hcf.
  splits.
  - introv (cfgSh' & Hstep).
    destruct cfgB as [(T & G) L].
    forwards* HdiscSh': LoggingSharedMemory.step_preserves_describes Hwf.
    inverts Hstep;
      match goal with
      | H: binds ?T ?t (?ts', ?e) |- _ =>
          apply Hexp in H as (d & h & Hbinds)
      end.
    + exists. constructors*.
    + forwards (h' & Hfresh): exists_commit_fresh HwfG.
      asserts (T' & G' & Hcommit): (exists T' G', do_commit t h' T G = (T', G')).
      {
        exists. unfolds do_commit.
        forwards Hread: read_of_binds Hbinds.
        replace T[t] with (state_running, te_ret r, d, h).
        reflexivity.
      }
      exists. constructors*.
    + destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      apply Hwrite in H6 as (t' & log' & Hfilter).
      admit. (* Cases on whether it is a global or local read *)
    + exists. constructors*.
    + forwards (h' & Hfresh): exists_commit_fresh HwfG.
      forwards* Heq: same_expressions_same_domain.
      rewrite Heq in H6.
      asserts* Hneq: (t <> t').
      asserts (T' & G' & Hpush): (exists T' G', push_thread t t' h' T[t:=(state_running, te_exp (K t'), d, h)][t':=(state_new, te_exp e', \{}, 0)] G = (T', G')).
      {
        exists. unfolds push_thread, do_commit.
        rewrite~ read_update_neq.
        rewrite read_update_same.
        rewrite~ read_update_neq.
        rewrite read_update_same.
        reflexivity.
      }
      exists. constructors*.
    + forwards (h'' & Hfresh): exists_commit_fresh HwfG.
      apply Hexp in H4 as (d' & h' & Hbinds').
      asserts (T' & G' & Hpull & Hbinds''): (exists T' G', pull_thread t t' h'' T G = (T', G') /\
                                                           binds T' t (state_running, te_exp e, d', h'')).
      {
        exists. unfolds pull_thread, do_merge.
        forwards Hread: read_of_binds Hbinds.
        replace T[t'] with (state_terminated, te_ret r, d, h).
        forwards Hread': read_of_binds Hbinds'.
        replace T[t] with (state_running, te_exp e, d', h').
        splits.
        - reflexivity.
        - apply binds_update_same.
      }
      asserts Hempty: (d = \{}).
      {
        admit. (* terminated thread has an empty staging area. *)
      }
      substs.
      asserts Hmerge: (conflict_free_merge d' h' h G).
      {
        admit.
      }
      exists. constructors*.
    + exists. constructors*.
      admit. (* Correspondence between locks via log *)
      all: admit. (* This is where things are shelved *)
    + forwards (h'' & Hfresh): exists_commit_fresh HwfG.
      asserts (h' & HbindsL): (exists h', binds L l0 (ls_held t, h')).
      {
        admit.
      }
      asserts (T' & G' & L' & Hpush & Hbinds'): (exists T' G' L', push_lock t l0 h'' T G L = (T', G', L') /\ binds T' t (state_running, te_exp e, \{}, h'')).
      {
        exists. unfolds push_lock, do_commit.
        forwards Hread: read_of_binds Hbinds.
        replace T[t] with (state_running, te_exp e, d, h).
        forwards Hread': read_of_binds HbindsL.
        replace L[l0] with (ls_held t, h').
        splits.
        - reflexivity.
        - apply binds_update_same.
      }
      exists. constructors*.
  - introv (cfgB' & Hstep).
    destruct cfgSh as ((Tsh & H) & Lsh).
    inverts Hstep;
      try
      match goal with
      | H: binds ?T ?t (?ts, ?e, ?d, ?h) |- _ =>
          asserts Hex: (exists d h, binds T t (ts, e, d, h));
          [exists d; exists h; exact H|];
          apply Hexp in Hex as Hbinds; clear Hex
      end.
    + exists. constructors*.
    + exists. constructors*.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescB as (_ & _ & _ & _ & _ & _ & (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC)).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      apply Hwrite.
      forwards Hcf': conflict_free_last_inv Hcf.
      forwards* Hbinds'': HdomD t.
      forwards* Hex: conflict_free_last_local_write Hplay.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescB as (_ & _ & _ & _ & _ & _ & (D & TC & LC & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC)).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      forwards* Heq: binds_inj Hbinds'.
      inverts Heq.
      asserts* ->: (h = TC[t]).
      apply Hwrite.
      forwards Hcf': conflict_free_last_inv Hcf.
      asserts* Hdom: (t \indom T).
      forwards~ Hdom': HdomTC Hdom.
      forwards* Hex: conflict_free_last_global_write Hplay.
    + exists. constructors*.
    + exists. constructors*.
      forwards* ->: same_expressions_same_domain.
    + asserts* Hex: (exists d h, binds T t' (state_terminated, te_ret r, d, h)).
      apply Hexp in Hex.
      exists. constructors*.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & HunlockedSh & _).
      destruct HdescB as (_ & _ & _ & _ & _ & HunlockedB & _).
      forwards Hiff: HunlockedSh l0.
      forwards Hiff': HunlockedB l0.
      apply Hiff. apply* Hiff'.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & HlockedSh & _ & _).
      destruct HdescB as (_ & _ & _ & _ & HunlockedB & _ & _).
      forwards* (t' & log' & Hiff): HlockedSh t l0.
      forwards* (t'' & log'' & Hiff'): HunlockedB t l0.
Admitted.

(* TODO: We currently model data races as stuck states. Regardless
of whether we add the exception rules, we will probably need a
lemma that says that a conflict-free log that describes a graph
implies a conflict-free graph. *)

(*
Lemma conflict_free_log_describes_conflict_free_graph :
  forall log G,
    conflict_free log ->
    describes log G ->
    conflict_free G. *)
