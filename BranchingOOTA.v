From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Linear.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.
From Vcm Require Import LoggingBranching.
From Vcm Require Import LoggingBranchingFacts.
From Vcm Require Import BranchingEquivLemmas.

Import Graph.
Import GraphFacts.
Import Linear.
Import Log.
Import LogFacts.
Import LoggingBranching.


(* ===========================================================================
   No out-of-thin-air reads (branching), local case.

   If a thread reads a value [v] for [x] from its own staging area [D[t]], then
   [t] itself wrote that value earlier, and (being the same thread, by program
   order) that write happens-before the read.  No conflict-freedom is needed.
   =========================================================================== *)

Lemma branching_no_ootar_local :
  forall log D TC G LC CH t x v,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    t \indom D ->
    binds (D[t]) x v ->
    exists m tw, LibList.Nth m log (event_write tw x v)
              /\ hb (log & event_read t x v) m (length log).
Proof.
  introv Hplay Hdom Hbind.
  forwards (m & HNm & _): delta_is_uncommitted_write Hplay Hdom Hbind.
  forwards Hlt: Nth_inbound HNm.
  exists m t. split.
  - exact HNm.
  - applys HbPo m (length log) (event_write t x v) (event_read t x v).
    + applys* Nth_app_l.
    + applys* Nth_app_r'.
    + reflexivity.
    + exact Hlt.
Qed.

(* Appending an event that is not a write of [x] by [t] preserves "no x-write by
   [t] after [m]".  (Companion to [no_commit_event_snoc].) *)
Lemma no_xwrite_snoc :
  forall (lg : log) E m t x,
    (forall p vp, m < p -> ~ LibList.Nth p lg (event_write t x vp)) ->
    (forall vp, E <> event_write t x vp) ->
    (forall p vp, m < p -> ~ LibList.Nth p (lg & E) (event_write t x vp)).
Proof.
  introv Hno HneqE. introv Hlt HN.
  forwards [HN' | (Hpe & Hee)]: Nth_last_inv HN.
  - applys Hno Hlt HN'.
  - apply (HneqE vp). congruence.
Qed.

(* Strengthening of [delta_is_uncommitted_write]: the write that put [x = v] into
   [t]'s staging is not only uncommitted ([t] performs no commit event after it)
   but is the *last* x-write by [t] (no [t]-write of [x] after it).  This is what
   makes it a maximal visible source: [D[t]] always reflects the latest staged
   write, so any later x-write would have overwritten [v]. *)
Lemma delta_last_uncommitted_write :
  forall log D TC G LC CH t x v,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    t \indom D ->
    binds D[t] x v ->
    exists m,
      LibList.Nth m log (event_write t x v) /\
      (forall p ep, m <= p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep) /\
      (forall p vp, m < p -> ~ LibList.Nth p log (event_write t x vp)).
Proof.
  introv Hplay Hdom Hbinds.
  inductions Hplay.
  - (* PlayNil: D = empty *)
    rew_dom. rew_set in Hdom.
    branches; [forwards*: indom_empty_inv|].
    subst. rewrite read_update_same in Hbinds.
    forwards* Heq: binds_empty_false Hbinds. typeclass.
  - inverts H.
    + (* PlayRead *)
      forwards* (wm & wHN & wHns & wHnw): IHHplay.
      exists wm. splits;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto
        | applys no_xwrite_snoc wHnw; intros vp; discriminate ].
    + (* PlayWrite (event_write t0 x0 v0) *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        destruct (classic (x = x0)) as [Hei | Hnei].
        { (* same variable: the new event is the last write, hence the witness *)
          subst x. forwards ->: binds_update_same_inv Hbinds.
          match goal with |- exists m, LibList.Nth m (?lg & _) _ /\ _ => exists (length lg) end.
          splits.
          - applys* Nth_app_r'.
          - introv Hle HN Hg.
            forwards [HN' | (Hpe & Hee)]: Nth_last_inv HN.
            + forwards Hib: Nth_inbound HN'. exfalso. nat_math.
            + subst ep. simpl. auto.
          - introv Hlt HN. forwards Hib: Nth_inbound HN. rew_list in Hib. nat_math. }
        { (* different variable: carry the older write forward *)
          forwards Hbd: binds_update_neq_inv Hbinds Hnei.
          lets Hin: (indom_of_binds H2).
          asserts Hb': (binds (D'[t0]) x v). { forwards: read_of_binds H2. subst*. }
          forwards* (wm & wHN & wHns & wHnw): IHHplay.
          exists wm. splits;
            [ applys* Nth_app_l wHN
            | applys no_commit_event_snoc wHns; intros _; simpl; auto
            | applys no_xwrite_snoc wHnw; intros vp Heq; inverts Heq; congruence ]. } }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns & wHnw): IHHplay.
        exists wm. splits;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros _; simpl; auto
          | applys no_xwrite_snoc wHnw; intros vp Heq; inverts Heq; congruence ]. }
    + (* PlayStart *)
      forwards* (wm & wHN & wHns & wHnw): IHHplay.
      exists wm. splits;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto
        | applys no_xwrite_snoc wHnw; intros vp; discriminate ].
    + (* PlayEnd (event_end t0) *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns & wHnw): IHHplay.
        exists wm. splits;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence
          | applys no_xwrite_snoc wHnw; intros vp; discriminate ]. }
    + (* PlaySpawn (event_spawn t1 t2) *)
      destruct (classic (t = t2)) as [Het2 | Hneq2].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        destruct (classic (t = t1)) as [Het1 | Hneq1].
        { subst t. rewrite read_update_same in Hbinds.
          lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
        { rewrite~ read_update_neq in Hbinds.
          asserts Hin: (t \indom D').
          { lets [Hc2 | Hd2]: (indom_update_inv Hdom). congruence.
            lets [Hc1 | Hd1]: (indom_update_inv Hd2). congruence. exact Hd1. }
          forwards* (wm & wHN & wHns & wHnw): IHHplay.
          exists wm. splits;
            [ applys* Nth_app_l wHN
            | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence
            | applys no_xwrite_snoc wHnw; intros vp; discriminate ]. } }
    + (* PlayJoin: merge, D unchanged *)
      forwards* (wm & wHN & wHns & wHnw): IHHplay.
      exists wm. splits;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto
        | applys no_xwrite_snoc wHnw; intros vp; discriminate ].
    + (* PlayLock: merge, D unchanged *)
      forwards* (wm & wHN & wHns & wHnw): IHHplay.
      exists wm. splits;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto
        | applys no_xwrite_snoc wHnw; intros vp; discriminate ].
    + (* PlayUnlock (event_unlock t0 l) *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns & wHnw): IHHplay.
        exists wm. splits;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence
          | applys no_xwrite_snoc wHnw; intros vp; discriminate ]. }
Qed.

(* The least commit event of [t] in the interval [(a, b]]: given SOME commit of
   [t] at [b > a], there is a first one [f] with no [t]-commit in [(a, f)]. *)
Lemma exists_first_commit :
  forall b lg t a eb,
    a < b -> LibList.Nth b lg eb -> get_thread eb = t -> is_commit_event eb ->
    exists f ef, a < f /\ f <= b /\ LibList.Nth f lg ef /\ get_thread ef = t /\
      is_commit_event ef /\
      (forall p ep, a < p -> p < f -> LibList.Nth p lg ep -> get_thread ep = t ->
                    ~ is_commit_event ep).
Proof.
  intros b. induction b using peano_induction. introv Hab HNb Hgb Hcb.
  destruct (classic (exists p ep, a < p /\ p < b /\ LibList.Nth p lg ep /\
                                  get_thread ep = t /\ is_commit_event ep))
    as [(p & ep & Hap & Hpb & HNp & Hgp & Hcp) | Hno].
  - forwards (f & ef & Haf & Hfp & HNf & Hgf & Hcf & Hcl): (>> H p Hap HNp Hgp Hcp); [ nat_math | ].
    exists f ef. splits; try assumption. nat_math.
  - exists b eb. splits; try assumption; try nat_math.
    introv Hap Hpb HNp Hgp Hcp. applys Hno. exists p ep. splits; assumption.
Qed.

(* A commit is created at a unique position: two commit events recording the same
   commit are the same event.  (The commit is fresh when created, so it cannot
   already be in the graph from an earlier creation.) *)
Lemma CH_commit_event_inj :
  forall log D TC G LC CH i j c ei ej,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    LibList.Nth i CH c -> LibList.Nth i log ei -> is_commit_event ei ->
    LibList.Nth j CH c -> LibList.Nth j log ej -> is_commit_event ej ->
    i = j.
Proof.
  introv Hplay. gen i j c ei ej. inductions Hplay; introv HNci HNli Hci HNcj HNlj Hcj.
  - forwards*: Nth_nil_inv HNci.
  - rename H into Hpe. forwards Hlen: play_log_CH_length Hplay.
    forwards [HNci0 | (HiN & Hcxi)]: Nth_last_inv HNci;
    forwards [HNcj0 | (HjN & Hcxj)]: Nth_last_inv HNcj.
    + (* both old: recurse *)
      forwards [HNli0 | (HiN' & _)]: Nth_last_inv HNli.
      2:{ forwards Hib: Nth_inbound HNci0. nat_math. }
      forwards [HNlj0 | (HjN' & _)]: Nth_last_inv HNlj.
      2:{ forwards Hib: Nth_inbound HNcj0. nat_math. }
      forwards* Heqij: (>> IHHplay HNci0 HNli0 Hci HNcj0 HNlj0 Hcj).
    + (* i old, j fresh: [c] both fresh at [j] and present from [i] -- contradiction *)
      exfalso.
      forwards [HNli0 | (HiN' & _)]: Nth_last_inv HNli.
      2:{ forwards Hib: Nth_inbound HNci0. nat_math. }
      forwards [HNlj0 | (HjN' & HljE)]: Nth_last_inv HNlj.
      { forwards Hib: Nth_inbound HNlj0. rewrite Hlen in HjN. nat_math. }
      subst ej. forwards Hin: CH_commit_event_indom Hplay HNci0 HNli0 Hci.
      forwards (Hfr & _): play_event_commit_new Hpe Hcj.
      rewrite Hcxj in Hfr. applys commit_fresh_not_indom Hfr Hin.
    + (* i fresh, j old: symmetric *)
      exfalso.
      forwards [HNlj0 | (HjN' & _)]: Nth_last_inv HNlj.
      2:{ forwards Hib: Nth_inbound HNcj0. nat_math. }
      forwards [HNli0 | (HiN' & HliE)]: Nth_last_inv HNli.
      { forwards Hib: Nth_inbound HNli0. rewrite Hlen in HiN. nat_math. }
      subst ei. forwards Hin: CH_commit_event_indom Hplay HNcj0 HNlj0 Hcj.
      forwards (Hfr & _): play_event_commit_new Hpe Hci.
      rewrite Hcxi in Hfr. applys commit_fresh_not_indom Hfr Hin.
    + (* both fresh: same position *)
      nat_math.
Qed.

(* HELPER 1: a write at [m] by [t] with no [t]-commit after [m] leaves [x] in
   [t]'s staging area [D[t]].  [wf_log] is needed only to rule out a re-spawn of
   [t] (which would reset [D[t]] to empty) via [spawned_thread_no_prior_event]. *)
Lemma write_persists_in_delta :
  forall log D TC G LC CH t x v m,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    LibList.Nth m log (event_write t x v) ->
    (forall p ep, m < p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep) ->
    x \indom (D[t]).
Proof.
  introv Hwf Hplay. gen m t x v. inductions Hplay; introv HNm Hncl.
  - inverts HNm.
  - forwards Hwf0: wf_log_last_inv Hwf.
    forwards Hlen: play_log_CH_length Hplay.
    forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNm.
    + (* the write is in the prefix; E is the last (appended) event, at [length log] > m *)
      forwards Hib: Nth_inbound HN0.
      asserts HNE: (LibList.Nth (length log) (log & E) E).
      { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
      asserts Hncl0:
        (forall p ep, m < p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep).
      { introv Hlt HNp Hgp. forwards HNp': Nth_app_l HNp. applys Hncl Hlt HNp' Hgp. }
      forwards* Hin0: (>> IHHplay Hwf0 HN0 Hncl0).
      (* now push [x \indom D'[t]] through the last play event to [x \indom D''[t]] *)
      destruct E as [s1 s2 | jt1 jt2 | rt rj rw | wt wj ww | lt ll | ut ul | stt | ett];
        inverts H.
      * (* spawn s1 s2 : a commit of s1; s2 is freshly spawned so [t <> s2] *)
        forwards Hns2: spawned_thread_no_prior_event Hwf HN0. cbn [get_thread] in Hns2.
        destruct (classic (t = s1)) as [Hs1 | Hs1].
        -- subst s1. exfalso. applys Hncl (length log) (event_spawn t s2); try nat_math.
           exact HNE. reflexivity. simpl; exact I.
        -- rewrite read_update_neq; [ | congruence ].
           rewrite read_update_neq; [ exact Hin0 | congruence ].
      * (* join : D unchanged *) exact Hin0.
      * (* read : D unchanged *) exact Hin0.
      * (* write wt wj ww : domain only grows *)
        destruct (classic (t = wt)) as [Hwt | Hwt].
        -- subst wt. rewrite read_update_same.
           match goal with Hbd : binds _ t ?dstg |- _ =>
             forwards Hdeq: read_of_binds Hbd end.
           apply indom_update_of_indom; (typeclass || (rewrite <- Hdeq; exact Hin0)).
        -- rewrite read_update_neq; [ exact Hin0 | congruence ].
      * (* lock (PlayLock) : D unchanged *) exact Hin0.
      * (* unlock ut ul : a commit of ut; if [t = ut] excluded by [Hncl] *)
        destruct (classic (t = ut)) as [Hut | Hut].
        -- subst ut. exfalso. applys Hncl (length log) (event_unlock t ul); try nat_math.
           exact HNE. reflexivity. simpl; exact I.
        -- rewrite read_update_neq; [ exact Hin0 | congruence ].
      * (* start : D unchanged *) exact Hin0.
      * (* end ett : a commit of ett; if [t = ett] excluded by [Hncl] *)
        destruct (classic (t = ett)) as [Het | Het].
        -- subst ett. exfalso. applys Hncl (length log) (event_end t); try nat_math.
           exact HNE. reflexivity. simpl; exact I.
        -- rewrite read_update_neq; [ exact Hin0 | congruence ].
    + (* the write is the last (appended) event *)
      subst E. inverts H.
      rewrite read_update_same. apply indom_update_same; typeclass.
Qed.

(* HELPER 2: the first commit event [f] of [t] after a write [m] of [x = v]
   (with no [t]-commit in [(m, f)]) flushes [x] into the graph: its commit
   [cf = CH[f]] is an x-writer.  ([v] need not be the flushed value: the delta may
   have been overwritten between [m] and [f], but [x] is still in [t]'s staging
   area at flush time, by [write_persists_in_delta].) *)
Lemma xwrite_flush_writer :
  forall log D TC G LC CH t x v m f ef cf,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    LibList.Nth m log (event_write t x v) ->
    m < f -> LibList.Nth f log ef -> get_thread ef = t -> is_commit_event ef ->
    (forall p ep, m < p -> p < f -> LibList.Nth p log ep -> get_thread ep = t ->
                  ~ is_commit_event ep) ->
    LibList.Nth f CH cf ->
    exists vf, graph_writes G cf x vf.
Proof.
  introv Hwf Hplay. gen m t x v f ef cf. inductions Hplay; introv HNm Hmf HNf Hgf Hcf Hncl HNfch.
  - inverts HNm.
  - forwards Hwf0: wf_log_last_inv Hwf.
    forwards Hlen: play_log_CH_length Hplay.
    forwards [HNf0 | (HfN & HefE)]: Nth_last_inv HNf.
    + (* the commit [f] is in the prefix: recurse there, then lift the graph *)
      forwards Hfib: Nth_inbound HNf0.
      forwards [HNm0 | (HmN & HmE)]: Nth_last_inv HNm.
      2:{ forwards Hib: Nth_inbound HNf0. nat_math. }
      forwards [HNfch0 | (HfchN & _)]: Nth_last_inv HNfch.
      2:{ rewrite Hlen in HfchN. nat_math. }
      asserts Hncl0:
        (forall p ep, m < p -> p < f -> LibList.Nth p log ep -> get_thread ep = t ->
                      ~ is_commit_event ep).
      { introv Hlt Hpf HNp Hgp. forwards HNp': Nth_app_l HNp. applys Hncl Hlt Hpf HNp' Hgp. }
      forwards* (vf & Hgw): (>> IHHplay Hwf0 HNm0 Hmf HNf0 Hgf Hcf Hncl0 HNfch0).
      exists vf. applys play_event_graph_writes_mono H Hgw.
    + (* the commit [f] is the last (appended) event [E], a commit event by [t] *)
      subst ef.
      (* [m] is strictly before [f = length log], hence in the prefix *)
      forwards [HNm0 | (HmN & HmE)]: Nth_last_inv HNm.
      2:{ subst E. cbn [is_commit_event] in Hcf. contradiction. }
      forwards Hmib: Nth_inbound HNm0.
      (* cf = CH[length log] = TC''[get_thread E] *)
      forwards [HNfch0 | (HfchN & Hcxeq)]: Nth_last_inv HNfch.
      { forwards Hib: Nth_inbound HNfch0. rewrite Hlen in Hib. nat_math. }
      (* [x] is in [t]'s staging area in the prefix (no [t]-commit after [m] in prefix) *)
      asserts Hnclp:
        (forall p ep, m < p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep).
      { introv Hlt HNp Hgp. forwards Hpib: Nth_inbound HNp.
        forwards HNp': Nth_app_l HNp.
        applys Hncl Hlt; [ nat_math | exact HNp' | exact Hgp ]. }
      forwards HxinD: (>> write_persists_in_delta Hwf0 Hplay HNm0 Hnclp).
      (* [E] is a commit event by [t]: spawn (as spawner), unlock, or end *)
      destruct E as [s1 s2 | jt1 jt2 | rt rj rw | wt wj ww | lt ll | ut ul | stt | ett];
        cbn [get_thread is_commit_event] in Hgf, Hcf; try contradiction;
        cbn [get_thread] in Hcxeq; inverts H.
      * (* PlaySpawn s1 s2, spawner is [t = s1] *)
        subst t.
        match goal with HbD : binds D' s1 d |- _ =>
          forwards Hdd: read_of_binds HbD end.
        asserts Hxd: (x \indom d). { rewrite <- Hdd. exact HxinD. }
        asserts Hbxv: (binds d x (d[x])).
        { applys binds_of_indom_read Hxd; (reflexivity || typeclass). }
        eexists. rewrite <- Hcxeq.
        destruct (classic (s1 = s2)) as [Heqt | Hnet].
        -- subst s2. rewrite read_update_same.
           applys graph_writes_graph_commit_new Hbxv.
        -- rewrite read_update_neq; [ | congruence ]. rewrite read_update_same.
           applys graph_writes_graph_commit_new Hbxv.
      * (* PlayUnlock ut ul, [t = ut] *)
        subst t.
        match goal with HbD : binds D' ut d |- _ =>
          forwards Hdd: read_of_binds HbD end.
        asserts Hxd: (x \indom d). { rewrite <- Hdd. exact HxinD. }
        asserts Hbxv: (binds d x (d[x])).
        { applys binds_of_indom_read Hxd; (reflexivity || typeclass). }
        eexists. rewrite <- Hcxeq. rewrite read_update_same.
        applys graph_writes_graph_commit_new Hbxv.
      * (* PlayEnd ett, [t = ett] *)
        subst t.
        match goal with HbD : binds D' ett d |- _ =>
          forwards Hdd: read_of_binds HbD end.
        asserts Hxd: (x \indom d). { rewrite <- Hdd. exact HxinD. }
        asserts Hbxv: (binds d x (d[x])).
        { applys binds_of_indom_read Hxd; (reflexivity || typeclass). }
        eexists. rewrite <- Hcxeq. rewrite read_update_same.
        applys graph_writes_graph_commit_new Hbxv.
Qed.

(* HELPER 3: the write feeding a flush commit is the *last* x-write of its thread
   before the flush.  If [cw = CH[fw]] is the commit of a [tw]-flush at [fw] and
   [cw] writes [x = v0] in the graph, then there is a [tw]-write of [x = v0] at some
   [kL < fw] that is the last [tw]-x-write before [fw] (and [tw] does not commit in
   [[kL, fw)]).  The committed diff is [tw]'s staging area at flush time, whose
   [x]-value is pinned to the last x-write by [delta_last_uncommitted_write]. *)
Lemma flush_last_write :
  forall log D TC G LC CH tw x0 fw ef cw v0,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    LibList.Nth fw CH cw -> LibList.Nth fw log ef ->
    get_thread ef = tw -> is_commit_event ef ->
    graph_writes G cw x0 v0 ->
    exists kL,
      kL < fw /\ LibList.Nth kL log (event_write tw x0 v0) /\
      (forall p ep, kL <= p -> p < fw -> LibList.Nth p log ep -> get_thread ep = tw ->
                    ~ is_commit_event ep) /\
      (forall p vp, kL < p -> p < fw -> ~ LibList.Nth p log (event_write tw x0 vp)).
Proof.
  introv Hwf Hplay. gen tw x0 fw ef cw v0. inductions Hplay;
    introv HNfch HNf Hgf Hcf Hgw.
  - forwards*: Nth_nil_inv HNfch.
  - forwards Hwf0: wf_log_last_inv Hwf.
    forwards Hlen: play_log_CH_length Hplay.
    forwards [HNf0 | (HfN & HefE)]: Nth_last_inv HNf.
    + (* flush in the prefix: recurse, then lift graph_writes back *)
      forwards Hfib: Nth_inbound HNf0.
      forwards [HNfch0 | (HfchN & _)]: Nth_last_inv HNfch.
      2:{ rewrite Hlen in HfchN. nat_math. }
      (* the fresh commit is a sink; [cw] is old, so its writes come from the prefix *)
      asserts Hgw0: (graph_writes G' cw x0 v0).
      { forwards Hin: CH_commit_event_indom Hplay HNfch0 HNf0 Hcf.
        rename H into Hpe. inverts Hpe; try exact Hgw;
          match goal with Hfr : commit_fresh G' ?cfresh |- _ =>
            asserts Hne: (cw <> cfresh);
            [ intro Heq; subst cw; applys commit_fresh_not_indom Hfr Hin | ] end;
          first [ applys graph_writes_graph_commit_inv Hne Hgw
                | applys graph_writes_graph_merge_inv Hne Hgw ]. }
      forwards* (kL & HkLlt & HNkL & Hnc & Hnw): (>> IHHplay Hwf0 HNfch0 HNf0 Hgf Hcf Hgw0).
      exists kL. splits.
      * exact HkLlt.
      * applys Nth_app_l HNkL.
      * introv Hle Hpf HNp Hgp. forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp.
        -- applys Hnc Hle Hpf HNp0 Hgp.
        -- nat_math.
      * introv Hlt Hpf HNp. forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp.
        -- applys Hnw Hlt Hpf HNp0.
        -- nat_math.
    + (* flush is the last event [E]: a commit by [tw] storing [tw]'s prefix delta *)
      subst ef.
      forwards [HNfch0 | (HfchN & Hcxeq)]: Nth_last_inv HNfch.
      { forwards Hib: Nth_inbound HNfch0. rewrite Hlen in Hib. nat_math. }
      destruct E as [s1 s2 | jt1 jt2 | rt rj rw | wt wj ww | lt ll | ut ul | stt | ett];
        cbn [get_thread is_commit_event] in Hgf, Hcf; try contradiction;
        cbn [get_thread] in Hcxeq; inverts H.
      * (* PlaySpawn s1 s2, spawner [tw = s1] *)
        subst tw.
        match goal with HbTC : binds TC' s1 ?cc, HbD : binds D' s1 d |- _ =>
          asserts Hbdd: (binds d x0 v0);
          [ rewrite <- Hcxeq in Hgw;
            (destruct (classic (s1 = s2)) as [Heqt | Hnet];
             [ subst s2; rewrite read_update_same in Hgw
             | rewrite read_update_neq in Hgw; [ rewrite read_update_same in Hgw | congruence ] ]);
            applys graph_writes_graph_commit_same Hgw
          | forwards Hdd: read_of_binds HbD;
            rewrite <- Hdd in Hbdd;
            forwards (kL & HNkL & Hnc & Hnw): delta_last_uncommitted_write Hplay (indom_of_binds HbD) Hbdd;
            forwards HkLib: Nth_inbound HNkL;
            exists kL; splits;
            [ nat_math
            | applys Nth_app_l HNkL
            | introv Hle Hpf HNp Hgp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnc Hle HNp0 Hgp | nat_math ]
            | introv Hlt Hpf HNp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnw Hlt HNp0 | nat_math ] ] ] end.
      * (* PlayUnlock ut ul, [tw = ut] *)
        subst tw.
        match goal with HbTC : binds TC' ut ?cc, HbD : binds D' ut d |- _ =>
          asserts Hbdd: (binds d x0 v0);
          [ rewrite <- Hcxeq in Hgw; rewrite read_update_same in Hgw;
            applys graph_writes_graph_commit_same Hgw
          | forwards Hdd: read_of_binds HbD;
            rewrite <- Hdd in Hbdd;
            forwards (kL & HNkL & Hnc & Hnw): delta_last_uncommitted_write Hplay (indom_of_binds HbD) Hbdd;
            forwards HkLib: Nth_inbound HNkL;
            exists kL; splits;
            [ nat_math
            | applys Nth_app_l HNkL
            | introv Hle Hpf HNp Hgp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnc Hle HNp0 Hgp | nat_math ]
            | introv Hlt Hpf HNp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnw Hlt HNp0 | nat_math ] ] ] end.
      * (* PlayEnd ett, [tw = ett] *)
        subst tw.
        match goal with HbTC : binds TC' ett ?cc, HbD : binds D' ett d |- _ =>
          asserts Hbdd: (binds d x0 v0);
          [ rewrite <- Hcxeq in Hgw; rewrite read_update_same in Hgw;
            applys graph_writes_graph_commit_same Hgw
          | forwards Hdd: read_of_binds HbD;
            rewrite <- Hdd in Hbdd;
            forwards (kL & HNkL & Hnc & Hnw): delta_last_uncommitted_write Hplay (indom_of_binds HbD) Hbdd;
            forwards HkLib: Nth_inbound HNkL;
            exists kL; splits;
            [ nat_math
            | applys Nth_app_l HNkL
            | introv Hle Hpf HNp Hgp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnc Hle HNp0 Hgp | nat_math ]
            | introv Hlt Hpf HNp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnw Hlt HNp0 | nat_math ] ] ] end.
Qed.

(* ============================================================================
   No out-of-thin-air reads (branching): preservation of [no_thin_air] by
   [LoggingBranching.step].

   A read at position [n] is [sourced] (Log.v [sourced_read]) when its value [v]
   of [x] is written by some write at [m] that is (i) not hb-after the read, and
   (ii) a *maximal visible* writer: no other x-write sits hb-strictly between it
   and the read.  This is proved as an invariant of the logging step because
   [play_log]'s [PlayRead] ignores the read value; the constraint is pinned only
   at read-*step* time.

   The eight non-read steps reduce to [no_thin_air_snoc_nonread].  The two read
   steps establish sourcedness of the freshly appended read:
     - StepReadLocal:  source is [t]'s own last uncommitted x-write [D[t][x]].
     - StepReadGlobal: source is the [is_latest_value] maximal x-writing ancestor
       of [TC[t]]; maximality rules out an intervening x-write via the (existing)
       [hb ==> ancestor] direction ([hb_pointer_ancestor]).
   Both directions are UNCONDITIONAL (no [conflict_free]).
   ============================================================================ *)

Theorem step_preserves_no_thin_air :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    no_thin_air log ->
    no_thin_air log'.
Proof.
  introv Hwf Hdesc Hstep Hnta.
  inverts Hstep;
    try (applys no_thin_air_snoc_nonread Hnta; intros; discriminate).
  - (* StepReadLocal: source is [t]'s own last uncommitted write [D[t][x]]. *)
    match goal with
    | Hb : binds _ _ (state_running, te_exp _, ?dd, _), Hd : binds ?dd _ _ |- _ =>
        rename Hb into HbT; rename Hd into Hbd
    end.
    destruct Hdesc as (_ & _ & _ & _ & _ & _ &
      (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC)).
    lets HtinT: (indom_of_binds HbT).
    forwards (st' & e'' & Hbd'): Hdelta HtinT.
    forwards~ Heqt: binds_inj HbT Hbd'. inverts Heqt.
    forwards HtinD: HdomD HtinT.
    forwards (m & HNm & Hunc & Hnw): delta_last_uncommitted_write Hplay HtinD Hbd.
    intros n t0 x0 v0 Hnth.
    forwards [Hnth' | (Hp & Heq)]: Nth_last_inv Hnth.
    + (* an older read: preserved by [sourced_read_snoc] *)
      forwards Hlt: Nth_inbound Hnth'.
      forwards Hsr: sourced_read_snoc Hlt (Hnta n). applys Hsr Hnth.
    + (* the freshly appended read at position [length log] *)
      inverts Heq. subst n.
      exists m t0. splits.
      * applys Nth_app_l HNm.
      * intros Hhb. forwards Hlt: hb_lt Hhb. forwards Hm: Nth_inbound HNm. nat_math.
      * (* maximality: no x-write hb-strictly-between [W = D[t][x]] and the read.
           A same-thread [W'] would be a later staged x-write, contradicting [Hnw]
           ([m] is [t]'s LAST x-write); a cross-thread [W'] would need a commit by
           [t] after [m] ([hb_cross_thread_flush]), contradicting [Hunc]. *)
        introv (m' & t'' & v' & Hneq & Hmth' & Hhb & Hhb').
        forwards Hm'lt: hb_lt Hhb'.
        forwards [Hmth'' | (Hpe' & Hee')]: Nth_last_inv Hmth'; [| inverts Hee'].
        forwards Hhb_l: hb_app_inv Hhb Hm'lt.
        destruct (classic (t'' = t0)) as [Ht'' | Ht''].
        -- subst t''. forwards Hmm': hb_lt Hhb_l.
           applys Hnw Hmm' Hmth''.
        -- asserts Hgm: (get_thread (event_write t0 x0 v0) = t0). { reflexivity. }
           asserts Hgm': (get_thread (event_write t'' x0 v') <> t0). { simpl. exact Ht''. }
           forwards (f & ef & Hle & HNf & Hgf & Hcf & Hhbf):
             hb_cross_thread_flush Hhb_l HNm Hgm Hmth'' Hgm'.
           forwards Hni: Hunc Hle HNf Hgf. applys Hni Hcf.
  - (* StepReadGlobal: source is the [is_latest_value] maximal x-writing ancestor. *)
    match goal with
    | Hb : binds _ _ (state_running, te_exp _, _, ?cc), Hl : is_latest_value _ ?cc _ _ |- _ =>
        rename Hb into HbT; rename Hl into Hlv
    end.
    destruct Hdesc as (_ & _ & _ & Hrun & _ & _ &
      (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC)).
    lets HtinT: (indom_of_binds HbT).
    forwards (st' & e'' & Hbd'): Hdelta HtinT.
    forwards~ Heqt: binds_inj HbT Hbd'. inverts Heqt.
    destruct Hlv as (cw & Hgw & Hanc & Hmax).
    (* Pick the source to be the write [kw] that actually *feeds* [cw] (flushed at
       [fw], with [CH[fw] = cw]), so the source is linked to the maximal ancestor. *)
    forwards (fw & ef & tw & kw & HNfw & HNef & Hgtef & Hcef & Hkwlt & HNkw & Hncl):
      graph_writes_flush Hplay Hgw.
    intros n t0 x0 v0 Hnth.
    forwards [Hnth' | (Hp & Heq)]: Nth_last_inv Hnth.
    + forwards Hlt: Nth_inbound Hnth'.
      forwards Hsr: sourced_read_snoc Hlt (Hnta n). applys Hsr Hnth.
    + inverts Heq. subst n.
      (* Strengthen the source to the LAST [tw]-write of [x0] before the flush [fw]:
         [cw]'s stored value is [x0]'s delta value at flush, pinned to the last
         x0-write.  This is what makes the source maximal. *)
      forwards (kL & HkLlt & HNkL & HnclL & HnwL):
        (>> flush_last_write Hwf Hplay HNfw HNef Hgtef Hcef Hgw).
      forwards HlenCH: play_log_CH_length Hplay.
      forwards HkLib: Nth_inbound HNkL.
      exists kL tw. splits.
      * applys Nth_app_l HNkL.
      * intros Hhb. forwards Hlt: hb_lt Hhb. nat_math.
      * (* Maximality.  An intervening x0-write [W'] at [m'] (thread [t'']) with
           [hb kL m'] and [hb m' R] flushes to a commit [cf] that (i) writes [x0]
           ([xwrite_flush_writer]), (ii) is an ancestor of [TC[t0]] ([hb f R] +
           [hb_pointer_ancestor]), and (iii) is a strict descendant of [cw],
           contradicting [Hmax].  The "last write" choice of [kL] ensures [cf <> cw]
           in every thread configuration. *)
        introv (m' & t'' & v' & Hneq & Hmth' & Hhb & Hhb').
        (* ---- common setup ---- *)
        forwards Hm'lt: hb_lt Hhb'.
        forwards [Hmth'' | (Hpe' & Hee')]: Nth_last_inv Hmth'; [| inverts Hee'].
        forwards HmthL: hb_app_inv Hhb Hm'lt.
        (* reader [t0] is running: it has started and not ended *)
        forwards (HstartT & HnoendT): (proj2 (Hrun t0)).
        { exists (te_exp e) D[t0] TC[t0]. exact HbT. }
        forwards HwfR: wf_log_read_last HstartT HnoendT Hwf.
        (* extended play including the read (a no-op that appends [TC[t0]] to [CH]) *)
        asserts HplayR:
          (play_log (log & event_read t0 x0 v0) init_play_cfg (D, TC, G, LC) (CH & TC[t0])).
        { applys PlaySnoc Hplay. applys PlayRead. }
        asserts HNRch: (LibList.Nth (length log) (CH & TC[t0]) (TC[t0])).
        { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
        (* the write event at [m'], both in [log] and in [log & read] *)
        asserts Hm'app: (LibList.Nth m' (log & event_read t0 x0 v0) (event_write t'' x0 v')).
        { applys Nth_app_l Hmth''. }
        asserts HNRapp: (LibList.Nth (length log) (log & event_read t0 x0 v0) (event_read t0 x0 v0)).
        { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
        (* [Get a first [t'']-commit [f] after [m'] with [hb f R], in the prefix]. *)
        asserts Hcommit:
          (exists b eb, m' < b /\ b < length log /\ LibList.Nth b log eb /\
                        get_thread eb = t'' /\ is_commit_event eb /\
                        hb (log & event_read t0 x0 v0) b (length log)).
        { destruct (classic (t'' = t0)) as [Ht0 | Ht0].
          - (* same as reader: [W'] by [t0]; if [t0] never commits after [m'], then
               [x0] stays in [D[t0]], contradicting the global read's [x0 \notindom D[t0]] *)
            subst t''.
            destruct (classic (exists b eb, m' < b /\ b < length log /\
                      LibList.Nth b log eb /\ get_thread eb = t0 /\ is_commit_event eb))
              as [(b & eb & Hmb & Hblt & HNb & Hgb & Hcb) | Hnone].
            + exists b eb. splits; try assumption.
              asserts HNbapp: (LibList.Nth b (log & event_read t0 x0 v0) eb).
              { applys Nth_app_l HNb. }
              applys HbPo HNbapp HNRapp; [ cbn [get_thread]; congruence | nat_math ].
            + exfalso.
              asserts Hncl0:
                (forall p ep, m' < p -> LibList.Nth p log ep -> get_thread ep = t0 ->
                              ~ is_commit_event ep).
              { introv Hlt HNp Hgp Hcp. forwards Hpib: Nth_inbound HNp.
                applys Hnone. exists p ep. splits; try assumption; try nat_math. }
              forwards HxinD: (>> write_persists_in_delta Hwf Hplay Hmth'' Hncl0).
              applys H5 HxinD.
          - (* other thread: [hb m' R] crosses from [t''] to [t0], so it flushes *)
            forwards (f0 & ef0 & Hle0 & HNf0 & Hgf0 & Hcf0 & Hhbf0):
              (>> hb_cross_thread_flush Hhb' Hm'app (eq_refl : get_thread (event_write t'' x0 v') = t'')
                  HNRapp).
            { cbn [get_thread]. intro HH. applys Ht0. rewrite~ HH. }
            (* [f0] is a [t'']-commit; the read at [length log] is by [t0 <> t''], so
               [f0 < length log] *)
            forwards [HNf0' | (Hf0N & Hf0E)]: Nth_last_inv HNf0.
            2:{ subst ef0. cbn [get_thread] in Hgf0. congruence. }
            forwards Hf0lt: Nth_inbound HNf0'.
            asserts Hm'f0: (m' < f0).
            { destruct (classic (m' = f0)) as [He | Hne']; [ | nat_math ].
              subst f0. forwards Heqw: Nth_functional HNf0' Hmth''.
              subst ef0. cbn [is_commit_event] in Hcf0. contradiction. }
            exists f0 ef0. splits; try assumption. }
        destruct Hcommit as (b & eb & Hmb & Hblt & HNb & Hgb & Hcb & Hhbb).
        (* first such commit [f] (no [t'']-commit in [(m', f)]) *)
        forwards (f & ef2 & Hmf & Hfb & HNf2 & Hgf2 & Hcf2 & HnclF):
          (>> exists_first_commit Hmb HNb Hgb Hcb).
        forwards Hflt: Nth_inbound HNf2.
        asserts HfltCH: (f < length CH). { rewrite HlenCH. nat_math. }
        forwards (cf & HNcf): Nth_inbound_inv HfltCH.
        (* [cf] writes [x0] *)
        forwards (vf & Hgwf): (>> xwrite_flush_writer Hwf Hplay Hmth'' Hmf HNf2 Hgf2 Hcf2 HnclF HNcf).
        (* [hb (log & read) f (length log)]: [f <= b] and [hb b R] *)
        asserts HhbfR: (hb (log & event_read t0 x0 v0) f (length log)).
        { destruct (classic (f = b)) as [Hfe | Hfne].
          - subst f. exact Hhbb.
          - asserts HNf2app: (LibList.Nth f (log & event_read t0 x0 v0) ef2).
            { applys Nth_app_l HNf2. }
            asserts HNbapp: (LibList.Nth b (log & event_read t0 x0 v0) eb).
            { applys Nth_app_l HNb. }
            asserts Hhbfb: (hb (log & event_read t0 x0 v0) f b).
            { applys HbPo HNf2app HNbapp; [ congruence | nat_math ]. }
            applys HbTrans Hhbfb Hhbb. }
        (* [cf] is an ancestor of [TC[t0]] (the reader's commit) *)
        asserts HNcfapp: (LibList.Nth f (CH & TC[t0]) cf). { applys Nth_app_l HNcf. }
        forwards HancfTC: (>> hb_pointer_ancestor HwfR HplayR HhbfR HNcfapp HNRch).
        (* [cw] is an ancestor of [cf]; strictness [cf <> cw] gives the contradiction *)
        destruct (classic (tw = t'')) as [Htweq | Htwne].
        -- (* same thread [tw = t'']: [kL] is the last [tw]-x0-write before [fw]; the
              intervening [m' > kL] forces [m' >= fw], hence [f > fw], a strict
              descendant [cf] of [cw]. *)
           rewrite <- Htweq in Hmth''.
           forwards HmL: hb_lt HmthL.
           asserts Hm'fw: (fw <= m').
           { destruct (classic (m' < fw)) as [Hlt | Hge]; [ | nat_math ].
             exfalso. applys HnwL m' v'; [ nat_math | nat_math | exact Hmth'' ]. }
           asserts Hfwf: (fw < f).
           { nat_math. }
           (* [cw = CH[fw]] and [cf = CH[f]] are both [tw]-commits with [fw < f] *)
           asserts Hgf2tw: (get_thread ef2 = tw). { rewrite Hgf2. rewrite~ Htweq. }
           asserts Hanccwcf: (ancestor G cw cf).
           { applys (>> CH_thread_monotone Hwf Hplay HNef Hgtef HNf2 Hgf2tw HNfw HNcf).
             nat_math. }
           asserts Hcfne: (cf <> cw).
           { intro Heq. subst cf.
             forwards Heqpos: (>> CH_commit_event_inj Hplay HNcf HNf2 Hcf2 HNfw HNef Hcef).
             nat_math. }
           forwards Heqcf: (>> Hmax cf vf Hgwf Hanccwcf HancfTC).
           applys Hcfne Heqcf.
        -- (* different threads: [write_hb_flush_ancestor] links [cw] below [cf] *)
           asserts Hanccwcf: (ancestor G cw cf).
           { applys (>> write_hb_flush_ancestor Hwf Hplay
               (conj HNkL (conj HNfw (conj HNef (conj Hgtef (conj Hcef (conj HkLlt HnclL))))))
               (conj Hmth'' (conj HNcf (conj HNf2 (conj Hgf2 (conj Hcf2 Hmf)))))
               Htwne HmthL). }
           asserts Hcfne: (cf <> cw).
           { intro Heq. subst cf.
             (* [cw] created at [fw] by [tw]; [cf=cw] created at [f] by [t'' <> tw];
                a commit is created at a unique position, so [f = fw] and [tw = t''] *)
             forwards Heqpos: (>> CH_commit_event_inj Hplay HNcf HNf2 Hcf2 HNfw HNef Hcef).
             subst f. forwards Heqe: Nth_functional HNf2 HNef.
             rewrite Heqe in Hgf2. cbn [get_thread] in Hgf2. applys Htwne. congruence. }
           forwards Heqcf: (>> Hmax cf vf Hgwf Hanccwcf HancfTC).
           applys Hcfne Heqcf.
Qed.
