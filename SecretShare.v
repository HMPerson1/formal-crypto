Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat fintype tuple.
From mathcomp Require Import ssralg finalg fingroup poly bigop seq.
Local Set Warnings "all".

From FC Require LagrangeInterpolation.
From FC Require Import SubseqPerm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Def.
  Variable RandState Sec Share : finType.
  Variable tm1 n : nat.
  Local Notation t := tm1.+1.
  Hypothesis tlen : t <= n.

  Record impl := Impl { share : RandState -> Sec -> n.-tuple Share; combine : t.-tuple Share -> Sec }.

  Definition correct (i : impl) :=
    forall randstate sec,
      let shares_n := share i randstate sec in
      forall (shares_t : t.-tuple Share),
        subseq_perm shares_t shares_n ->
        combine i shares_t = sec.
  Definition secure (i : impl) :=
    exists c, forall (shares_tm1 : (tm1).-tuple Share),
        (exists randstate0 sec0, subseq_perm shares_tm1 (share i randstate0 sec0)) ->
        forall sec, #|[pred randstate | subseq_perm shares_tm1 (share i randstate sec)]| = c.
End Def.


Section ShamirScheme.
  Variable T : finFieldType.
  Variable tm1 nm1 : nat.
  Local Notation t := tm1.+1.
  Local Notation n := nm1.+1.
  Hypothesis tlen : t <= n.

  Hypothesis le_n_cardunitT : n <= #|[finType of {unit T}]|.

  Definition ShamirScheme
    : impl [finType of (tm1.-tuple T)] T [finType of ({unit T} * T)] tm1 n
    := Impl
         (fun (randstate : (tm1.-tuple T)) sec =>
            let p : {poly T} := Poly (sec :: randstate) in
            [tuple of map
                   (fun i0 =>
                      let i := enum_val (widen_ord le_n_cardunitT i0) in
                      (i , p.[val i]%R))
                   (ord_tuple n)])
         (fun shares =>
            (LagrangeInterpolation.interp_poly
               [tuple of map val (unzip1 shares)]
               [tuple of unzip2 shares]).[0]%R).

  Lemma uniq_shares randstate sec : uniq (share ShamirScheme randstate sec).
  Proof.
    rewrite map_inj_in_uniq; first by apply enum_uniq.
    move=> x y _ _ [Heq _].
    move: Heq => /enum_val_inj.
    rewrite /widen_ord.
    by case => /ord_inj.
  Qed.

  Lemma uniq_subseq_perm_xs randstate sec shares_m
    : subseq_perm shares_m (share ShamirScheme randstate sec) ->
      uniq [seq val i | i <- unzip1 shares_m].
  Proof.
    set shares_n := share _ _ _.
    move=> Hspmn.
    rewrite map_inj_in_uniq; last by move=> x y _ _; apply val_inj.
    rewrite map_inj_in_uniq; first by apply (uniq_subseq_perm Hspmn (uniq_shares _ _)).
    have Hmem_shares : {subset shares_m <= shares_n} by apply mem_subseq_perm.
    move=> a b.
    move=> /Hmem_shares/nthP Ha /Hmem_shares/nthP Hb.
    move: (Ha (1%g, 0%R)) => [ia Hltia <-].
    move: (Hb (1%g, 0%R)) => [ib Hltib <-].
    rewrite size_tuple in Hltia Hltib.
    rewrite ![nth (1%g, _) _ _](nth_map ord0); try by rewrite size_enum_ord.
    rewrite (_ : ia = Ordinal Hltia) //.
    rewrite (_ : ib = Ordinal Hltib) //.
    rewrite !nth_ord_enum /=.
    by move=> ->.
  Qed.

  Theorem shamir_correct : correct ShamirScheme.
  Proof.
    move=> randstate sec shares_n shares_t Hssptn.
    have uniq_xs := (uniq_subseq_perm_xs Hssptn).
    move: @shares_n Hssptn.
    rewrite /share {1}/ShamirScheme.
    set p := Poly _.
    move=> Hssptn.
    rewrite /combine /ShamirScheme.
    suff Heqpp :
      p = LagrangeInterpolation.interp_poly [tuple of map val (unzip1 shares_t)] [tuple of unzip2 shares_t];
      first by rewrite -Heqpp /p horner_cons GRing.mulr0 GRing.add0r.
    apply (LagrangeInterpolation.interpolation_unique uniq_xs).
    {
      apply (leq_trans (size_Poly _)).
      by rewrite size_tuple.
    }
    {
      move=> i.
      rewrite !tnth_map.
      set st_i := tnth _ _.
      have Hst_i : st_i \in shares_t; first by (apply/tnthP; exists i).
      move: Hst_i => /(mem_subseq_perm Hssptn) /(tnthP) [i' Hi'].
      move: Hi'.
      by rewrite tnth_map tnth_ord_tuple => ->.
    }
  Qed.

  Theorem shamir_secure : secure ShamirScheme.
  Proof.
    exists 1 => shares_tm1 [randstate0 [sec0 Hssp0]] sec.
    have Huniqst := uniq_subseq_perm Hssp0 (uniq_shares _ _).
    pose xs := [tuple of 0%R::map val (unzip1 shares_tm1)].
    have Huniqxs : uniq xs.
    {
      rewrite /xs /=.
      apply/andP; split; last by apply (uniq_subseq_perm_xs Hssp0).
      apply/mapP.
      move=> /= [x _ Heq0val].
      move: (valP x).
      rewrite GRing.unitfE Heq0val /=.
      apply/negP.
      by rewrite negbK.
    }
    pose cand_p :=
      LagrangeInterpolation.interp_poly xs [tuple of sec::unzip2 shares_tm1].
    pose cand_randstate :=
      let s := behead cand_p
      in [tuple of map (fun (i : 'I__) => (s`_i)%R) (ord_tuple tm1)].
    apply (eq_card1 (x:=cand_randstate)) => randstate.
    simpl in randstate.
    rewrite !inE.
    set cand_shares_n := share _ _ _.
    have Huniqcsn : uniq cand_shares_n by apply uniq_shares.
    move: @cand_shares_n Huniqcsn.
    rewrite /share /ShamirScheme.
    set p0 := Poly _.
    set cand_shares_n := tuple _.
    move=> Huniqcsn.
    apply (sameP idP).
    apply/(iffP idP).
    {
      move=> /eqP Heq; move: @p0 @cand_shares_n Huniqcsn.
      rewrite {}Heq; clear randstate.
      rewrite /share /ShamirScheme.
      set p0 := Poly _.
      rewrite (_:p0=cand_p); last first.
      {
        clear Hssp0 randstate0 sec0 Huniqst.
        apply polyP => i.
        rewrite {}/p0 coef_Poly.
        case: i => [|i].
        {
          rewrite [nth _ _ _]/=.
          rewrite -horner_coef0 (_:0%R=tnth xs ord0) //.
          by rewrite (LagrangeInterpolation.correct_interp_poly (T:=T)) //.
        }
        {
          rewrite (_:((_::cand_randstate)`_i.+1 = cand_randstate`_i)%R) //.
          case: (ltnP i tm1) => Hi.
          {
            rewrite (_:i=Ordinal Hi) // -tnth_nth.
            rewrite {}/cand_randstate.
            by rewrite tnth_map tnth_ord_tuple nth_behead.
          }
          {
            rewrite nth_default; last by rewrite size_map size_tuple.
            rewrite nth_default //.
            by apply (leq_trans (LagrangeInterpolation.size_interp_poly _ Huniqxs)).
          }
        }
      }
      clear cand_randstate p0.
      set cand_shares_n := tuple _.
      move=> Huniqcsn.
      apply/mem_uniq_subseq_permP => // s Hmemsst.
      clear Huniqcsn Huniqst.
      apply/tnthP.
      move: (mem_subseq_perm Hssp0 Hmemsst) => /tnthP [i_n Heqsi].
      clear Hssp0.
      exists i_n.
      move: Heqsi.
      rewrite !tnth_map tnth_ord_tuple.
      set i := enum_val _.
      rewrite (surjective_pairing s); move=> [<- _].
      apply injective_projections => //=.
      move: Hmemsst => /tnthP [i_t Hi_t].
      rewrite (_ : val s.1 = tnth xs (lift ord0 i_t)); last first.
      {
        rewrite (tnth_nth 0%R) /= -tnth_nth.
        rewrite tnth_map tnth_map.
        by rewrite Hi_t.
      }
      rewrite (LagrangeInterpolation.correct_interp_poly _ Huniqxs).
      rewrite (tnth_nth 0%R) /= -tnth_nth.
      rewrite tnth_map.
      by rewrite Hi_t.
    }
    {
      move=> Hsspstcsn.
      suff Heqpp : p0 = cand_p.
      {
        move: Heqpp.
        rewrite /p0 /cand_randstate => <-.
        apply/eqP; apply eq_from_tnth => i.
        by rewrite tnth_map nth_behead coef_Poly tnth_ord_tuple /= -tnth_nth.
      }
      apply (LagrangeInterpolation.interpolation_unique Huniqxs);
        first by (apply (leq_trans (size_Poly _)); rewrite size_tuple).
      move=> [[|i] Hi]; rewrite !(tnth_nth 0%R);
        first by rewrite horner_coef0 coef_Poly.
      rewrite /xs /=.
      rewrite (nth_map 1%g); last by rewrite size_tuple.
      rewrite (nth_map (1%g,0%R)); last by rewrite size_tuple.
      rewrite (nth_map (1%g,0%R)); last by rewrite size_tuple.
      rewrite ltnS in Hi.
      pose io := Ordinal Hi.
      rewrite (_:i = io) // -tnth_nth.
      have Hmemsi := mem_tnth io shares_tm1.
      move: (mem_uniq_subseq_permP Huniqst Huniqcsn Hsspstcsn _ Hmemsi) => /tnthP [i_n ->].
      by rewrite tnth_map tnth_ord_tuple.
    }
  Qed.
End ShamirScheme.
