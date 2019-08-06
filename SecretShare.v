Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat fintype tuple.
From mathcomp Require Import ssralg finalg fingroup poly bigop seq.
Local Set Warnings "all".

From FC Require LagrangeInterpolation.
From FC Require Import SubseqPerm.

Set Implicit Arguments.
Unset Strict Implicit.

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
    exists c, forall (shares_tm1 : (tm1).-tuple Share) randstate sec,
        let shares_n := share i randstate sec in
        #|[pred s | subseq_perm (s :: shares_tm1) shares_n]| = c.
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


  Theorem shamir_correct : correct ShamirScheme.
  Proof.
    move=> randstate sec.
    remember (share _ _ _) as shares_n.
    move=> shares_n0. rewrite {}/shares_n0.
    simpl in Heqshares_n.
    move=> shares_t /subseq_permP [permshares_n Hpermshares_n_sub Hpermshares_n_perm].
    set p := cons_poly _ _ in Heqshares_n.
    simpl.
    suff Heqpp :
      p = LagrangeInterpolation.interp_poly [tuple of map val (unzip1 shares_t)] [tuple of unzip2 shares_t];
      first by rewrite -Heqpp /p horner_cons GRing.mulr0 GRing.add0r.
    have Hmem_shares : {subset shares_t <= shares_n}.
    { move=> x. rewrite -(perm_mem Hpermshares_n_perm). by apply (mem_subseq Hpermshares_n_sub). }
    apply LagrangeInterpolation.interpolation_unique; last first; last 2 first.
    {
      rewrite size_cons_poly. set b := _ && _. elim: b => //.
      apply (leq_trans (size_Poly _)). by rewrite size_tuple.
    }
    {
      rewrite /= map_inj_in_uniq; last by move=> x y _ _; apply val_inj.
      rewrite map_inj_in_uniq; last first.
      {
        move=> a b.
        move=> /Hmem_shares Ha /Hmem_shares Hb.
        move: Ha Hb => /nthP /= Ha /nthP /= Hb.
        move: (Ha (1%g, 0%R)) => [ia Hltia <-].
        move: (Hb (1%g, 0%R)) => [ib Hltib <-].
        rewrite size_tuple in Hltia Hltib.
        rewrite Heqshares_n.
        rewrite ![nth (1%g, _) _ _](nth_map ord0); try by rewrite size_enum_ord.
        rewrite (_ : ia = Ordinal Hltia) //.
        rewrite (_ : ib = Ordinal Hltib) //.
        rewrite !nth_ord_enum /=.
        by move=> ->.
      }
      apply (subseq_uniq Hpermshares_n_sub).
      rewrite (perm_uniq Hpermshares_n_perm).
      rewrite Heqshares_n /=.
      rewrite map_inj_in_uniq; first by apply enum_uniq.
      move=> x y _ _ [Heq _].
      move: Heq => /enum_val_inj.
      rewrite /widen_ord => Heq.
      inversion Heq.
      by apply ord_inj in H0.
    }
    {
      move=> i.
      rewrite !tnth_map.
      set st_i := tnth _ _.
      have Hst_i : st_i \in shares_t; first by (apply/tnthP; exists i).
      move: Hst_i => /Hmem_shares /(tnthP) [i' Hi'].
      move: Hi'.
      by rewrite Heqshares_n tnth_map tnth_ord_tuple => ->.
    }
  Qed.
End ShamirScheme.
