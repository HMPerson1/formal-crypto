Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype tuple bigop.
From mathcomp Require Import ssralg poly.
Local Set Warnings "all".

Set Implicit Arguments.
Unset Strict Implicit.

Section LagrangeInterpolation.
  Variable T : fieldType.
  Variable k : nat.
  Variable xs : k.+1.-tuple T.
  Variable ys : k.+1.-tuple T.

  Hypothesis uniq_xs : uniq xs.

  Local Notation "'x_ i" := (tnth xs i) (at level 2).
  Local Notation "'y_ i" := (tnth ys i) (at level 2).

  Definition basis j : {poly T}
    := \prod_(m < k.+1 | m != j) (('X - 'x_m %:P)/ ('x_j - 'x_m) %:P).

  Lemma wf_basis0 i j : i != j -> root (basis j) 'x_i.
  Proof.
    move=> Hij. rewrite /basis /index_enum -enumT. apply/factor_theorem.
    have Hue := enum_uniq 'I_k.+1.
    rewrite -big_filter -rem_filter //.
    rewrite (big_rem i) /=; last first.
    {
      rewrite rem_filter // mem_filter /=. apply/andP. split => //; last by apply mem_enum.
    }
    rewrite !rem_filter //; last by apply filter_uniq.
    rewrite big_filter big_filter_cond /=. rewrite -GRing.mulrA GRing.mulrC.
    set q := (_ * \prod_(i <- _ | _) _)%R.
    by exists q.
  Qed.

  Lemma distinct_x : forall i j, i != j -> ('x_j - 'x_i != 0)%R.
  Proof.
    move=> i j.
    apply contra => /eqP /GRing.subr0_eq.
    move: uniq_xs => /uniqP Hinj_nth.
    rewrite size_tuple in Hinj_nth.
    rewrite !(tnth_nth 0%R).
    move=> H; apply/eqP.
    apply ord_inj.
    apply (Hinj_nth 0%R _) => //; [by rewrite inE|by rewrite inE].
  Qed.

  Lemma wf_basis1 j : ((basis j).['x_j] = 1)%R.
  Proof.
    rewrite /basis horner_prod.
    elim/big_ind: _ => // [a b Ha Hb| i Hij].
    { rewrite Ha Hb. by apply GRing.mulr1. }
    rewrite polyC_inv hornerM hornerC hornerXsubC GRing.mulrV //.
    rewrite GRing.unitfE.
    by apply (distinct_x Hij).
  Qed.

  Lemma size_basis j : size (basis j) <= k.+1.
  Proof.
    apply (leq_trans (size_prod_leq _ _)). simpl.
    set sum_size := \sum_(_ <- _ | _) _.
    rewrite (_ : sum_size = \sum_(i < k.+1 | i != j) 2); last first.
    {
      rewrite /sum_size. elim/big_rec2: _ => [|i x y Hij ->] //.
      rewrite polyC_inv GRing.mulrC size_Cmul; last by apply (GRing.invr_neq0 (distinct_x Hij)).
      by rewrite size_XsubC.
    }
    rewrite sum_nat_const /=.
    rewrite (_ : @card _ (@mem _ (predPredType 'I_k.+1) (fun i => i != j)) = k); last first.
    {
      apply (eq_card_trans (A:=predC1 j)); first by rewrite cardC1 card_ord.
      move=> i. by rewrite inE.
    }
    rewrite -add1n mulnC mul2n -addnn.
    rewrite -addnBA; last by apply leq_addr.
    by rewrite addnK.
  Qed.

  Definition interp_poly
    : {poly T}
    := \sum_(j < k.+1) (('y_j %:P) * basis j).

  Theorem size_interp_poly : size interp_poly <= k.+1.
  Proof.
    apply (leq_trans (size_sum _ _ _)). apply/bigmax_leqP => i _.
    apply (leq_trans (size_mul_leq _ _)).
    rewrite {2}(_ : k.+1 = k.+2.-1) //.
    rewrite -!subn1 leq_sub //.
    rewrite -[k.+2]addn1 addnC leq_add //; first apply size_basis.
    by apply size_polyC_leq1.
  Qed.

  Definition correct p := forall i, (p.['x_i])%R = 'y_i.

  Theorem correct_interp_poly : correct interp_poly.
  Proof.
    move=> i.
    rewrite horner_sum.
    rewrite (big_rem i) /=; last (rewrite /index_enum -enumT; by apply mem_enum).
    rewrite rem_filter; last (rewrite /index_enum -enumT; by apply enum_uniq).
    rewrite big_filter /=.
    set sum_basis := (\sum_(_ <- _ | _) _)%R.
    rewrite (_ : sum_basis = 0)%R; last first.
    {
      rewrite /sum_basis. elim/big_ind: _ => // [a b -> ->|m Hmi]; first by apply GRing.addr0.
      rewrite hornerM.
      rewrite (eqP (wf_basis0 _)); last by rewrite eq_sym.
      by apply GRing.mulr0.
    }
    rewrite hornerCM.
    rewrite wf_basis1.
    by rewrite GRing.addr0 GRing.mulr1.
  Qed.

  Theorem interpolation_unique (po : {poly T})
    : size po <= k.+1 -> correct po -> po = interp_poly.
  Proof.
    move=> Hsize_po Hct_po.
    apply GRing.subr0_eq.
    apply (roots_geq_poly_eq0 (rs:=xs)) => //.
    {
      apply/allP => x /tnthP [i ->].
      rewrite /root hornerD.
      by rewrite Hct_po hornerN correct_interp_poly GRing.addrN.
    }
    {
      rewrite size_tuple. apply (leq_trans (size_add _ _)). rewrite geq_max. apply/andP.
      split=> //.
      rewrite size_opp.
      by apply size_interp_poly.
    }
  Qed.
End LagrangeInterpolation.
