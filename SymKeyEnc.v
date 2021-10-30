Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import fingroup.
Local Set Warnings "all".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section Def.
  Variable K M C : finType.

  Record impl := Impl {enc : K -> M -> C; dec : K -> C -> M}.

  Definition correct (i : impl)
    := forall k, cancel (enc i k) (dec i k).
  Definition secure (i : impl)
    := exists n, forall c m, #|[pred k | enc i k m == c]| = n.

End Def.


Section Theory.
  Variable K M C : finType.
  Variable i : impl K M C.
  Hypothesis correct_i : correct i.
  Hypothesis secure_i : secure i.
  Variable (k0 : K) (m0 : M).

  Theorem card_ciphertext_ge : #|M| <= #|C|.
  Proof.
    rewrite -(cardC (mem_seq (image (enc i k0) M))).
    apply/(leq_trans _ (leq_addr _ _)).
    rewrite card_image => //.
    by apply (can_inj (correct_i k0)).
  Qed.

  Theorem card_key_ge : #|C| <= #|K|.
  Proof.
    have find_k : forall c m, exists k, enc i k m == c.
    {
      move=> c m.
      move: secure_i => [n Hsecuren].
      have Hgtn : 0 < n.
      {
        rewrite -(Hsecuren (enc i k0 m0) m0).
        by apply/card_gt0P; exists k0; rewrite inE.
      }
      move: Hgtn; rewrite -(Hsecuren c m).
      by move/card_gt0P => [k Hk]; exists k.
    }
    pose fun_c2k c := xchoose (find_k c m0).
    rewrite -(cardC (mem_seq (image fun_c2k C))).
    apply/(leq_trans _ (leq_addr _ _)).
    rewrite card_image => //.
    apply (can_inj (g:=(enc i)^~ m0)).
    move=> c; rewrite /fun_c2k.
    by apply (eqP (xchooseP (find_k _ _))).
  Qed.
End Theory.


Section OneTimePad.
  Variable T : finGroupType.

  Definition one_time_pad : impl T T T
    := Impl mulg (mulg \o invg).

  Theorem correct_otp : correct one_time_pad.
  Proof.
    move=> k m /=. by rewrite mulgA mulVg mul1g.
  Qed.

  Theorem secure_otp : secure one_time_pad.
  Proof.
    exists 1.
    move=> c m /=.
    apply (eq_card1 (x:=(c * m^-1)%g)).
    move=> k.
    rewrite !inE.
    rewrite -(inj_eq (mulIg (invg m))).
    by rewrite -mulgA mulgV mulg1.
  Qed.
End OneTimePad.


Section Pair.
  Variable K1 M1 C1 : finType.
  Variable i1 : impl K1 M1 C1.
  Hypothesis correct_i1 : correct i1.
  Hypothesis secure_i1 : secure i1.

  Variable K2 M2 C2 : finType.
  Variable i2 : impl K2 M2 C2.
  Hypothesis correct_i2 : correct i2.
  Hypothesis secure_i2 : secure i2.

  Local Notation K := [finType of (K1 * K2)].
  Local Notation M := [finType of (M1 * M2)].
  Local Notation C := [finType of (C1 * C2)].

  Definition compose_pair : impl K M C
    := Impl
         (fun '(k1, k2) '(m1, m2) => (enc i1 k1 m1, enc i2 k2 m2))
         (fun '(k1, k2) '(c1, c2) => (dec i1 k1 c1, dec i2 k2 c2)).

  Theorem correct_compose_pair : correct compose_pair.
  Proof.
    by move=> [k1 k2] [m1 m2] /=; rewrite correct_i1 correct_i2.
  Qed.

  Theorem secure_compose_pair : secure compose_pair.
  Proof.
    move: secure_i1 => [n1 Hsecure1].
    move: secure_i2 => [n2 Hsecure2].
    exists (n1 * n2) => [[c1 c2] [m1 m2]].
    rewrite -(Hsecure1 c1 m1) -(Hsecure2 c2 m2) -cardX.
    apply eq_card => [[k1 k2]].
    by rewrite !inE /=.
  Qed.
End Pair.


Section BijectTuplePair.
  Variable T : Type.
  Variable n : nat.

  Definition pair_to_tuple_cons (p : (T * n.-tuple T)) := [tuple of p.1 :: p.2].
  Definition tuple_cons_to_pair (t : n.+1.-tuple T) := (thead t, behead_tuple t).

  Theorem can_pttc_tctp : cancel pair_to_tuple_cons tuple_cons_to_pair.
  Proof.
    move=> [h t].
    rewrite /pair_to_tuple_cons /tuple_cons_to_pair /= theadE.
    set ht := tuple _.
    suff H : t = behead_tuple ht by rewrite H.
    rewrite {}/ht.
    apply/eq_from_tnth => i.
    by rewrite tnth_behead !(tnth_nth h) /= inordK // ltnS.
  Qed.

  Theorem can_tctp_pttc : cancel tuple_cons_to_pair pair_to_tuple_cons.
  Proof.
    move=> t.
    rewrite /pair_to_tuple_cons /tuple_cons_to_pair /=.
    by symmetry; apply tuple_eta.
  Qed.

  Theorem bij_tctp : bijective tuple_cons_to_pair.
  Proof. exact (Bijective can_tctp_pttc can_pttc_tctp). Qed.
End BijectTuplePair.

Arguments bij_tctp {T n}.


Section Tuple.
  Variable K0 M0 C0 : finType.
  Variable i0 : impl K0 M0 C0.
  Hypothesis correct_i0 : correct i0.
  Hypothesis secure_i0 : secure i0.
  Variable n : nat.
  Local Notation K := [finType of (n.-tuple K0)].
  Local Notation M := [finType of (n.-tuple M0)].
  Local Notation C := [finType of (n.-tuple C0)].

  Definition lift_tuple2 {A B C} (f : A -> B -> C) (a : n.-tuple A) (b : n.-tuple B)
    := map_tuple (prod_curry f) (zip_tuple a b).

  Definition compose : impl K M C
    := Impl (lift_tuple2 (enc i0)) (lift_tuple2 (dec i0)).

  Lemma tnth_zip {A B} n' (a : n'.-tuple A) (b : n'.-tuple B) j
    : tnth (zip_tuple a b) j = (tnth a j, tnth b j).
  Proof.
    rewrite /tnth nth_zip_cond size_zip !size_tuple minnn ltn_ord.
    by apply injective_projections; apply set_nth_default; rewrite size_tuple ltn_ord.
  Qed.

  Theorem correct_compose : correct compose.
  Proof.
    move=> k m /=; apply eq_from_tnth => j /=.
    by rewrite tnth_map tnth_zip tnth_map tnth_zip /prod_curry correct_i0.
  Qed.

  Theorem secure_compose : secure compose.
  Proof.
    move: secure_i0 => [l Hsecure]; exists (l^n) => c m.
    rewrite /compose /lift_tuple2 /=.
    have cHsecure cm := Hsecure cm.1 cm.2.
    elim: n c m => [|n' IHn] c m.
    - rewrite expn0.
      rewrite (eq_card1 (x:=[tuple])) // => k.
      rewrite !inE.
      by rewrite [k]tuple0 [c]tuple0 [map_tuple _ _]tuple0.
    - rewrite expnS.
      rewrite -(IHn (behead_tuple c) (behead_tuple m)).
      rewrite -(Hsecure (thead c) (thead m)).
      rewrite -cardX.
      rewrite !cardE -(size_map (@tuple_cons_to_pair _ _)).
      apply perm_size.
      apply uniq_perm;
        [by rewrite (map_inj_uniq (bij_inj bij_tctp)); apply enum_uniq|exact: enum_uniq|]
        => [[headk tailk]].
      rewrite -{1}[(headk, tailk)]can_pttc_tctp (mem_map (bij_inj bij_tctp)) !mem_enum !inE.
      apply/(sameP idP)/(iffP idP).
      + move=> /andP [Hheadk Htailk].
        apply/eqP/eq_from_tnth => j.
        rewrite [m]tuple_eta [c]tuple_eta.
        rewrite tnth_map tnth_zip /prod_curry.
        move: j => [[|j] Hj].
        * rewrite (_:Hj=ltn0Sn n'); last by apply bool_irrelevance.
          by rewrite !tnth0; apply/eqP.
        * rewrite (tnth_nth (headk)) (tnth_nth (thead m)) (tnth_nth (thead c)) /=.
          rewrite (_ : behead c = behead_tuple c) //.
          rewrite ltnS in Hj.
          pose oj := Ordinal Hj.
          rewrite (_:j=oj) //.
          rewrite -!tnth_nth.
          rewrite -(eqP Htailk).
          by rewrite tnth_map tnth_zip /prod_curry.
      + move=> /eqP <- /=.
        apply/andP; split.
        * by rewrite /thead tnth_map tnth_zip.
        * apply/eqP/eq_from_tnth => j.
          rewrite tnth_behead !tnth_map !tnth_zip /=.
          rewrite {2}[m]tuple_eta.
          rewrite [tnth _ (inord _)](tnth_nth headk).
          rewrite [tnth _ (inord _)](tnth_nth (thead m)).
          rewrite inordK /=; last by rewrite ltnS.
          by rewrite -!tnth_nth.
  Qed.
End Tuple.
