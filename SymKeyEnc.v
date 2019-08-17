Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp Require Import fingroup.
Local Set Warnings "all".

Set Implicit Arguments.
Unset Strict Implicit.

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

  Theorem ciphertext_size_ge : #|M| <= #|C|.
  Proof.
    rewrite -(cardC (mem_seq (image (enc i k0) M))).
    apply/(leq_trans _ (leq_addr _ _)).
    rewrite card_image => //.
    by apply (can_inj (correct_i k0)).
  Qed.

  Theorem key_size_ge : #|C| <= #|K|.
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
