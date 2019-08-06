Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype fintype.
From mathcomp Require Import fingroup.
Local Set Warnings "all".

Set Implicit Arguments.
Unset Strict Implicit.

Section Def.
  Variable K M C : finType.

  Record impl := Impl {enc : K -> M -> C; dec : K -> C -> M}.

  Definition correct (i : impl)
    := forall k m, dec i k (enc i k m) == m.
  Definition secure (i : impl)
    := exists n, forall c m, #|[pred k | enc i k m == c]| = n.

End Def.


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
