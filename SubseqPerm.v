Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Local Set Warnings "all".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SubseqPerm.
  Variable T : eqType.
  Implicit Type s : seq T.

  Definition subseq_perm s1 s2
    := all [pred x | count_mem x s1 <= count_mem x s2] (s1 ++ s2).

  Lemma subseq_count s1 s2 : subseq s1 s2 -> forall a, count a s1 <= count a s2.
  Proof.
    elim: s2 s1 => [|y s2 IHs2] [|x s1] //.
    rewrite [subseq _ _]/=.
    case: (x == y) /eqP => [-> Hss32 /= a|_ Hss32 a].
    { apply leq_add => //. by apply IHs2. }
    rewrite [count _ (_::s2)]/=.
    apply (leq_trans (IHs2 _ Hss32 _)).
    by apply leq_addl.
  Qed.


  Theorem subseq_permP s1 s2 : reflect (exists2 s3, subseq s1 s3 & perm_eq s3 s2) (subseq_perm s1 s2).
  Proof.
    apply: (iffP allP) => /= [Hcountle12|[s3 Hss13 /permP Heqcount] x _]; last first.
    { rewrite -Heqcount. by apply subseq_count. }
    exists (s1 ++ foldr (@rem T) s2 s1); first by apply prefix_subseq.
    elim: s1 s2 Hcountle12 => [//|x s1 IHs1] s2 Hcountle12.
    have aIHs1 : perm_eq (s1 ++ foldr (@rem T) s2 s1) s2.
    {
      apply IHs1 => w Hmemw.
      have Hcountw : (count_mem w) (x :: s1) <= (count_mem w) s2.
      {
        apply Hcountle12.
        move: Hmemw.
        rewrite !mem_cat.
        move=> /orP Hmemw.
        apply/orP.
        case: Hmemw => [Hmemwxs1|Hmemws2].
        { left. rewrite inE. apply/orP. by right. }
        { by right. }
      }
      move: Hcountw => /= Hcountw.
      by apply (leq_trans (leq_addl _ _) Hcountw).
    }
    rewrite /= -cat1s perm_catCA cat1s.
    rewrite -(perm_catl _ (perm_to_rem _)) //.
    have Hcountx : (count_mem x) (x :: s1) <= (count_mem x) s2.
    {
      apply Hcountle12.
      by rewrite inE eq_refl.
    }
    move: Hcountx.
    rewrite -(permP aIHs1) /= eq_refl /=.
    rewrite count_cat addnC leq_add2l.
    by rewrite -has_count has_pred1.
  Qed.


  Theorem uniq_subseq_perm s1 s2 : subseq_perm s1 s2 -> uniq s2 -> uniq s1.
  Proof.
    move=> /subseq_permP [s3 Hss13 Hperm32] Huniqs2.
    apply (subseq_uniq Hss13).
    by rewrite (perm_uniq Hperm32).
  Qed.


  Theorem mem_subseq_perm s1 s2 : subseq_perm s1 s2 -> {subset s1 <= s2}.
  Proof.
    move=> /subseq_permP [s3 Hss13 Hperm32] x.
    rewrite -(perm_mem Hperm32).
    by apply mem_subseq.
  Qed.


  Theorem mem_uniq_subseq_permP s1 s2
    : uniq s1 -> uniq s2 -> reflect {subset s1 <= s2} (subseq_perm s1 s2).
  Proof.
    move=> Huniqs1 Huniqs2.
    apply/(iffP idP); first by apply mem_subseq_perm.
    move=> Hss12.
    apply/allP => x /=.
    rewrite mem_cat => /orP.
    rewrite !count_uniq_mem //.
    case.
    {
      move=> Hmemxs1 /=.
      by rewrite Hmemxs1 (Hss12 _ Hmemxs1).
    }
    {
      move=> -> /=.
      by apply leq_b1.
    }
  Qed.
End SubseqPerm.
