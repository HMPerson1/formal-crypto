Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Local Set Warnings "all".

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
    elim: s1 s2 Hcountle12 => [|x s1 IHs1] s2 Hcountle12.
    { exists s2 => //. by apply sub0seq. }
    {
      elim: s2 Hcountle12 => [|y s2 IHs2] Hcountle12.
      {
        have Hle := Hcountle12 x (mem_head _ (s1 ++ [::])).
        by rewrite /= eq_refl in Hle.
      }
      {
        have H : exists2 s3 : seq T, subseq s1 s3 & perm_eq s3 (y::s2).
        {
          apply IHs1 => w Hmemw.
          have Hcw : (count_mem w) (x :: s1) <= (count_mem w) (y :: s2).
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
          move: Hcw => /= Hcw.
          by apply (leq_trans (leq_addl _ _) Hcw).
        }
        move: H => [s3 Hss13 /permP Hce32].
        have [sc1 /permP Hce31c1] := perm_to_subseq Hss13.
        have Hmemxs1c : x \in sc1.
        {
          have Hcx : (count_mem x) (x :: s1) <= (count_mem x) (y :: s2).
          {
            apply Hcountle12.
            apply/orP.
            by left.
          }
          move: Hcx.
          rewrite -Hce32 /= eq_refl /=.
          rewrite Hce31c1 count_cat addnC leq_add2l.
          by rewrite -has_count has_pred1.
        }
        exists (x :: s1 ++ (rem x sc1)).
        {
          rewrite /= eq_refl /=.
          by apply prefix_subseq.
        }
        {
          rewrite -cat1s perm_catCA cat1s.
          have Hpr := perm_to_rem Hmemxs1c.
          rewrite perm_sym in Hpr.
          rewrite (perm_catl _ Hpr).
          apply/permP => w.
          by rewrite -Hce31c1 Hce32.
        }
      }
    }
  Qed.
End SubseqPerm.

Arguments subseq_perm {T}.
