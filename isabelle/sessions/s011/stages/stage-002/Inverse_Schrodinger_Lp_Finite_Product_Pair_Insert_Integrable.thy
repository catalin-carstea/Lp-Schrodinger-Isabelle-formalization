theory Inverse_Schrodinger_Lp_Finite_Product_Pair_Insert_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Pair_Insert_Integral"
begin

section \<open>Integrability for two inserted finite-product families\<close>

context product_sigma_finite
begin

theorem slp_integrable_inserted_pair_heads_tails:
  fixes f :: "(('i \<Rightarrow> 'a) \<times> ('i \<Rightarrow> 'a)) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes finite_I: "finite I"
    and i_notin: "i \<notin> I"
    and f_integrable:
      "integrable
        ((PiM (insert i I) M) \<Otimes>\<^sub>M (PiM (insert i I) M)) f"
  shows
    "integrable
      ((M i \<Otimes>\<^sub>M M i) \<Otimes>\<^sub>M
        ((PiM I M) \<Otimes>\<^sub>M (PiM I M)))
      (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
        f (pos_tail(i := pos_head), neg_tail(i := neg_head)))"
proof -
  let ?T = "PiM I M"
  let ?F = "PiM (insert i I) M"
  let ?S = "M i \<Otimes>\<^sub>M ?T"
  let ?U = "?F \<Otimes>\<^sub>M ?F"
  let ?V = "?S \<Otimes>\<^sub>M ?S"
  let ?update = "\<lambda>(head, tail). tail(i := head)"
  let ?pair_update = "\<lambda>(positive, negative).
    (?update positive, ?update negative)"
  let ?g = "\<lambda>((pos_head, pos_tail), (neg_head, neg_tail)).
    f (pos_tail(i := pos_head), neg_tail(i := neg_head))"
  have F_sigma: "sigma_finite_measure ?F"
    by (rule sigma_finite) (use finite_I in simp)
  have T_sigma: "sigma_finite_measure ?T"
    by (rule sigma_finite[OF finite_I])
  have head_sigma: "sigma_finite_measure (M i)"
    by (rule sigma_finite_measures)
  have swap_measurable:
      "(\<lambda>(head, tail). (tail, head))
        \<in> measurable ?S (?T \<Otimes>\<^sub>M M i)"
    by (rule measurable_pair_swap')
  have add_measurable:
      "(\<lambda>(tail, head). tail(i := head))
        \<in> measurable (?T \<Otimes>\<^sub>M M i) ?F"
    by (rule measurable_add_dim)
  have update_measurable: "?update \<in> measurable ?S ?F"
    using measurable_compose[OF swap_measurable add_measurable]
    by (simp only: comp_def split_beta' fst_conv snd_conv)
  have pair_update_measurable:
      "?pair_update \<in> measurable ?V ?U"
  proof -
    have raw:
        "(\<lambda>coordinates.
          (?update (fst coordinates), ?update (snd coordinates)))
          \<in> measurable ?V ?U"
      by (rule measurable_Pair)
        (use update_measurable in measurable)
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have single_distribution:
      "distr ?S ?F ?update = ?F"
    by (rule slp_distr_product_insert_head[OF finite_I i_notin])
  have pair_distribution:
      "distr ?V ?U ?pair_update = ?U"
  proof -
    have raw:
        "distr ?S ?F ?update \<Otimes>\<^sub>M distr ?S ?F ?update =
          distr ?V ?U
            (\<lambda>(positive, negative).
              (?update positive, ?update negative))"
      by (rule pair_measure_distr[OF
            update_measurable update_measurable])
        (use F_sigma single_distribution in simp)
    show ?thesis
      using raw single_distribution by (simp only: split_beta')
  qed
  have grouped_integrable: "integrable ?V ?g"
  proof -
    have distr_integrable:
        "integrable (distr ?V ?U ?pair_update) f"
      using pair_distribution f_integrable by simp
    have raw:
        "integrable ?V (\<lambda>coordinates. f (?pair_update coordinates))"
      by (rule integrable_distr[OF
            pair_update_measurable distr_integrable])
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have interleaved_integrable:
      "integrable
        ((M i \<Otimes>\<^sub>M M i) \<Otimes>\<^sub>M (?T \<Otimes>\<^sub>M ?T))
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          ?g ((pos_head, pos_tail), (neg_head, neg_tail)))"
    by (rule slp_integrable_four_factor_middle_swap[OF
          head_sigma T_sigma head_sigma T_sigma grouped_integrable])
  have interleaved_integrand:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          ?g ((pos_head, pos_tail), (neg_head, neg_tail))) =
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          f (pos_tail(i := pos_head), neg_tail(i := neg_head)))"
    by (rule ext) (auto split: prod.split)
  show ?thesis
    using interleaved_integrable unfolding interleaved_integrand .
qed

end

end
