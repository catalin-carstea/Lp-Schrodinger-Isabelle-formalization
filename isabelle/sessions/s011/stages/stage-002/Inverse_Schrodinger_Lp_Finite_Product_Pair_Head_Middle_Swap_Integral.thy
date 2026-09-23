theory Inverse_Schrodinger_Lp_Finite_Product_Pair_Head_Middle_Swap_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Four_Factor_Middle_Swap_Integral"
begin

section \<open>Middle swap for two inserted finite-product families\<close>

context product_sigma_finite
begin

theorem slp_integral_inserted_pair_head_middle_swap:
  fixes f :: "(('a \<times> ('i \<Rightarrow> 'a)) \<times>
      ('a \<times> ('i \<Rightarrow> 'a))) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes finite_I: "finite I"
    and f_integrable:
      "integrable
        (((M i \<Otimes>\<^sub>M PiM I M) \<Otimes>\<^sub>M
          (M i \<Otimes>\<^sub>M PiM I M))) f"
  shows
    "integral\<^sup>L
        (((M i \<Otimes>\<^sub>M PiM I M) \<Otimes>\<^sub>M
          (M i \<Otimes>\<^sub>M PiM I M))) f =
      integral\<^sup>L
        (((M i \<Otimes>\<^sub>M M i) \<Otimes>\<^sub>M
          ((PiM I M) \<Otimes>\<^sub>M (PiM I M))))
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          f ((pos_head, pos_tail), (neg_head, neg_tail)))"
proof -
  have head_sigma: "sigma_finite_measure (M i)"
    by (rule sigma_finite_measures)
  have tail_sigma: "sigma_finite_measure (PiM I M)"
    by (rule sigma_finite[OF finite_I])
  show ?thesis
    by (rule slp_integral_four_factor_middle_swap[OF
          head_sigma tail_sigma head_sigma tail_sigma f_integrable])
qed

end


end
