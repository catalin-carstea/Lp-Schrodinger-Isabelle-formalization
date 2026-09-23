theory Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Finite_Target_Uniform_Power
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Finite_Target"
begin

section \<open>Uniform finite-target convolution power control\<close>

theorem slp_positive_ennreal_convolution_finite_target_uniform_power:
  fixes t A B :: real
    and F G :: "slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
  assumes t_lower: "1 < t"
    and A_nonnegative: "0 \<le> A"
    and B_nonnegative: "0 \<le> B"
    and F_lp: "\<And>root. slp_positive_ennreal_lp_on_plane
      (slp_mixed_unweighted_branch_exponent t) (F root)"
    and G_lp: "\<And>root. slp_positive_ennreal_lp_on_plane
      (slp_mixed_unweighted_branch_exponent t) (G root)"
    and F_power_bound:
      "\<And>root. integral\<^sup>L lborel
        (\<lambda>x. enn2real (F root x) powr
          slp_mixed_unweighted_branch_exponent t) \<le> A"
    and G_power_bound:
      "\<And>root. integral\<^sup>L lborel
        (\<lambda>x. enn2real (G root x) powr
          slp_mixed_unweighted_branch_exponent t) \<le> B"
  shows cap_nonnegative:
      "0 \<le> (A * B) * (A * B) powr ((t - 1) / 2)"
    and all_convolutions_Lt:
      "\<And>root. slp_positive_ennreal_lp_on_plane t
        (slp_positive_ennreal_convolution (F root) (G root))"
    and uniform_power:
      "\<And>root. integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_positive_ennreal_convolution (F root) (G root) out) powr t)
        \<le> (A * B) * (A * B) powr ((t - 1) / 2)"
proof -
  have cap_product_nonnegative: "0 \<le> A * B"
    by (rule mult_nonneg_nonneg[OF A_nonnegative B_nonnegative])
  show "0 \<le> (A * B) * (A * B) powr ((t - 1) / 2)"
    using cap_product_nonnegative by simp
  show "slp_positive_ennreal_lp_on_plane t
      (slp_positive_ennreal_convolution (F root) (G root))"
    for root
    by (rule slp_positive_ennreal_convolution_finite_target(1)[OF
          t_lower F_lp G_lp])
  show "integral\<^sup>L lborel
      (\<lambda>out. enn2real
        (slp_positive_ennreal_convolution (F root) (G root) out) powr t)
      \<le> (A * B) * (A * B) powr ((t - 1) / 2)"
    for root
  proof -
    let ?I_F = "integral\<^sup>L lborel
      (\<lambda>x. enn2real (F root x) powr
        slp_mixed_unweighted_branch_exponent t)"
    let ?I_G = "integral\<^sup>L lborel
      (\<lambda>x. enn2real (G root x) powr
        slp_mixed_unweighted_branch_exponent t)"
    let ?P = "?I_F * ?I_G"
    let ?beta = "(t - 1) / 2"
    have endpoint:
        "integral\<^sup>L lborel
            (\<lambda>out. enn2real
              (slp_positive_ennreal_convolution (F root) (G root) out)
              powr t)
          \<le> ?P * ?P powr ?beta"
      by (rule slp_positive_ennreal_convolution_finite_target(2)[OF
            t_lower F_lp G_lp])
    have I_F_nonnegative: "0 \<le> ?I_F"
      by (rule integral_nonneg_AE) simp
    have I_G_nonnegative: "0 \<le> ?I_G"
      by (rule integral_nonneg_AE) simp
    have product_nonnegative: "0 \<le> ?P"
      by (rule mult_nonneg_nonneg[OF I_F_nonnegative I_G_nonnegative])
    have product_bound: "?P \<le> A * B"
      by (rule mult_mono[OF F_power_bound G_power_bound
            A_nonnegative I_G_nonnegative])
    have beta_nonnegative: "0 \<le> ?beta"
      using t_lower by simp
    have power_bound: "?P powr ?beta \<le> (A * B) powr ?beta"
      by (rule powr_mono2[OF beta_nonnegative product_nonnegative
            product_bound])
    have power_nonnegative: "0 \<le> ?P powr ?beta"
      by simp
    have combined_bound:
        "?P * ?P powr ?beta \<le>
          (A * B) * (A * B) powr ?beta"
      by (rule mult_mono[OF product_bound power_bound
            cap_product_nonnegative power_nonnegative])
    show ?thesis using endpoint combined_bound by linarith
  qed
qed

end
