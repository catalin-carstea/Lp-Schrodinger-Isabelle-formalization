theory Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Mixed_Uniform_Power
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Mixed_Real_Power_Bound"
begin

section \<open>Root-uniform positive mixed-convolution power control\<close>

theorem slp_positive_ennreal_convolution_mixed_uniform_power:
  fixes a b q r A B :: real
    and F G :: "slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and b_lower: "1 < b"
    and b_upper: "b < 2"
    and q_lower: "1 < q"
    and r_lower: "1 < r"
    and split_conjugate: "1 / q + 1 / r = 1"
    and q_scale: "(2 - a) * q = a"
    and r_scale: "(2 - b) * r = b"
    and A_nonnegative: "0 \<le> A"
    and B_nonnegative: "0 \<le> B"
    and F_lp: "\<And>root. slp_positive_ennreal_lp_on_plane a (F root)"
    and G_lp: "\<And>root. slp_positive_ennreal_lp_on_plane b (G root)"
    and F_power_bound:
      "\<And>root. integral\<^sup>L lborel
        (\<lambda>x. enn2real (F root x) powr a) \<le> A"
    and G_power_bound:
      "\<And>root. integral\<^sup>L lborel
        (\<lambda>x. enn2real (G root x) powr b) \<le> B"
  shows cap_nonnegative:
      "0 \<le> (A * B) * (A / q + B / r)"
    and all_convolutions_L2:
      "\<And>root. slp_positive_ennreal_lp_on_plane 2
        (slp_positive_ennreal_convolution (F root) (G root))"
    and uniform_square_power:
      "\<And>root. integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_positive_ennreal_convolution (F root) (G root) out) powr 2)
        \<le> (A * B) * (A / q + B / r)"
proof -
  have q_nonnegative: "0 \<le> q" using q_lower by linarith
  have r_nonnegative: "0 \<le> r" using r_lower by linarith
  show "0 \<le> (A * B) * (A / q + B / r)"
    apply (rule mult_nonneg_nonneg)
     apply (rule mult_nonneg_nonneg[OF A_nonnegative B_nonnegative])
    apply (rule add_nonneg_nonneg)
     apply (rule divide_nonneg_nonneg[OF A_nonnegative q_nonnegative])
    apply (rule divide_nonneg_nonneg[OF B_nonnegative r_nonnegative])
    done
  show "slp_positive_ennreal_lp_on_plane 2
      (slp_positive_ennreal_convolution (F root) (G root))"
    for root
    by (rule slp_positive_ennreal_convolution_mixed_L2(1)[OF
          a_lower a_upper b_lower b_upper q_lower r_lower split_conjugate
          q_scale r_scale F_lp G_lp])
  show "integral\<^sup>L lborel
      (\<lambda>out. enn2real
        (slp_positive_ennreal_convolution (F root) (G root) out) powr 2)
      \<le> (A * B) * (A / q + B / r)"
    for root
  proof -
    let ?FA =
      "integral\<^sup>L lborel (\<lambda>x. enn2real (F root x) powr a)"
    let ?GB =
      "integral\<^sup>L lborel (\<lambda>x. enn2real (G root x) powr b)"
    have endpoint:
        "integral\<^sup>L lborel
            (\<lambda>out. enn2real
              (slp_positive_ennreal_convolution (F root) (G root) out)
              powr 2)
          \<le> (?FA * ?GB) * (?FA / q + ?GB / r)"
      by (rule slp_positive_ennreal_convolution_mixed_real_power_bound[OF
            a_lower a_upper b_lower b_upper q_lower r_lower split_conjugate
            q_scale r_scale F_lp G_lp])
    have FA_nonnegative: "0 \<le> ?FA"
      by (rule integral_nonneg_AE) simp
    have GB_nonnegative: "0 \<le> ?GB"
      by (rule integral_nonneg_AE) simp
    have product_bound: "?FA * ?GB \<le> A * B"
      by (rule mult_mono[OF F_power_bound G_power_bound])
        (use FA_nonnegative A_nonnegative in simp_all)
    have F_quotient_bound: "?FA / q \<le> A / q"
      by (rule divide_right_mono[OF F_power_bound q_nonnegative])
    have G_quotient_bound: "?GB / r \<le> B / r"
      by (rule divide_right_mono[OF G_power_bound r_nonnegative])
    have sum_bound: "?FA / q + ?GB / r \<le> A / q + B / r"
      by (rule add_mono[OF F_quotient_bound G_quotient_bound])
    have cap_product_nonnegative: "0 \<le> A * B"
      by (rule mult_nonneg_nonneg[OF A_nonnegative B_nonnegative])
    have source_sum_nonnegative: "0 \<le> ?FA / q + ?GB / r"
      apply (rule add_nonneg_nonneg)
       apply (rule divide_nonneg_nonneg[OF FA_nonnegative q_nonnegative])
      apply (rule divide_nonneg_nonneg[OF GB_nonnegative r_nonnegative])
      done
    have cap_bound:
        "(?FA * ?GB) * (?FA / q + ?GB / r) \<le>
          (A * B) * (A / q + B / r)"
      by (rule mult_mono[OF product_bound sum_bound
            cap_product_nonnegative source_sum_nonnegative])
    show ?thesis using endpoint cap_bound by linarith
  qed
qed

end
