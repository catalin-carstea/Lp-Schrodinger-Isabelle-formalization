theory Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Mixed_Real_Power_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Mixed_L2"
begin

section \<open>Ordinary square-power bound for positive mixed convolution\<close>

theorem slp_positive_ennreal_convolution_mixed_real_power_bound:
  fixes a b q r :: real
    and F G :: "slp_point \<Rightarrow> ennreal"
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and b_lower: "1 < b"
    and b_upper: "b < 2"
    and q_lower: "1 < q"
    and r_lower: "1 < r"
    and split_conjugate: "1 / q + 1 / r = 1"
    and q_scale: "(2 - a) * q = a"
    and r_scale: "(2 - b) * r = b"
    and F_lp: "slp_positive_ennreal_lp_on_plane a F"
    and G_lp: "slp_positive_ennreal_lp_on_plane b G"
  shows
    "integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_positive_ennreal_convolution F G out) powr 2) \<le>
      (integral\<^sup>L lborel
          (\<lambda>x. enn2real (F x) powr a) *
        integral\<^sup>L lborel
          (\<lambda>x. enn2real (G x) powr b)) *
      (integral\<^sup>L lborel
          (\<lambda>x. enn2real (F x) powr a) / q +
        integral\<^sup>L lborel
          (\<lambda>x. enn2real (G x) powr b) / r)"
proof -
  let ?H = "slp_positive_ennreal_convolution F G"
  let ?B =
    "(integral\<^sup>L lborel (\<lambda>x. enn2real (F x) powr a) *
      integral\<^sup>L lborel (\<lambda>x. enn2real (G x) powr b)) *
    (integral\<^sup>L lborel (\<lambda>x. enn2real (F x) powr a) / q +
      integral\<^sup>L lborel (\<lambda>x. enn2real (G x) powr b) / r)"
  note mixed = slp_positive_ennreal_convolution_mixed_L2[OF
      a_lower a_upper b_lower b_upper q_lower r_lower split_conjugate
      q_scale r_scale F_lp G_lp]
  have H_finite: "AE out in lborel. ?H out < \<infinity>"
    using mixed(1) unfolding slp_positive_ennreal_lp_on_plane_def
    infinity_ennreal_def by blast
  have H_power_integrable:
      "integrable lborel (\<lambda>out. enn2real (?H out) powr 2)"
    using mixed(1) unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have real_square_nn:
      "(\<integral>\<^sup>+ out. enn2real (?H out) powr 2 \<partial>lborel) =
        (\<integral>\<^sup>+ out. ?H out ^ 2 \<partial>lborel)"
  proof (rule nn_integral_cong_AE)
    show "AE out in lborel.
        ennreal (enn2real (?H out) powr 2) = ?H out ^ 2"
      using H_finite
    proof eventually_elim
      fix out :: slp_point
      assume H_out_finite: "?H out < \<infinity>"
      have H_lift: "?H out = ennreal (enn2real (?H out))"
        using H_out_finite by simp
      have real_power:
          "enn2real (?H out) powr 2 = enn2real (?H out) ^ 2"
        by simp
      show "ennreal (enn2real (?H out) powr 2) = ?H out ^ 2"
        unfolding real_power
        apply (subst (2) H_lift)
        apply (rule ennreal_power [symmetric])
        apply simp
        done
    qed
  qed
  have real_square_integral:
      "(\<integral>\<^sup>+ out. enn2real (?H out) powr 2 \<partial>lborel) =
        ennreal
          (integral\<^sup>L lborel
            (\<lambda>out. enn2real (?H out) powr 2))"
    by (rule nn_integral_eq_integral[OF H_power_integrable]) simp
  have B_nonnegative: "0 \<le> ?B"
  proof -
    have F_power_nonnegative:
        "0 \<le> integral\<^sup>L lborel
          (\<lambda>x. enn2real (F x) powr a)"
      by (rule integral_nonneg_AE) simp
    have G_power_nonnegative:
        "0 \<le> integral\<^sup>L lborel
          (\<lambda>x. enn2real (G x) powr b)"
      by (rule integral_nonneg_AE) simp
    have q_nonnegative: "0 \<le> q" using q_lower by linarith
    have r_nonnegative: "0 \<le> r" using r_lower by linarith
    show ?thesis
      apply (rule mult_nonneg_nonneg)
       apply (rule mult_nonneg_nonneg[OF
            F_power_nonnegative G_power_nonnegative])
      apply (rule add_nonneg_nonneg)
       apply (rule divide_nonneg_nonneg[OF
            F_power_nonnegative q_nonnegative])
      apply (rule divide_nonneg_nonneg[OF
            G_power_nonnegative r_nonnegative])
      done
  qed
  have real_square_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (\<lambda>out. enn2real (?H out) powr 2)"
    by (rule integral_nonneg_AE) simp
  have ennreal_bound:
      "ennreal
          (integral\<^sup>L lborel
            (\<lambda>out. enn2real (?H out) powr 2)) \<le>
        ennreal ?B"
    using mixed(2) real_square_nn real_square_integral by simp
  show ?thesis
    using ennreal_bound real_square_nonnegative B_nonnegative by simp
qed

end
