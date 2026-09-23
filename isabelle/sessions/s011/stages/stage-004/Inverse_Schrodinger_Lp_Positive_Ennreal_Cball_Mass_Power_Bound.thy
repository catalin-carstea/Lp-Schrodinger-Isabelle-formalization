theory Inverse_Schrodinger_Lp_Positive_Ennreal_Cball_Mass_Power_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Bounded_Support_L1_Predicate"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Weighted_Holder_Power"
    "HOL-Analysis.Ball_Volume"
begin

section \<open>Quantitative mass bound for a positive density in a closed ball\<close>

lemma slp_positive_ennreal_lp_cball_mass_power_bound:
  fixes a b L radius :: real
    and center :: slp_point
    and F :: "slp_point \<Rightarrow> ennreal"
  assumes a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and radius_nonnegative: "0 \<le> radius"
    and L_nonnegative: "0 \<le> L"
    and F_lp: "slp_positive_ennreal_lp_on_plane a F"
    and F_outside: "\<And>x. x \<notin> cball center radius \<Longrightarrow> F x = 0"
    and F_power_bound:
      "integral\<^sup>L lborel (\<lambda>x. enn2real (F x) powr a) \<le> L"
  shows
    "enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel) powr a \<le>
      (unit_ball_vol (DIM(slp_point)) * radius ^ DIM(slp_point))
        powr (a / b) * L"
proof -
  let ?D = "\<lambda>x. enn2real (F x)"
  let ?W = "indicator (cball center radius) :: slp_point \<Rightarrow> real"
  have F_support_subset:
      "{x. F x \<noteq> 0} \<subseteq> cball center radius"
    using F_outside by blast
  have F_support: "bounded {x. F x \<noteq> 0}"
    by (rule bounded_subset[OF bounded_cball F_support_subset])
  have F_L1: "slp_positive_ennreal_lp_on_plane 1 F"
    by (rule slp_positive_ennreal_lp_bounded_support_to_L1[OF
          less_imp_le[OF a_lower] F_lp F_support])
  note D_lp = slp_positive_ennreal_Lp_real_representative[OF F_lp]
  note D_L1 = slp_positive_ennreal_L1_real_representative[OF F_L1]
  have W_measurable: "?W \<in> borel_measurable lborel"
    by (rule borel_measurable_indicator) simp
  have W_nonnegative: "0 \<le> ?W x" for x
    by simp
  have W_integrable: "integrable lborel ?W"
    using emeasure_lborel_cball_finite[of center radius]
    by (simp add: integrable_indicator_iff)
  have weighted_eq: "?W x * ?D x = ?D x" for x
    by (cases "x \<in> cball center radius")
      (simp_all add: indicator_def F_outside)
  have weighted_power_eq:
      "?W x * ?D x powr a = ?D x powr a" for x
    by (cases "x \<in> cball center radius")
      (simp_all add: indicator_def F_outside)
  have weighted_power_integrable:
      "integrable lborel (\<lambda>x. ?W x * ?D x powr a)"
    using D_lp(3) by (simp only: weighted_power_eq)
  have holder:
      "(integral\<^sup>L lborel (\<lambda>x. ?W x * ?D x)) powr a \<le>
        (integral\<^sup>L lborel ?W) powr (a / b) *
          integral\<^sup>L lborel (\<lambda>x. ?W x * ?D x powr a)"
    by (rule slp_weighted_holder_power(2)[OF
          a_lower b_lower conjugate W_measurable D_lp(1)
          W_nonnegative D_lp(2) W_integrable weighted_power_integrable])
  have D_integral_nonnegative: "0 \<le> integral\<^sup>L lborel ?D"
    by (rule integral_nonneg_AE) simp
  have mass_real:
      "enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel) =
        integral\<^sup>L lborel ?D"
    using D_L1(5) D_integral_nonnegative by simp
  have volume:
      "integral\<^sup>L lborel ?W =
        unit_ball_vol (DIM(slp_point)) * radius ^ DIM(slp_point)"
    using radius_nonnegative
    by (simp add: integral_indicator content_cball)
  have holder_rewritten:
      "(integral\<^sup>L lborel ?D) powr a \<le>
        (unit_ball_vol (DIM(slp_point)) * radius ^ DIM(slp_point))
          powr (a / b) *
            integral\<^sup>L lborel (\<lambda>x. ?D x powr a)"
    using holder volume
    by (simp only: weighted_eq weighted_power_eq)
  have scale_nonnegative:
      "0 \<le> (unit_ball_vol (DIM(slp_point)) *
        radius ^ DIM(slp_point)) powr (a / b)"
    by simp
  have final_bound:
      "(integral\<^sup>L lborel ?D) powr a \<le>
        (unit_ball_vol (DIM(slp_point)) * radius ^ DIM(slp_point))
          powr (a / b) * L"
    using holder_rewritten
      mult_left_mono[OF F_power_bound scale_nonnegative]
    by linarith
  show ?thesis using final_bound mass_real by simp
qed

end
