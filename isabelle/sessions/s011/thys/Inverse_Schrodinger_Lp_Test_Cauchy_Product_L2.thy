theory Inverse_Schrodinger_Lp_Test_Cauchy_Product_L2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Riesz_L2"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Smooth_Error_Limits"
begin

section \<open>Compact test multipliers of Cauchy fields in complex \(L^2\)\<close>

lemma aim_complex_lp_on_plane_two_bounded_multiplier:
  fixes a g :: "slp_point \<Rightarrow> complex"
  assumes a_measurable: "a \<in> borel_measurable lborel"
    and g_lp: "aim_complex_lp_on_plane 2 g"
    and a_bound: "\<And>x. cmod (a x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows "aim_complex_lp_on_plane 2 (\<lambda>x. a x * g x)"
proof -
  have g_measurable: "g \<in> borel_measurable lborel"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. cmod (g x) powr 2)"
    using g_lp unfolding aim_complex_lp_on_plane_def by auto
  have target_measurable:
      "(\<lambda>x. a x * g x) \<in> borel_measurable lborel"
    using a_measurable g_measurable by measurable
  have target_power_measurable:
      "(\<lambda>x. cmod (a x * g x) powr 2) \<in> borel_measurable lborel"
    using target_measurable by measurable
  have majorant_integrable:
      "integrable lborel (\<lambda>x. C^2 * (cmod (g x) powr 2))"
    using g_power_integrable by simp
  have pointwise_bound:
      "AE x in lborel.
        Real_Vector_Spaces.norm (cmod (a x * g x) powr 2) \<le>
          Real_Vector_Spaces.norm (C^2 * (cmod (g x) powr 2))"
  proof (rule AE_I2)
    fix x :: slp_point
    have factor_bound: "cmod (a x) * cmod (g x) \<le> C * cmod (g x)"
      by (rule mult_right_mono[OF a_bound]) simp
    have factor_nonnegative: "0 \<le> cmod (a x) * cmod (g x)"
      by simp
    have square_bound:
        "(cmod (a x) * cmod (g x))^2 \<le> (C * cmod (g x))^2"
      by (rule power_mono[OF factor_bound factor_nonnegative])
    show "Real_Vector_Spaces.norm (cmod (a x * g x) powr 2) \<le>
        Real_Vector_Spaces.norm (C^2 * (cmod (g x) powr 2))"
      using square_bound C_nonnegative
      by (simp add: powr_numeral norm_mult power_mult_distrib)
  qed
  have target_power_integrable:
      "integrable lborel (\<lambda>x. cmod (a x * g x) powr 2)"
    by (rule Bochner_Integration.integrable_bound[OF
          majorant_integrable target_power_measurable pointwise_bound])
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using target_measurable target_power_integrable by blast
qed

context aim_planar_hls_cauchy
begin

theorem slp_test_cauchy_product_l2:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "aim_complex_lp_on_plane 2
      (\<lambda>x. phi x * slp_cauchy_transform orientation potential x)"
proof -
  let ?X = "closure {x. phi x \<noteq> 0}"
  have X_compact: "compact ?X"
    using phi_test unfolding slp_test_function_on_def by blast
  have X_measurable: "?X \<in> sets lborel"
    using borel_compact[OF X_compact] by simp
  have X_bounded: "bounded ?X"
    by (rule compact_imp_bounded[OF X_compact])
  have target_above_two: "2 < aim_hls_target_exponent p"
    by (rule slp_hls_target_exponent_above_two[OF p_lower p_upper])
  have cauchy_target:
      "slp_complex_lp_on (aim_hls_target_exponent p) ?X
        (slp_cauchy_transform orientation potential)"
  proof (cases orientation)
    case SLP_Partial_Inverse
    then show ?thesis
      using slp_both_cauchy_hls_sum_on_measurable p_lower p_upper
        potential_lp X_measurable by blast
  next
    case SLP_Dbar_Inverse
    then show ?thesis
      using slp_both_cauchy_hls_sum_on_measurable p_lower p_upper
        potential_lp X_measurable by blast
  qed
  have cauchy_local_l2:
      "slp_complex_lp_on 2 ?X
        (slp_cauchy_transform orientation potential)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          zero_less_numeral less_imp_le[OF target_above_two]
          X_measurable X_bounded cauchy_target])
  have restricted_l2:
      "aim_complex_lp_on_plane 2
        (slp_restrict_field ?X
          (slp_cauchy_transform orientation potential))"
    using cauchy_local_l2 unfolding slp_complex_lp_on_def .
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have phi_bounded: "bounded (range phi)"
    by (rule slp_test_function_integrable_bounded(2)[OF phi_test])
  obtain C where phi_bound: "\<And>x. cmod (phi x) \<le> C"
    using phi_bounded unfolding bounded_iff by auto
  have C_nonnegative: "0 \<le> C"
  proof -
    have "0 \<le> cmod (phi 0)" by simp
    then show ?thesis using phi_bound[of 0] by linarith
  qed
  have restricted_product_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>x. phi x * slp_restrict_field ?X
          (slp_cauchy_transform orientation potential) x)"
    by (rule aim_complex_lp_on_plane_two_bounded_multiplier[OF
          phi_measurable restricted_l2 phi_bound C_nonnegative])
  have product_eq:
      "(\<lambda>x. phi x * slp_restrict_field ?X
          (slp_cauchy_transform orientation potential) x) =
        (\<lambda>x. phi x * slp_cauchy_transform orientation potential x)"
    by (rule ext) (auto simp: slp_restrict_field_def)
  show ?thesis
    using restricted_product_l2 by (simp only: product_eq)
qed

end

end
