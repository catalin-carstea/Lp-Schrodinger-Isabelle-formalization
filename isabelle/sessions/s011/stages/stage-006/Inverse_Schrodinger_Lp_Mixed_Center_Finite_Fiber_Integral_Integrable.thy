theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Fiber_Integral_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Fiber_Integral_Positive_Bound"
begin

section \<open>Global integrability of the finite mixed center fiber integral\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_fiber_integral_integrable:
  fixes frequency B C p :: real
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_lp:
      "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp:
      "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_weight_integrable: "integrable lborel root_weight"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "integrable lborel
      (\<lambda>center :: slp_point.
        slp_mixed_center_finite_fiber_integral TYPE('i::finite)
          TYPE('j::finite) frequency root_weight cutoff left_potential cutoff
          right_potential center :: complex)"
proof -
  note measurable_and_bound =
    slp_mixed_center_finite_fiber_integral_measurable_and_positive_bound[OF
      B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      right_potential_lp cutoff_bound C_nonnegative root_weight_integrable
      root_support cutoff_support left_potential_support
      right_potential_support, where frequency = frequency]
  have positive_mass_finite:
      "nn_integral lborel (\<lambda>center.
          slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
            (2 * B) root_weight cutoff left_potential cutoff right_potential
            center) < top_class.top"
    by (rule slp_mixed_center_finite_positive_mass_finite[OF
          _ p_lower p_upper cutoff_measurable left_potential_lp
          right_potential_lp cutoff_bound C_nonnegative
          root_weight_integrable])
      (use B_nonnegative in simp)
  have norm_integral_le:
      "nn_integral lborel (\<lambda>center.
          ennreal (norm_class.norm
            (slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j)
              frequency root_weight cutoff left_potential cutoff
              right_potential center))) \<le>
        nn_integral lborel (\<lambda>center.
          slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
            (2 * B) root_weight cutoff left_potential cutoff right_potential
            center)"
    by (rule nn_integral_mono_AE[OF measurable_and_bound(2)])
  have norm_integral_finite:
      "nn_integral lborel (\<lambda>center.
          ennreal (norm_class.norm
            (slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j)
              frequency root_weight cutoff left_potential cutoff
              right_potential center))) < top_class.top"
    using order.strict_trans1[OF norm_integral_le positive_mass_finite] .
  show ?thesis
  proof (rule integrableI_bounded)
    show
      "(\<lambda>center :: slp_point.
        slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
          root_weight cutoff left_potential cutoff right_potential center ::
          complex) \<in> borel_measurable lborel"
      by (rule measurable_and_bound(1))
    show
      "nn_integral lborel (\<lambda>center :: slp_point.
          ennreal (norm
            (slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j)
              frequency root_weight cutoff left_potential cutoff
              right_potential center :: complex))) < \<infinity>"
      using norm_integral_finite by simp
  qed
qed

end

end
