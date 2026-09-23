theory Inverse_Schrodinger_Lp_Born_One_Sided_Zero_L2
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Zero_Riesz
begin

section \<open>The order-zero one-sided density in \(L^2\)\<close>

definition slp_positive_root_output_density_real ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_positive_root_output_density_real R cutoff potential terminal_weight n
      root_weight output =
    enn2real
      (slp_positive_root_output_density R cutoff potential terminal_weight n
        root_weight output)"

lemma aim_real_lp_on_plane_two_bounded_multiplier:
  fixes a g :: "slp_point \<Rightarrow> real"
  assumes a_measurable: "a \<in> borel_measurable lborel"
    and g_lp: "aim_real_lp_on_plane 2 g"
    and a_bound: "\<And>x. abs (a x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows "aim_real_lp_on_plane 2 (\<lambda>x. a x * g x)"
proof -
  have g_measurable: "g \<in> borel_measurable lborel"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. abs (g x) powr 2)"
    using g_lp unfolding aim_real_lp_on_plane_def by auto
  have target_measurable:
      "(\<lambda>x. a x * g x) \<in> borel_measurable lborel"
    using a_measurable g_measurable by measurable
  have target_power_measurable:
      "(\<lambda>x. abs (a x * g x) powr 2) \<in> borel_measurable lborel"
    using target_measurable by measurable
  have majorant_integrable:
      "integrable lborel (\<lambda>x. C^2 * (abs (g x) powr 2))"
    using g_power_integrable by simp
  have pointwise_bound:
      "AE x in lborel.
        norm (abs (a x * g x) powr 2) \<le>
          norm (C^2 * (abs (g x) powr 2))"
  proof (rule AE_I2)
    fix x :: slp_point
    have factor_bound: "abs (a x) * abs (g x) \<le> C * abs (g x)"
      by (rule mult_right_mono[OF a_bound]) simp
    have factor_nonnegative: "0 \<le> abs (a x) * abs (g x)"
      by simp
    have square_bound:
        "(abs (a x) * abs (g x))^2 \<le> (C * abs (g x))^2"
      by (rule power_mono[OF factor_bound factor_nonnegative])
    show "norm (abs (a x * g x) powr 2) \<le>
        norm (C^2 * (abs (g x) powr 2))"
      using square_bound C_nonnegative
      by (simp add: powr_numeral abs_mult power_mult_distrib)
  qed
  have target_power_integrable:
      "integrable lborel (\<lambda>x. abs (a x * g x) powr 2)"
    by (rule Bochner_Integration.integrable_bound[OF
          majorant_integrable target_power_measurable pointwise_bound])
  show ?thesis
    unfolding aim_real_lp_on_plane_def
    using target_measurable target_power_integrable by blast
qed

context aim_planar_riesz_hls
begin

theorem slp_positive_root_output_density_real_zero_l2:
  fixes R C p :: real
    and cutoff root_weight :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_support: "bounded {x. root_weight x \<noteq> 0}"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "aim_real_lp_on_plane 2
      (slp_positive_root_output_density_real R cutoff root_weight
        (\<lambda>_. 1) 0 root_weight)"
proof -
  let ?potential = "slp_localized_riesz_potential R root_weight"
  let ?factor = "\<lambda>z. inverse pi * norm (cutoff z)"
  let ?product = "\<lambda>z. ?factor z * ?potential z"
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have potential_l2: "aim_real_lp_on_plane 2 ?potential"
    using slp_localized_riesz_l2_compact_lp[OF radius_nonnegative p_lower
      p_upper root_weight_lp root_weight_support]
    by blast
  have factor_measurable: "?factor \<in> borel_measurable lborel"
    using cutoff_measurable by measurable
  have inverse_pi_positive: "0 < inverse pi"
    by simp
  have factor_bound: "abs (?factor x) \<le> inverse pi * C" for x
  proof -
    have "abs (?factor x) = inverse pi * norm (cutoff x)"
      using inverse_pi_positive by simp
    also have "... \<le> inverse pi * C"
      by (rule mult_left_mono[OF cutoff_bound])
        (use inverse_pi_positive in simp)
    finally show ?thesis .
  qed
  have scaled_C_nonnegative: "0 \<le> inverse pi * C"
    using inverse_pi_positive C_nonnegative by simp
  have product_l2: "aim_real_lp_on_plane 2 ?product"
    by (rule aim_real_lp_on_plane_two_bounded_multiplier[OF
          factor_measurable potential_l2 factor_bound
          scaled_C_nonnegative])
  have density_measurable:
      "slp_positive_root_output_density R cutoff root_weight (\<lambda>_. 1) 0
        root_weight \<in> borel_measurable lborel"
    by (rule slp_positive_root_output_density_measurable[OF
          cutoff_measurable root_weight_measurable _
          root_weight_measurable]) measurable
  have density_real_measurable:
      "slp_positive_root_output_density_real R cutoff root_weight
        (\<lambda>_. 1) 0 root_weight \<in> borel_measurable lborel"
    unfolding slp_positive_root_output_density_real_def
    using density_measurable by measurable
  have density_identity:
      "AE z in lborel.
        slp_positive_root_output_density R cutoff root_weight (\<lambda>_. 1) 0
            root_weight z =
          ennreal (?product z)"
    by (rule slp_positive_root_output_density_zero_riesz_AE[OF
          radius_nonnegative p_lower p_upper root_weight_lp
          root_weight_support])
  have product_nonnegative: "0 \<le> ?product z" for z
    using inverse_pi_positive
      slp_localized_riesz_potential_nonnegative[of R root_weight z]
    by simp
  have density_real_identity:
      "AE z in lborel.
        slp_positive_root_output_density_real R cutoff root_weight
            (\<lambda>_. 1) 0 root_weight z = ?product z"
  proof (rule eventually_mono[OF density_identity])
    fix z :: slp_point
    assume identity:
      "slp_positive_root_output_density R cutoff root_weight (\<lambda>_. 1) 0
          root_weight z = ennreal (?product z)"
    show "slp_positive_root_output_density_real R cutoff root_weight
          (\<lambda>_. 1) 0 root_weight z = ?product z"
      unfolding slp_positive_root_output_density_real_def
      using identity product_nonnegative[of z] by simp
  qed
  have product_power_integrable:
      "integrable lborel (\<lambda>z. abs (?product z) powr 2)"
    using product_l2 unfolding aim_real_lp_on_plane_def by blast
  have density_real_power_measurable:
      "(\<lambda>z. abs
          (slp_positive_root_output_density_real R cutoff root_weight
            (\<lambda>_. 1) 0 root_weight z) powr 2)
        \<in> borel_measurable lborel"
    using density_real_measurable by measurable
  have density_real_power_integrable:
      "integrable lborel
        (\<lambda>z. abs
          (slp_positive_root_output_density_real R cutoff root_weight
            (\<lambda>_. 1) 0 root_weight z) powr 2)"
    by (rule integrable_cong_AE_imp[OF product_power_integrable
          density_real_power_measurable])
      (use density_real_identity in eventually_elim; simp)
  show ?thesis
    unfolding aim_real_lp_on_plane_def
    using density_real_measurable density_real_power_integrable by blast
qed

end

end
