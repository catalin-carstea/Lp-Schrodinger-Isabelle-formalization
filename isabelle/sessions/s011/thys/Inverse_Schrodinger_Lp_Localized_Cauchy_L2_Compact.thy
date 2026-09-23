theory Inverse_Schrodinger_Lp_Localized_Cauchy_L2_Compact
  imports
    Inverse_Schrodinger_Lp_Double_Localized_Cauchy_Endpoint
    Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Above_Two
begin

section \<open>The compact-support mapping from localized \(L^2\) data\<close>

definition slp_localized_complex_integrand ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> complex"
where
  "slp_localized_complex_integrand R f z y =
    of_real (slp_localized_cauchy_kernel R (z - y)) * f y"

definition slp_localized_complex_convolution ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_localized_complex_convolution R f z =
    integral\<^sup>L lborel (slp_localized_complex_integrand R f z)"

lemma slp_localized_complex_integrand_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_localized_complex_integrand R f z
    \<in> borel_measurable lborel"
  unfolding slp_localized_complex_integrand_def
  using slp_localized_cauchy_kernel_borel_measurable f_measurable
  by measurable

lemma slp_localized_complex_convolution_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_localized_complex_convolution R f
    \<in> borel_measurable lborel"
  unfolding slp_localized_complex_convolution_def
    slp_localized_complex_integrand_def
  using slp_localized_cauchy_kernel_borel_measurable f_measurable
  by measurable

lemma slp_localized_complex_integrand_norm:
  "norm (slp_localized_complex_integrand R f z y) =
    slp_localized_riesz_integrand R f z y"
  unfolding slp_localized_complex_integrand_def
    slp_localized_riesz_integrand_def
  using slp_localized_cauchy_kernel_nonnegative[of R "z - y"]
  by (simp add: norm_mult)

lemma slp_localized_integrable_iff_complex_integrable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "integrable lborel (slp_localized_riesz_integrand R f z) \<longleftrightarrow>
    integrable lborel (slp_localized_complex_integrand R f z)"
proof -
  have complex_measurable:
    "slp_localized_complex_integrand R f z
      \<in> borel_measurable lborel"
    by (rule slp_localized_complex_integrand_measurable[OF f_measurable])
  have norm_integrand:
    "(\<lambda>y. norm (slp_localized_complex_integrand R f z y)) =
      slp_localized_riesz_integrand R f z"
    by (rule ext) (rule slp_localized_complex_integrand_norm)
  show ?thesis
    using Bochner_Integration.integrable_norm_iff[OF complex_measurable]
    by (simp only: norm_integrand)
qed

lemma slp_localized_riesz_potential_nonnegative:
  "0 \<le> slp_localized_riesz_potential R f z"
  unfolding slp_localized_riesz_potential_def
  by (rule Bochner_Integration.integral_nonneg)
    (simp add: slp_localized_riesz_integrand_nonnegative)

lemma slp_localized_complex_convolution_norm_le:
  "norm (slp_localized_complex_convolution R f z) \<le>
    slp_localized_riesz_potential R f z"
proof -
  have norm_integrand:
    "(\<lambda>y. norm (slp_localized_complex_integrand R f z y)) =
      slp_localized_riesz_integrand R f z"
    by (rule ext) (rule slp_localized_complex_integrand_norm)
  show ?thesis
    unfolding slp_localized_complex_convolution_def
      slp_localized_riesz_potential_def
    using integral_norm_bound[of lborel
        "slp_localized_complex_integrand R f z"]
    by (simp only: norm_integrand)
qed

lemma slp_real_nonzero_set_measurable:
  assumes g_measurable: "g \<in> borel_measurable lborel"
  shows "{x. g x \<noteq> (0::real)} \<in> sets lborel"
proof -
  have zero_preimage:
    "g -` {0} \<inter> space lborel \<in> sets lborel"
    using g_measurable by measurable
  have "{x. g x \<noteq> 0} = space lborel - (g -` {0} \<inter> space lborel)"
    by auto
  then show ?thesis
    using zero_preimage by simp
qed

lemma aim_real_lp_on_plane_mono_exponent_bounded_support:
  assumes p_positive: "0 < p"
    and exponent_order: "p \<le> q"
    and g_support: "bounded {x. g x \<noteq> 0}"
    and g_lp: "aim_real_lp_on_plane q g"
  shows "aim_real_lp_on_plane p g"
proof -
  have q_positive: "0 < q"
    using p_positive exponent_order by linarith
  have g_measurable: "g \<in> borel_measurable lborel"
    and g_q_integrable:
      "integrable lborel (\<lambda>x. abs (g x) powr q)"
    using g_lp unfolding aim_real_lp_on_plane_def by auto
  have nonzero_measurable: "{x. g x \<noteq> 0} \<in> sets lborel"
    by (rule slp_real_nonzero_set_measurable[OF g_measurable])
  have indicator_integrable:
    "integrable lborel
      (indicator {x. g x \<noteq> 0} :: slp_point \<Rightarrow> real)"
    using nonzero_measurable emeasure_bounded_finite[OF g_support]
    by (simp add: integrable_indicator_iff)
  have majorant_integrable:
    "integrable lborel
      (\<lambda>x. indicator {x. g x \<noteq> 0} x + abs (g x) powr q)"
    by (rule Bochner_Integration.integrable_add[OF
          indicator_integrable g_q_integrable])
  have target_measurable:
    "(\<lambda>x. abs (g x) powr p) \<in> borel_measurable lborel"
    using g_measurable by measurable
  have pointwise_bound:
    "AE x in lborel.
      norm (abs (g x) powr p) \<le>
        norm (indicator {x. g x \<noteq> 0} x + abs (g x) powr q)"
  proof (rule AE_I2)
    fix x :: slp_point
    have raw_bound:
      "abs (g x) powr p \<le>
        indicator {x. g x \<noteq> 0} x + abs (g x) powr q"
    proof (cases "g x = 0")
      case True
      then show ?thesis
        using p_positive q_positive by simp
    next
      case False
      have "abs (g x) powr p \<le> 1 + abs (g x) powr q"
        by (rule slp_powr_le_one_add_powr)
          (use p_positive exponent_order in auto)
      then show ?thesis
        using False by simp
    qed
    have left_nonnegative: "0 \<le> abs (g x) powr p"
      by simp
    have right_nonnegative:
      "0 \<le> indicator {x. g x \<noteq> 0} x + abs (g x) powr q"
      by (cases "g x = 0") simp_all
    show "norm (abs (g x) powr p) \<le>
        norm (indicator {x. g x \<noteq> 0} x + abs (g x) powr q)"
      using raw_bound left_nonnegative right_nonnegative by simp
  qed
  have target_integrable:
    "integrable lborel (\<lambda>x. abs (g x) powr p)"
    by (rule Bochner_Integration.integrable_bound[OF
          majorant_integrable target_measurable pointwise_bound])
  show ?thesis
    unfolding aim_real_lp_on_plane_def
    using g_measurable target_integrable by blast
qed

lemma slp_localized_riesz_potential_bounded_support:
  assumes radius_nonnegative: "0 \<le> R"
    and f_support: "bounded {x. f x \<noteq> 0}"
  shows "bounded {z. slp_localized_riesz_potential R f z \<noteq> 0}"
proof -
  obtain B where support_bound:
    "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> B"
    using f_support unfolding bounded_iff by auto
  let ?B = "max 0 B"
  have B_nonnegative: "0 \<le> ?B"
    by simp
  have support_bound_max:
    "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> ?B"
    using support_bound by fastforce
  show ?thesis
    unfolding bounded_iff
  proof (intro exI ballI)
    fix z :: slp_point
    assume z_nonzero: "z \<in>
      {z. slp_localized_riesz_potential R f z \<noteq> 0}"
    show "norm z \<le> R + ?B"
    proof (rule ccontr)
      assume outside: "\<not> norm z \<le> R + ?B"
      have outside_strict: "R + ?B < norm z"
        using outside by simp
      have integrand_zero:
        "slp_localized_riesz_integrand R f z = (\<lambda>_. 0)"
      proof (rule ext)
        fix y :: slp_point
        show "slp_localized_riesz_integrand R f z y = 0"
        proof (cases "f y = 0")
          case True
          then show ?thesis
            by (simp add: slp_localized_riesz_integrand_def)
        next
          case False
          have y_bound: "norm y \<le> ?B"
            by (rule support_bound_max[OF False])
          have difference_outside: "R < norm (z - y)"
          proof (rule ccontr)
            assume "\<not> R < norm (z - y)"
            then have difference_inside: "norm (z - y) \<le> R"
              by simp
            have "norm z \<le> norm (z - y) + norm y"
              using norm_triangle_ineq[of "z - y" y] by simp
            also have "... \<le> R + ?B"
              using difference_inside y_bound by linarith
            finally show False
              using outside_strict by linarith
          qed
          then show ?thesis
            unfolding slp_localized_riesz_integrand_def
            by (simp add: slp_localized_cauchy_kernel_outside)
        qed
      qed
      have potential_zero: "slp_localized_riesz_potential R f z = 0"
        unfolding slp_localized_riesz_potential_def
        by (simp only: integrand_zero integral_zero)
      show False
        using z_nonzero potential_zero by simp
    qed
  qed
qed

context aim_planar_riesz_hls
begin

theorem slp_localized_riesz_l2_compact_all_finite:
  assumes radius_nonnegative: "0 \<le> R"
    and exponent_lower: "1 \<le> (s::real)"
    and f_lp: "aim_complex_lp_on_plane 2 f"
    and f_support: "bounded {x. f x \<noteq> 0}"
  shows "(AE z in lborel.
      integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
    aim_real_lp_on_plane s (slp_localized_riesz_potential R f) \<and>
    bounded {z. slp_localized_riesz_potential R f z \<noteq> 0}"
proof -
  have exponent_positive: "0 < s"
    using exponent_lower by linarith
  have potential_support:
    "bounded {z. slp_localized_riesz_potential R f z \<noteq> 0}"
    by (rule slp_localized_riesz_potential_bounded_support[OF
          radius_nonnegative f_support])
  obtain C::real where C_positive: "0 < C"
    and localized:
      "\<forall>R p f. 0 \<le> R \<and> 1 < p \<and> p < 2 \<and>
          aim_complex_lp_on_plane p f
        \<longrightarrow>
        (AE z in lborel.
          integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (slp_localized_riesz_potential R f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_localized_riesz_hls by blast
  show ?thesis
  proof (cases "s \<le> 2")
    case True
    have input_three_halves:
      "aim_complex_lp_on_plane (3 / 2) f"
      by (rule aim_complex_lp_on_plane_mono_exponent_bounded_support)
        (use f_support f_lp in simp_all)
    have hls_result:
      "(AE z in lborel.
          integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent (3 / 2))
          (slp_localized_riesz_potential R f)"
      using localized radius_nonnegative input_three_halves by force
    have potential_six:
      "aim_real_lp_on_plane 6 (slp_localized_riesz_potential R f)"
      using hls_result slp_hls_target_exponent_three_halves by simp
    have potential_s:
      "aim_real_lp_on_plane s (slp_localized_riesz_potential R f)"
      by (rule aim_real_lp_on_plane_mono_exponent_bounded_support[OF
            exponent_positive _ potential_support potential_six])
        (use True in linarith)
    show ?thesis
      using hls_result potential_s potential_support by blast
  next
    case False
    have s_above_two: "2 < s"
      using False by simp
    have source_lower: "1 < slp_hls_source_exponent s"
      and source_upper: "slp_hls_source_exponent s < 2"
      using slp_hls_source_exponent_bounds[OF s_above_two] by auto
    have source_positive: "0 < slp_hls_source_exponent s"
      using source_lower by linarith
    have input_source:
      "aim_complex_lp_on_plane (slp_hls_source_exponent s) f"
      by (rule aim_complex_lp_on_plane_mono_exponent_bounded_support[OF
            source_positive less_imp_le[OF source_upper] f_support f_lp])
    have hls_result:
      "(AE z in lborel.
          integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
        aim_real_lp_on_plane
          (aim_hls_target_exponent (slp_hls_source_exponent s))
          (slp_localized_riesz_potential R f)"
      using localized radius_nonnegative source_lower source_upper input_source
      by blast
    have potential_s:
      "aim_real_lp_on_plane s (slp_localized_riesz_potential R f)"
      using hls_result slp_hls_source_target_identity[OF s_above_two]
      by simp
    show ?thesis
      using hls_result potential_s potential_support by blast
  qed
qed

theorem slp_localized_complex_l2_compact_all_finite:
  assumes radius_nonnegative: "0 \<le> R"
    and exponent_lower: "1 \<le> (s::real)"
    and f_lp: "aim_complex_lp_on_plane 2 f"
    and f_support: "bounded {x. f x \<noteq> 0}"
  shows "(AE z in lborel.
      integrable lborel (slp_localized_complex_integrand R f z)) \<and>
    aim_complex_lp_on_plane s (slp_localized_complex_convolution R f) \<and>
    bounded {z. slp_localized_complex_convolution R f z \<noteq> 0}"
proof -
  have exponent_positive: "0 < s"
    using exponent_lower by linarith
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast
  have positive_result:
    "(AE z in lborel.
        integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
      aim_real_lp_on_plane s (slp_localized_riesz_potential R f) \<and>
      bounded {z. slp_localized_riesz_potential R f z \<noteq> 0}"
    by (rule slp_localized_riesz_l2_compact_all_finite[OF assms])
  have complex_integrable:
    "AE z in lborel.
      integrable lborel (slp_localized_complex_integrand R f z)"
    using conjunct1[OF positive_result]
  proof eventually_elim
    fix z :: slp_point
    assume real_integrable:
      "integrable lborel (slp_localized_riesz_integrand R f z)"
    show "integrable lborel (slp_localized_complex_integrand R f z)"
      using slp_localized_integrable_iff_complex_integrable[OF f_measurable,
          of R z]
        real_integrable by blast
  qed
  have potential_lp:
    "aim_real_lp_on_plane s (slp_localized_riesz_potential R f)"
    using positive_result by blast
  have convolution_measurable:
    "slp_localized_complex_convolution R f
      \<in> borel_measurable lborel"
    by (rule slp_localized_complex_convolution_measurable[OF f_measurable])
  have convolution_power_measurable:
    "(\<lambda>z. norm (slp_localized_complex_convolution R f z) powr s)
      \<in> borel_measurable lborel"
    using convolution_measurable by measurable
  have convolution_power_integrable:
    "integrable lborel
      (\<lambda>z. norm (slp_localized_complex_convolution R f z) powr s)"
  proof (rule Bochner_Integration.integrable_bound)
    show "integrable lborel
        (\<lambda>z. abs (slp_localized_riesz_potential R f z) powr s)"
      using potential_lp unfolding aim_real_lp_on_plane_def by blast
    show "(\<lambda>z. norm (slp_localized_complex_convolution R f z) powr s)
        \<in> borel_measurable lborel"
      by (rule convolution_power_measurable)
    show "AE z in lborel.
        norm (norm (slp_localized_complex_convolution R f z) powr s) \<le>
        norm (abs (slp_localized_riesz_potential R f z) powr s)"
    proof (rule AE_I2)
      fix z :: slp_point
      have potential_nonnegative:
        "0 \<le> slp_localized_riesz_potential R f z"
        by (rule slp_localized_riesz_potential_nonnegative)
      have convolution_le:
        "norm (slp_localized_complex_convolution R f z) \<le>
          slp_localized_riesz_potential R f z"
        by (rule slp_localized_complex_convolution_norm_le)
      have power_le:
        "norm (slp_localized_complex_convolution R f z) powr s \<le>
          slp_localized_riesz_potential R f z powr s"
        by (rule powr_mono2[OF less_imp_le[OF exponent_positive]
              norm_ge_zero convolution_le])
      show "norm (norm (slp_localized_complex_convolution R f z) powr s) \<le>
          norm (abs (slp_localized_riesz_potential R f z) powr s)"
        using power_le potential_nonnegative by simp
    qed
  qed
  have convolution_lp:
    "aim_complex_lp_on_plane s (slp_localized_complex_convolution R f)"
    unfolding aim_complex_lp_on_plane_def
    using convolution_measurable convolution_power_integrable by blast
  have support_subset:
    "{z. slp_localized_complex_convolution R f z \<noteq> 0} \<subseteq>
      {z. slp_localized_riesz_potential R f z \<noteq> 0}"
  proof
    fix z :: slp_point
    assume convolution_nonzero:
      "z \<in> {z. slp_localized_complex_convolution R f z \<noteq> 0}"
    have convolution_le:
      "norm (slp_localized_complex_convolution R f z) \<le>
        slp_localized_riesz_potential R f z"
      by (rule slp_localized_complex_convolution_norm_le)
    show "z \<in> {z. slp_localized_riesz_potential R f z \<noteq> 0}"
      using convolution_nonzero convolution_le by auto
  qed
  have convolution_support:
    "bounded {z. slp_localized_complex_convolution R f z \<noteq> 0}"
    by (rule bounded_subset[OF conjunct2[OF conjunct2[OF positive_result]]
          support_subset])
  show ?thesis
    using complex_integrable convolution_lp convolution_support by blast
qed

end

end
