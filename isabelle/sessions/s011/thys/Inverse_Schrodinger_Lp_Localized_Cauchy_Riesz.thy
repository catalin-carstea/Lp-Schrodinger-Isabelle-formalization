theory Inverse_Schrodinger_Lp_Localized_Cauchy_Riesz
  imports
    Inverse_Schrodinger_Lp_Localized_Cauchy_Kernel_Lp
    "Paper_ISLP_AIM_Planar_Riesz_Potential_HLS.AIM_Planar_Riesz_Potential_HLS_Interface"
begin

section \<open>Localized positive Cauchy kernel from the planar Riesz bound\<close>

definition slp_localized_riesz_integrand ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> real"
where
  "slp_localized_riesz_integrand R f z y =
    slp_localized_cauchy_kernel R (z - y) * norm (f y)"

definition slp_localized_riesz_potential ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_localized_riesz_potential R f z =
    integral\<^sup>L lborel (slp_localized_riesz_integrand R f z)"

lemma slp_point_as_complex_norm [simp]:
  "norm (slp_point_as_complex x) = norm x"
proof -
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  show ?thesis
    by (simp add: slp_point_as_complex_def norm_complex_def norm_vec_def
        L2_set_def universe_two add.commute)
qed

lemma slp_point_as_complex_diff [simp]:
  "slp_point_as_complex (x - y) =
    slp_point_as_complex x - slp_point_as_complex y"
  by (rule complex_eqI)
    (simp_all add: slp_point_as_complex_def)

lemma aim_point_as_complex_eq_slp [simp]:
  "aim_point_as_complex x = slp_point_as_complex x"
  by (simp add: aim_point_as_complex_def slp_point_as_complex_def)

lemma slp_localized_cauchy_kernel_le_riesz:
  assumes radius_nonnegative: "0 \<le> R"
  shows "slp_localized_cauchy_kernel R (z - y) \<le>
    inverse (norm (aim_point_as_complex z - aim_point_as_complex y))"
proof -
  have complex_difference:
    "aim_point_as_complex z - aim_point_as_complex y =
      slp_point_as_complex (z - y)"
    by simp
  have denominator_norm:
    "norm (aim_point_as_complex z - aim_point_as_complex y) =
      norm (z - y)"
    by (simp only: complex_difference slp_point_as_complex_norm)
  show ?thesis
  proof (cases "norm (z - y) \<le> R")
  case True
  then show ?thesis
    by (simp only: slp_localized_cauchy_kernel_def True if_True
        denominator_norm order_refl)
  next
    case False
    then show ?thesis
      by (simp add: slp_localized_cauchy_kernel_def)
  qed
qed

lemma slp_localized_riesz_integrand_le:
  assumes radius_nonnegative: "0 \<le> R"
  shows "slp_localized_riesz_integrand R f z y \<le>
    aim_planar_riesz_integrand f z y"
  unfolding slp_localized_riesz_integrand_def
    aim_planar_riesz_integrand_def
proof -
  have kernel_le:
    "slp_localized_cauchy_kernel R (z - y) \<le>
      inverse (norm (aim_point_as_complex z - aim_point_as_complex y))"
    by (rule slp_localized_cauchy_kernel_le_riesz[OF radius_nonnegative])
  show "slp_localized_cauchy_kernel R (z - y) * norm (f y) \<le>
      norm (f y) *
        inverse (norm (aim_point_as_complex z - aim_point_as_complex y))"
    using mult_right_mono[OF kernel_le norm_ge_zero]
    by (simp only: mult.commute)
qed

lemma slp_localized_riesz_integrand_nonnegative:
  "0 \<le> slp_localized_riesz_integrand R f z y"
  unfolding slp_localized_riesz_integrand_def
  by (rule mult_nonneg_nonneg[OF
        slp_localized_cauchy_kernel_nonnegative norm_ge_zero])

lemma slp_localized_riesz_integrand_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_localized_riesz_integrand R f z \<in> borel_measurable lborel"
  unfolding slp_localized_riesz_integrand_def
  using slp_localized_cauchy_kernel_borel_measurable f_measurable
  by measurable

lemma slp_localized_riesz_potential_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_localized_riesz_potential R f \<in> borel_measurable lborel"
  unfolding slp_localized_riesz_potential_def
    slp_localized_riesz_integrand_def
  using slp_localized_cauchy_kernel_borel_measurable f_measurable
  by measurable

context aim_planar_riesz_hls
begin

theorem slp_localized_riesz_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>R p f. 0 \<le> R \<and> 1 < p \<and> p < 2 \<and>
        aim_complex_lp_on_plane p f
      \<longrightarrow>
      (AE z in lborel.
        integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent p)
        (slp_localized_riesz_potential R f) \<and>
      aim_real_lp_norm (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f)"
proof -
  obtain C::real where C_positive: "0 < C"
    and C_bound:
      "\<And>p f. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p f \<Longrightarrow>
        (AE z in lborel. integrable lborel (aim_planar_riesz_integrand f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (aim_planar_riesz_potential f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (aim_planar_riesz_potential f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using aim_planar_riesz_hls
    unfolding aim_planar_riesz_hls_claim_def by blast
  have all_localized:
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
  proof (intro allI impI)
    fix R p :: real and f :: slp_scalar_field
    assume hypotheses:
      "0 \<le> R \<and> 1 < p \<and> p < 2 \<and>
        aim_complex_lp_on_plane p f"
    have radius_nonnegative: "0 \<le> R"
      using hypotheses by blast
    have p_lower: "1 < p" and p_upper: "p < 2"
      using hypotheses by blast+
    have f_lp: "aim_complex_lp_on_plane p f"
      using hypotheses by blast
    have f_measurable: "f \<in> borel_measurable lborel"
      using f_lp unfolding aim_complex_lp_on_plane_def by blast
    have full_result:
      "(AE z in lborel. integrable lborel (aim_planar_riesz_integrand f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (aim_planar_riesz_potential f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (aim_planar_riesz_potential f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      by (rule C_bound[OF p_lower p_upper f_lp])
    have localized_integrable:
      "AE z in lborel.
        integrable lborel (slp_localized_riesz_integrand R f z)"
      using conjunct1[OF full_result]
    proof eventually_elim
      fix z :: slp_point
      assume full_integrable:
        "integrable lborel (aim_planar_riesz_integrand f z)"
      show "integrable lborel (slp_localized_riesz_integrand R f z)"
      proof (rule Bochner_Integration.integrable_bound[OF full_integrable])
        show "slp_localized_riesz_integrand R f z
            \<in> borel_measurable lborel"
          by (rule slp_localized_riesz_integrand_measurable[OF f_measurable])
        show "AE y in lborel.
            norm (slp_localized_riesz_integrand R f z y) \<le>
            norm (aim_planar_riesz_integrand f z y)"
        proof (rule AE_I2)
          fix y :: slp_point
          show "norm (slp_localized_riesz_integrand R f z y) \<le>
              norm (aim_planar_riesz_integrand f z y)"
            using slp_localized_riesz_integrand_le[OF radius_nonnegative]
              slp_localized_riesz_integrand_nonnegative[of R f z y]
            by (simp add: aim_planar_riesz_integrand_def)
        qed
      qed
    qed
    have localized_le_full:
      "AE z in lborel.
        slp_localized_riesz_potential R f z \<le>
          aim_planar_riesz_potential f z"
      using localized_integrable conjunct1[OF full_result]
    proof eventually_elim
      fix z :: slp_point
      assume local_integrable:
          "integrable lborel (slp_localized_riesz_integrand R f z)"
        and full_integrable:
          "integrable lborel (aim_planar_riesz_integrand f z)"
      show "slp_localized_riesz_potential R f z \<le>
          aim_planar_riesz_potential f z"
        unfolding slp_localized_riesz_potential_def
          aim_planar_riesz_potential_def
        by (rule integral_mono[OF local_integrable full_integrable])
          (simp add: slp_localized_riesz_integrand_le[OF radius_nonnegative])
    qed
    have localized_nonnegative:
      "AE z in lborel. 0 \<le> slp_localized_riesz_potential R f z"
      using localized_integrable
    proof eventually_elim
      fix z :: slp_point
      assume local_integrable:
        "integrable lborel (slp_localized_riesz_integrand R f z)"
      show "0 \<le> slp_localized_riesz_potential R f z"
        unfolding slp_localized_riesz_potential_def
        by (rule Bochner_Integration.integral_nonneg)
          (simp add: slp_localized_riesz_integrand_nonnegative)
    qed
    have target_positive: "0 < aim_hls_target_exponent p"
      unfolding aim_hls_target_exponent_def
      using p_lower p_upper by (intro divide_pos_pos mult_pos_pos) auto
    have full_lp:
      "aim_real_lp_on_plane (aim_hls_target_exponent p)
        (aim_planar_riesz_potential f)"
      using full_result by blast
    have localized_measurable:
      "slp_localized_riesz_potential R f \<in> borel_measurable lborel"
      by (rule slp_localized_riesz_potential_measurable[OF f_measurable])
    have localized_power_integrable:
      "integrable lborel
        (\<lambda>z. abs (slp_localized_riesz_potential R f z) powr
          aim_hls_target_exponent p)"
    proof (rule Bochner_Integration.integrable_bound)
      show "integrable lborel
          (\<lambda>z. abs (aim_planar_riesz_potential f z) powr
            aim_hls_target_exponent p)"
        using full_lp unfolding aim_real_lp_on_plane_def by blast
      show "(\<lambda>z. abs (slp_localized_riesz_potential R f z) powr
          aim_hls_target_exponent p) \<in> borel_measurable lborel"
        using localized_measurable by measurable
      show "AE z in lborel.
          norm (abs (slp_localized_riesz_potential R f z) powr
            aim_hls_target_exponent p) \<le>
          norm (abs (aim_planar_riesz_potential f z) powr
            aim_hls_target_exponent p)"
        using localized_le_full localized_nonnegative
      proof eventually_elim
        fix z :: slp_point
        assume local_le:
            "slp_localized_riesz_potential R f z \<le>
              aim_planar_riesz_potential f z"
          and local_nonnegative:
            "0 \<le> slp_localized_riesz_potential R f z"
        have full_nonnegative:
          "0 \<le> aim_planar_riesz_potential f z"
          using local_nonnegative local_le by linarith
        show "norm (abs (slp_localized_riesz_potential R f z) powr
              aim_hls_target_exponent p) \<le>
            norm (abs (aim_planar_riesz_potential f z) powr
              aim_hls_target_exponent p)"
          using powr_mono2[OF less_imp_le[OF target_positive]
              local_nonnegative local_le]
            local_nonnegative full_nonnegative
          by simp
      qed
    qed
    have localized_lp:
      "aim_real_lp_on_plane (aim_hls_target_exponent p)
        (slp_localized_riesz_potential R f)"
      unfolding aim_real_lp_on_plane_def
      using localized_measurable localized_power_integrable by blast
    have power_integral_le:
      "(\<integral>z. abs (slp_localized_riesz_potential R f z) powr
          aim_hls_target_exponent p \<partial>lborel) \<le>
        (\<integral>z. abs (aim_planar_riesz_potential f z) powr
          aim_hls_target_exponent p \<partial>lborel)"
      by (rule integral_mono_AE)
        (use localized_lp full_lp localized_le_full localized_nonnegative
          target_positive in
          \<open>auto simp: aim_real_lp_on_plane_def intro!: powr_mono2\<close>)
    have localized_norm_le:
      "aim_real_lp_norm (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R f) \<le>
        aim_real_lp_norm (aim_hls_target_exponent p)
          (aim_planar_riesz_potential f)"
      unfolding aim_real_lp_norm_def
      by (rule powr_mono2)
        (use target_positive power_integral_le in
          \<open>auto intro!: Bochner_Integration.integral_nonneg\<close>)
    have localized_bound:
      "aim_real_lp_norm (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      using localized_norm_le full_result by linarith
    show "(AE z in lborel.
        integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent p)
        (slp_localized_riesz_potential R f) \<and>
      aim_real_lp_norm (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      using localized_integrable localized_lp localized_bound by blast
  qed
  show ?thesis
    using C_positive all_localized by blast
qed

end

end
