theory Inverse_Schrodinger_Lp_Qstar_Annular_I2_Riesz_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_I2_Source"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The second annular term from the full positive Riesz bound\<close>

definition slp_qstar_annular_I2_weighted_integrand ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> real"
where
  "slp_qstar_annular_I2_weighted_integrand delta f z y =
    slp_annular_I2_integrand delta z y * norm_class.norm (f y)"

definition slp_qstar_annular_I2_potential ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_qstar_annular_I2_potential delta f z =
    integral\<^sup>L lborel
      (slp_qstar_annular_I2_weighted_integrand delta f z)"

lemma slp_qstar_annular_I2_weighted_integrand_measurable:
  assumes amplitude_measurable: "f \<in> borel_measurable lborel"
  shows "slp_qstar_annular_I2_weighted_integrand delta f z
    \<in> borel_measurable lborel"
  unfolding slp_qstar_annular_I2_weighted_integrand_def
  using amplitude_measurable by measurable

lemma slp_qstar_annular_I2_weighted_integrand_nonnegative:
  "0 \<le> slp_qstar_annular_I2_weighted_integrand delta f z y"
  unfolding slp_qstar_annular_I2_weighted_integrand_def by simp

lemma slp_aim_planar_riesz_integrand_nonnegative:
  "0 \<le> aim_planar_riesz_integrand g z y"
proof -
  have field_norm_nonnegative: "0 \<le> norm_class.norm (g y)"
    by (rule norm_ge_zero)
  have inverse_norm_nonnegative:
    "0 \<le> inverse (norm_class.norm
      (aim_point_as_complex z - aim_point_as_complex y))"
    by (simp only: inverse_nonnegative_iff_nonnegative norm_ge_zero)
  show ?thesis
    unfolding aim_planar_riesz_integrand_def
    by (rule mult_nonneg_nonneg[OF field_norm_nonnegative
          inverse_norm_nonnegative])
qed

lemma slp_qstar_annular_I2_weighted_integrand_le_riesz:
  "slp_qstar_annular_I2_weighted_integrand delta f z y \<le>
    aim_planar_riesz_integrand
      (slp_qstar_annular_I2_source delta f) z y"
proof (cases "delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
    delta \<le> norm (z - y)")
  case True
  have annulus:
      "delta \<le> norm y \<and> norm y \<le> 2 * delta"
    using True by blast
  have complex_difference:
      "aim_point_as_complex z - aim_point_as_complex y =
        slp_point_as_complex (z - y)"
    by (simp only: aim_point_as_complex_eq_slp
        slp_point_as_complex_diff[symmetric])
  have difference_norm:
      "norm_class.norm
          (aim_point_as_complex z - aim_point_as_complex y) =
        norm (z - y)"
    by (simp only: complex_difference slp_point_as_complex_norm)
  have coefficient_value:
      "slp_qstar_annular_I2_coefficient delta y =
        of_real (slp_radial_inverse y)"
    unfolding slp_qstar_annular_I2_coefficient_def if_P[OF annulus]
    by (rule refl)
  have raw_value:
      "slp_annular_I2_integrand delta z y =
        slp_radial_inverse (z - y) * slp_radial_inverse y"
    unfolding slp_annular_I2_integrand_def if_P[OF True]
    by (rule refl)
  have coefficient_norm:
      "norm_class.norm (slp_qstar_annular_I2_coefficient delta y) =
        slp_radial_inverse y"
    by (simp only: coefficient_value norm_of_real
        abs_of_nonneg slp_radial_inverse_nonnegative)
  show ?thesis
    unfolding slp_qstar_annular_I2_weighted_integrand_def
      aim_planar_riesz_integrand_def
      slp_qstar_annular_I2_source_def
    by (simp only: raw_value norm_mult coefficient_norm difference_norm
        slp_radial_inverse_def mult.assoc mult.commute mult.left_commute)
next
  case False
  have raw_zero: "slp_annular_I2_integrand delta z y = 0"
    unfolding slp_annular_I2_integrand_def if_not_P[OF False]
    by (rule refl)
  have weighted_zero:
      "slp_qstar_annular_I2_weighted_integrand delta f z y = 0"
    unfolding slp_qstar_annular_I2_weighted_integrand_def raw_zero
    by simp
  show ?thesis
    unfolding weighted_zero
    by (rule slp_aim_planar_riesz_integrand_nonnegative)
qed

lemma slp_qstar_annular_I2_potential_measurable:
  assumes amplitude_measurable: "f \<in> borel_measurable lborel"
  shows "slp_qstar_annular_I2_potential delta f
    \<in> borel_measurable lborel"
  unfolding slp_qstar_annular_I2_potential_def
    slp_qstar_annular_I2_weighted_integrand_def
    slp_annular_I2_integrand_def
  using amplitude_measurable by measurable

context aim_planar_riesz_hls
begin

theorem slp_qstar_annular_I2_riesz_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a delta f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      (AE z in lborel. integrable lborel
        (slp_qstar_annular_I2_weighted_integrand delta f z)) \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_I2_potential delta f) \<and>
      aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_I2_potential delta f)
        \<le> C / ((a - 1) * (2 - a)) *
          (integral\<^sup>L lborel
            (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f)"
proof -
  obtain C::real where C_positive: "0 < C"
    and C_bound:
      "\<And>p g. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p g \<Longrightarrow>
        (AE z in lborel. integrable lborel
          (aim_planar_riesz_integrand g z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (aim_planar_riesz_potential g) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (aim_planar_riesz_potential g)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p g"
    using aim_planar_riesz_hls
    unfolding aim_planar_riesz_hls_claim_def by blast
  have all_I2:
    "\<forall>a delta f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      (AE z in lborel. integrable lborel
        (slp_qstar_annular_I2_weighted_integrand delta f z)) \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_I2_potential delta f) \<and>
      aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_I2_potential delta f)
        \<le> C / ((a - 1) * (2 - a)) *
          (integral\<^sup>L lborel
            (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
  proof (intro allI impI)
    fix a delta :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    have exponent_lower: "1 < a" and exponent_upper: "a < 2"
      and delta_positive: "0 < delta"
      using hypotheses by blast+
    have amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      using hypotheses by blast
    have amplitude_measurable: "f \<in> borel_measurable lborel"
      using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
    have source_lp:
      "aim_complex_lp_on_plane a
        (slp_qstar_annular_I2_source delta f)"
      by (rule slp_qstar_annular_I2_source_bound(3)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have source_norm_bound:
      "aim_complex_lp_norm a
          (slp_qstar_annular_I2_source delta f) \<le>
        (integral\<^sup>L lborel
          (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
        aim_complex_lp_norm (aim_hls_target_exponent a) f"
      by (rule slp_qstar_annular_I2_source_bound(5)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have full_result:
      "(AE z in lborel. integrable lborel
          (aim_planar_riesz_integrand
            (slp_qstar_annular_I2_source delta f) z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent a)
          (aim_planar_riesz_potential
            (slp_qstar_annular_I2_source delta f)) \<and>
        aim_real_lp_norm (aim_hls_target_exponent a)
            (aim_planar_riesz_potential
              (slp_qstar_annular_I2_source delta f))
          \<le> C / ((a - 1) * (2 - a)) *
            aim_complex_lp_norm a
              (slp_qstar_annular_I2_source delta f)"
      by (rule C_bound[OF exponent_lower exponent_upper source_lp])
    have I2_integrable:
      "AE z in lborel. integrable lborel
        (slp_qstar_annular_I2_weighted_integrand delta f z)"
      using conjunct1[OF full_result]
    proof eventually_elim
      fix z :: slp_point
      assume full_integrable:
        "integrable lborel
          (aim_planar_riesz_integrand
            (slp_qstar_annular_I2_source delta f) z)"
      show "integrable lborel
          (slp_qstar_annular_I2_weighted_integrand delta f z)"
      proof (rule Bochner_Integration.integrable_bound[OF full_integrable])
        show "slp_qstar_annular_I2_weighted_integrand delta f z
            \<in> borel_measurable lborel"
          by (rule slp_qstar_annular_I2_weighted_integrand_measurable[OF
                amplitude_measurable])
        show "AE y in lborel.
            norm (slp_qstar_annular_I2_weighted_integrand delta f z y) \<le>
            norm (aim_planar_riesz_integrand
              (slp_qstar_annular_I2_source delta f) z y)"
        proof (rule AE_I2)
          fix y :: slp_point
          show "norm (slp_qstar_annular_I2_weighted_integrand delta f z y)
              \<le> norm (aim_planar_riesz_integrand
                (slp_qstar_annular_I2_source delta f) z y)"
          proof -
            have pointwise_le:
              "slp_qstar_annular_I2_weighted_integrand delta f z y \<le>
                aim_planar_riesz_integrand
                  (slp_qstar_annular_I2_source delta f) z y"
              by (rule slp_qstar_annular_I2_weighted_integrand_le_riesz)
            have I2_nonnegative_at:
              "0 \<le> slp_qstar_annular_I2_weighted_integrand delta f z y"
              by (rule slp_qstar_annular_I2_weighted_integrand_nonnegative)
            have full_nonnegative_at:
              "0 \<le> aim_planar_riesz_integrand
                (slp_qstar_annular_I2_source delta f) z y"
              by (rule slp_aim_planar_riesz_integrand_nonnegative)
            show ?thesis
              using pointwise_le I2_nonnegative_at full_nonnegative_at
              by (simp only: real_norm_def abs_of_nonneg)
          qed
        qed
      qed
    qed
    have I2_le_full:
      "AE z in lborel.
        slp_qstar_annular_I2_potential delta f z \<le>
          aim_planar_riesz_potential
            (slp_qstar_annular_I2_source delta f) z"
      using I2_integrable conjunct1[OF full_result]
    proof eventually_elim
      fix z :: slp_point
      assume I2_fiber_integrable:
          "integrable lborel
            (slp_qstar_annular_I2_weighted_integrand delta f z)"
        and full_integrable:
          "integrable lborel
            (aim_planar_riesz_integrand
              (slp_qstar_annular_I2_source delta f) z)"
      show "slp_qstar_annular_I2_potential delta f z \<le>
          aim_planar_riesz_potential
            (slp_qstar_annular_I2_source delta f) z"
        unfolding slp_qstar_annular_I2_potential_def
          aim_planar_riesz_potential_def
        by (rule integral_mono[OF I2_fiber_integrable full_integrable])
          (simp add: slp_qstar_annular_I2_weighted_integrand_le_riesz)
    qed
    have I2_nonnegative:
      "AE z in lborel. 0 \<le> slp_qstar_annular_I2_potential delta f z"
      using I2_integrable
    proof eventually_elim
      fix z :: slp_point
      assume I2_fiber_integrable:
        "integrable lborel
          (slp_qstar_annular_I2_weighted_integrand delta f z)"
      show "0 \<le> slp_qstar_annular_I2_potential delta f z"
        unfolding slp_qstar_annular_I2_potential_def
        by (rule Bochner_Integration.integral_nonneg)
          (simp add: slp_qstar_annular_I2_weighted_integrand_nonnegative)
    qed
    have target_positive: "0 < aim_hls_target_exponent a"
      unfolding aim_hls_target_exponent_def
      using exponent_lower exponent_upper
      by (intro divide_pos_pos mult_pos_pos) auto
    have full_lp:
      "aim_real_lp_on_plane (aim_hls_target_exponent a)
        (aim_planar_riesz_potential
          (slp_qstar_annular_I2_source delta f))"
      using full_result by blast
    have I2_measurable:
      "slp_qstar_annular_I2_potential delta f
        \<in> borel_measurable lborel"
      by (rule slp_qstar_annular_I2_potential_measurable[OF
            amplitude_measurable])
    have I2_power_integrable:
      "integrable lborel
        (\<lambda>z. abs (slp_qstar_annular_I2_potential delta f z) powr
          aim_hls_target_exponent a)"
    proof (rule Bochner_Integration.integrable_bound)
      show "integrable lborel
          (\<lambda>z. abs (aim_planar_riesz_potential
              (slp_qstar_annular_I2_source delta f) z) powr
            aim_hls_target_exponent a)"
        using full_lp unfolding aim_real_lp_on_plane_def by blast
      show "(\<lambda>z. abs (slp_qstar_annular_I2_potential delta f z) powr
          aim_hls_target_exponent a) \<in> borel_measurable lborel"
        using I2_measurable by measurable
      show "AE z in lborel.
          norm (abs (slp_qstar_annular_I2_potential delta f z) powr
            aim_hls_target_exponent a) \<le>
          norm (abs (aim_planar_riesz_potential
              (slp_qstar_annular_I2_source delta f) z) powr
            aim_hls_target_exponent a)"
        using I2_le_full I2_nonnegative
      proof eventually_elim
        fix z :: slp_point
        assume I2_le:
            "slp_qstar_annular_I2_potential delta f z \<le>
              aim_planar_riesz_potential
                (slp_qstar_annular_I2_source delta f) z"
          and I2_nonnegative_at:
            "0 \<le> slp_qstar_annular_I2_potential delta f z"
        have full_nonnegative:
          "0 \<le> aim_planar_riesz_potential
            (slp_qstar_annular_I2_source delta f) z"
          using I2_nonnegative_at I2_le by linarith
        show "norm (abs (slp_qstar_annular_I2_potential delta f z) powr
              aim_hls_target_exponent a) \<le>
            norm (abs (aim_planar_riesz_potential
                (slp_qstar_annular_I2_source delta f) z) powr
              aim_hls_target_exponent a)"
          using powr_mono2[OF less_imp_le[OF target_positive]
              I2_nonnegative_at I2_le]
            I2_nonnegative_at full_nonnegative
          by simp
      qed
    qed
    have I2_lp:
      "aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_I2_potential delta f)"
      unfolding aim_real_lp_on_plane_def
      using I2_measurable I2_power_integrable by blast
    have power_integral_le:
      "(\<integral>z. abs (slp_qstar_annular_I2_potential delta f z) powr
          aim_hls_target_exponent a \<partial>lborel) \<le>
        (\<integral>z. abs (aim_planar_riesz_potential
            (slp_qstar_annular_I2_source delta f) z) powr
          aim_hls_target_exponent a \<partial>lborel)"
      by (rule integral_mono_AE)
        (use I2_lp full_lp I2_le_full I2_nonnegative target_positive in
          \<open>auto simp: aim_real_lp_on_plane_def intro!: powr_mono2\<close>)
    have I2_norm_le:
      "aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_I2_potential delta f) \<le>
        aim_real_lp_norm (aim_hls_target_exponent a)
          (aim_planar_riesz_potential
            (slp_qstar_annular_I2_source delta f))"
      unfolding aim_real_lp_norm_def
      by (rule powr_mono2)
        (use target_positive power_integral_le in
          \<open>auto intro!: Bochner_Integration.integral_nonneg\<close>)
    have I2_to_source:
      "aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_I2_potential delta f) \<le>
        C / ((a - 1) * (2 - a)) *
          aim_complex_lp_norm a
            (slp_qstar_annular_I2_source delta f)"
      using I2_norm_le full_result by linarith
    have HLS_factor_nonnegative:
      "0 \<le> C / ((a - 1) * (2 - a))"
    proof (rule divide_nonneg_nonneg)
      show "0 \<le> C"
        using C_positive by linarith
      show "0 \<le> (a - 1) * (2 - a)"
        using exponent_lower exponent_upper by (intro mult_nonneg_nonneg) auto
    qed
    have source_to_amplitude:
      "C / ((a - 1) * (2 - a)) *
          aim_complex_lp_norm a
            (slp_qstar_annular_I2_source delta f) \<le>
        C / ((a - 1) * (2 - a)) *
          ((integral\<^sup>L lborel
            (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f)"
      by (rule mult_left_mono[OF source_norm_bound
            HLS_factor_nonnegative])
    have final_bound:
      "aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_I2_potential delta f)
        \<le> C / ((a - 1) * (2 - a)) *
          (integral\<^sup>L lborel
            (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
      using order_trans[OF I2_to_source source_to_amplitude]
      by (simp only: mult.assoc)
    show "(AE z in lborel. integrable lborel
          (slp_qstar_annular_I2_weighted_integrand delta f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent a)
          (slp_qstar_annular_I2_potential delta f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent a)
            (slp_qstar_annular_I2_potential delta f)
          \<le> C / ((a - 1) * (2 - a)) *
            (integral\<^sup>L lborel
              (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f"
      using I2_integrable I2_lp final_bound by blast
  qed
  show ?thesis
    using C_positive all_I2 by blast
qed

end

end
