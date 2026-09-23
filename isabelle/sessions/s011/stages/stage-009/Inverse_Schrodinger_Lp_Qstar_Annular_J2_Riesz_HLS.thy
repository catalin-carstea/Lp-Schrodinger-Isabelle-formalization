theory Inverse_Schrodinger_Lp_Qstar_Annular_J2_Riesz_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_J2_Source"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Annular_J2_Full_Bounds"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The far-output square term from the full positive Riesz bound\<close>

definition slp_qstar_annular_J2_weighted_integrand ::
  "real \<Rightarrow> real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> real"
where
  "slp_qstar_annular_J2_weighted_integrand delta R f z y =
    slp_annular_J2_full_integrand delta R z y * norm_class.norm (f y)"

definition slp_qstar_annular_J2_potential ::
  "real \<Rightarrow> real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_qstar_annular_J2_potential delta R f z =
    integral\<^sup>L lborel
      (slp_qstar_annular_J2_weighted_integrand delta R f z)"

lemma slp_qstar_annular_J2_weighted_integrand_measurable:
  assumes amplitude_measurable: "f \<in> borel_measurable lborel"
  shows "slp_qstar_annular_J2_weighted_integrand delta R f z
    \<in> borel_measurable lborel"
  unfolding slp_qstar_annular_J2_weighted_integrand_def
  using amplitude_measurable by measurable

lemma slp_qstar_annular_J2_weighted_integrand_nonnegative:
  "0 \<le> slp_qstar_annular_J2_weighted_integrand delta R f z y"
  unfolding slp_qstar_annular_J2_weighted_integrand_def by simp

lemma slp_qstar_annular_J2_weighted_integrand_le_riesz:
  "slp_qstar_annular_J2_weighted_integrand delta R f z y \<le>
    aim_planar_riesz_integrand
      (slp_qstar_annular_J2_source delta R f) z y"
proof (cases "delta \<le> norm y \<and> norm y \<le> R \<and>
    delta \<le> norm (z - y)")
  case True
  have annulus: "delta \<le> norm y \<and> norm y \<le> R"
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
      "slp_qstar_annular_J2_coefficient delta R y =
        of_real (slp_radial_inverse_square y)"
    unfolding slp_qstar_annular_J2_coefficient_def if_P[OF annulus]
    by (rule refl)
  have raw_value:
      "slp_annular_J2_full_integrand delta R z y =
        slp_radial_inverse (z - y) * slp_radial_inverse_square y"
    unfolding slp_annular_J2_full_integrand_def if_P[OF True]
    by (rule refl)
  have coefficient_norm:
      "norm_class.norm (slp_qstar_annular_J2_coefficient delta R y) =
        slp_radial_inverse_square y"
    by (simp only: coefficient_value norm_of_real
        abs_of_nonneg slp_radial_inverse_square_nonnegative)
  show ?thesis
    unfolding slp_qstar_annular_J2_weighted_integrand_def
      aim_planar_riesz_integrand_def
      slp_qstar_annular_J2_source_def
    by (simp only: raw_value norm_mult coefficient_norm difference_norm
        slp_radial_inverse_def mult.assoc mult.commute mult.left_commute)
next
  case False
  have raw_zero: "slp_annular_J2_full_integrand delta R z y = 0"
    unfolding slp_annular_J2_full_integrand_def if_not_P[OF False]
    by (rule refl)
  have weighted_zero:
      "slp_qstar_annular_J2_weighted_integrand delta R f z y = 0"
    unfolding slp_qstar_annular_J2_weighted_integrand_def raw_zero
    by simp
  show ?thesis
    unfolding weighted_zero
    by (rule slp_aim_planar_riesz_integrand_nonnegative)
qed

lemma slp_qstar_annular_J2_potential_measurable:
  assumes amplitude_measurable: "f \<in> borel_measurable lborel"
  shows "slp_qstar_annular_J2_potential delta R f
    \<in> borel_measurable lborel"
  unfolding slp_qstar_annular_J2_potential_def
    slp_qstar_annular_J2_weighted_integrand_def
    slp_annular_J2_full_integrand_def
  using amplitude_measurable by measurable

theorem slp_nonnegative_real_lp_mono:
  assumes exponent_positive: "0 < p"
    and minorant_measurable: "u \<in> borel_measurable lborel"
    and majorant_lp: "aim_real_lp_on_plane p v"
    and minorant_nonnegative: "AE z in lborel. 0 \<le> u z"
    and pointwise: "AE z in lborel. u z \<le> v z"
  shows membership: "aim_real_lp_on_plane p u"
    and norm_bound: "aim_real_lp_norm p u \<le> aim_real_lp_norm p v"
proof -
  have majorant_power_integrable:
      "integrable lborel (\<lambda>z. abs (v z) powr p)"
    using majorant_lp unfolding aim_real_lp_on_plane_def by blast
  have power_bound:
      "AE z in lborel.
        norm (abs (u z) powr p) \<le> norm (abs (v z) powr p)"
    using minorant_nonnegative pointwise
  proof eventually_elim
    fix z :: slp_point
    assume u_nonnegative: "0 \<le> u z" and u_le: "u z \<le> v z"
    have v_nonnegative: "0 \<le> v z"
      using u_nonnegative u_le by linarith
    have powered: "u z powr p \<le> v z powr p"
      by (rule powr_mono2[OF less_imp_le[OF exponent_positive]
            u_nonnegative u_le])
    show "norm (abs (u z) powr p) \<le> norm (abs (v z) powr p)"
      using powered u_nonnegative v_nonnegative by simp
  qed
  have minorant_power_measurable:
      "(\<lambda>z. abs (u z) powr p) \<in> borel_measurable lborel"
    using minorant_measurable by measurable
  have minorant_power_integrable:
      "integrable lborel (\<lambda>z. abs (u z) powr p)"
    by (rule Bochner_Integration.integrable_bound[OF
          majorant_power_integrable minorant_power_measurable power_bound])
  show membership: "aim_real_lp_on_plane p u"
    unfolding aim_real_lp_on_plane_def
    using minorant_measurable minorant_power_integrable by blast
  have power_integral_le:
      "(\<integral>z. abs (u z) powr p \<partial>lborel) \<le>
        (\<integral>z. abs (v z) powr p \<partial>lborel)"
    by (rule integral_mono_AE[OF minorant_power_integrable
          majorant_power_integrable])
      (use power_bound in simp)
  show norm_bound: "aim_real_lp_norm p u \<le> aim_real_lp_norm p v"
    unfolding aim_real_lp_norm_def
    by (rule powr_mono2)
      (use exponent_positive power_integral_le in
        \<open>auto intro!: Bochner_Integration.integral_nonneg\<close>)
qed

context aim_planar_riesz_hls
begin

theorem slp_qstar_annular_J2_riesz_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a delta R f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      (AE z in lborel. integrable lborel
        (slp_qstar_annular_J2_weighted_integrand delta R f z)) \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_J2_potential delta R f) \<and>
      aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_J2_potential delta R f)
        \<le> C / ((a - 1) * (2 - a)) * (1 / delta) *
          slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
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
  have all_J2:
    "\<forall>a delta R f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      (AE z in lborel. integrable lborel
        (slp_qstar_annular_J2_weighted_integrand delta R f z)) \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_J2_potential delta R f) \<and>
      aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_J2_potential delta R f)
        \<le> C / ((a - 1) * (2 - a)) * (1 / delta) *
          slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
  proof (intro allI impI)
    fix a delta R :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    have exponent_lower: "1 < a" and exponent_upper: "a < 2"
      and delta_positive: "0 < delta" and radius_lower: "delta \<le> R"
      using hypotheses by blast+
    have amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      using hypotheses by blast
    have amplitude_measurable: "f \<in> borel_measurable lborel"
      using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
    have source_lp:
      "aim_complex_lp_on_plane a
        (slp_qstar_annular_J2_source delta R f)"
      by (rule slp_qstar_annular_J2_source_bound(4)[OF exponent_lower
            exponent_upper delta_positive radius_lower amplitude_lp])
    have source_norm_bound:
      "aim_complex_lp_norm a
          (slp_qstar_annular_J2_source delta R f) \<le>
        (1 / delta) *
          slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
      by (rule slp_qstar_annular_J2_source_bound(6)[OF exponent_lower
            exponent_upper delta_positive radius_lower amplitude_lp])
    have full_result:
      "(AE z in lborel. integrable lborel
          (aim_planar_riesz_integrand
            (slp_qstar_annular_J2_source delta R f) z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent a)
          (aim_planar_riesz_potential
            (slp_qstar_annular_J2_source delta R f)) \<and>
        aim_real_lp_norm (aim_hls_target_exponent a)
            (aim_planar_riesz_potential
              (slp_qstar_annular_J2_source delta R f))
          \<le> C / ((a - 1) * (2 - a)) *
            aim_complex_lp_norm a
              (slp_qstar_annular_J2_source delta R f)"
      by (rule C_bound[OF exponent_lower exponent_upper source_lp])
    have J2_integrable:
      "AE z in lborel. integrable lborel
        (slp_qstar_annular_J2_weighted_integrand delta R f z)"
      using conjunct1[OF full_result]
    proof eventually_elim
      fix z :: slp_point
      assume full_integrable:
        "integrable lborel
          (aim_planar_riesz_integrand
            (slp_qstar_annular_J2_source delta R f) z)"
      show "integrable lborel
          (slp_qstar_annular_J2_weighted_integrand delta R f z)"
      proof (rule Bochner_Integration.integrable_bound[OF full_integrable])
        show "slp_qstar_annular_J2_weighted_integrand delta R f z
            \<in> borel_measurable lborel"
          by (rule slp_qstar_annular_J2_weighted_integrand_measurable[OF
                amplitude_measurable])
        show "AE y in lborel.
            norm (slp_qstar_annular_J2_weighted_integrand delta R f z y) \<le>
            norm (aim_planar_riesz_integrand
              (slp_qstar_annular_J2_source delta R f) z y)"
        proof (rule AE_I2)
          fix y :: slp_point
          have pointwise_le:
            "slp_qstar_annular_J2_weighted_integrand delta R f z y \<le>
              aim_planar_riesz_integrand
                (slp_qstar_annular_J2_source delta R f) z y"
            by (rule slp_qstar_annular_J2_weighted_integrand_le_riesz)
          show "norm (slp_qstar_annular_J2_weighted_integrand delta R f z y)
              \<le> norm (aim_planar_riesz_integrand
                (slp_qstar_annular_J2_source delta R f) z y)"
            using pointwise_le
              slp_qstar_annular_J2_weighted_integrand_nonnegative[of
                delta R f z y]
              slp_aim_planar_riesz_integrand_nonnegative[of
                "slp_qstar_annular_J2_source delta R f" z y]
            by (simp only: real_norm_def abs_of_nonneg)
        qed
      qed
    qed
    have J2_le_full:
      "AE z in lborel.
        slp_qstar_annular_J2_potential delta R f z \<le>
          aim_planar_riesz_potential
            (slp_qstar_annular_J2_source delta R f) z"
      using J2_integrable conjunct1[OF full_result]
    proof eventually_elim
      fix z :: slp_point
      assume J2_fiber_integrable:
          "integrable lborel
            (slp_qstar_annular_J2_weighted_integrand delta R f z)"
        and full_integrable:
          "integrable lborel
            (aim_planar_riesz_integrand
              (slp_qstar_annular_J2_source delta R f) z)"
      show "slp_qstar_annular_J2_potential delta R f z \<le>
          aim_planar_riesz_potential
            (slp_qstar_annular_J2_source delta R f) z"
        unfolding slp_qstar_annular_J2_potential_def
          aim_planar_riesz_potential_def
        by (rule integral_mono[OF J2_fiber_integrable full_integrable])
          (simp add: slp_qstar_annular_J2_weighted_integrand_le_riesz)
    qed
    have J2_nonnegative:
      "AE z in lborel. 0 \<le> slp_qstar_annular_J2_potential delta R f z"
      using J2_integrable
    proof eventually_elim
      fix z :: slp_point
      assume J2_fiber_integrable:
        "integrable lborel
          (slp_qstar_annular_J2_weighted_integrand delta R f z)"
      show "0 \<le> slp_qstar_annular_J2_potential delta R f z"
        unfolding slp_qstar_annular_J2_potential_def
        by (rule Bochner_Integration.integral_nonneg)
          (simp add: slp_qstar_annular_J2_weighted_integrand_nonnegative)
    qed
    have target_positive: "0 < aim_hls_target_exponent a"
      unfolding aim_hls_target_exponent_def
      using exponent_lower exponent_upper
      by (intro divide_pos_pos mult_pos_pos) auto
    have J2_measurable:
      "slp_qstar_annular_J2_potential delta R f
        \<in> borel_measurable lborel"
      by (rule slp_qstar_annular_J2_potential_measurable[OF
            amplitude_measurable])
    have J2_lp:
      "aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_J2_potential delta R f)"
      by (rule slp_nonnegative_real_lp_mono(1)[OF target_positive
            J2_measurable conjunct1[OF conjunct2[OF full_result]]
            J2_nonnegative J2_le_full])
    have J2_norm_le:
      "aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_J2_potential delta R f) \<le>
        aim_real_lp_norm (aim_hls_target_exponent a)
          (aim_planar_riesz_potential
            (slp_qstar_annular_J2_source delta R f))"
      by (rule slp_nonnegative_real_lp_mono(2)[OF target_positive
            J2_measurable conjunct1[OF conjunct2[OF full_result]]
            J2_nonnegative J2_le_full])
    have J2_to_source:
      "aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_J2_potential delta R f) \<le>
        C / ((a - 1) * (2 - a)) *
          aim_complex_lp_norm a
            (slp_qstar_annular_J2_source delta R f)"
      using J2_norm_le full_result by linarith
    have HLS_factor_nonnegative:
      "0 \<le> C / ((a - 1) * (2 - a))"
    proof (rule divide_nonneg_nonneg)
      show "0 \<le> C"
        using C_positive by linarith
      show "0 \<le> (a - 1) * (2 - a)"
        using exponent_lower exponent_upper
        by (intro mult_nonneg_nonneg) auto
    qed
    have source_to_amplitude:
      "C / ((a - 1) * (2 - a)) *
          aim_complex_lp_norm a
            (slp_qstar_annular_J2_source delta R f) \<le>
        C / ((a - 1) * (2 - a)) *
          ((1 / delta) *
            slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f)"
      by (rule mult_left_mono[OF source_norm_bound
            HLS_factor_nonnegative])
    have final_bound:
      "aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_J2_potential delta R f) \<le>
        C / ((a - 1) * (2 - a)) * (1 / delta) *
          slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
      using order_trans[OF J2_to_source source_to_amplitude]
      by (simp only: mult.assoc)
    show "(AE z in lborel. integrable lborel
          (slp_qstar_annular_J2_weighted_integrand delta R f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent a)
          (slp_qstar_annular_J2_potential delta R f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent a)
            (slp_qstar_annular_J2_potential delta R f)
          \<le> C / ((a - 1) * (2 - a)) * (1 / delta) *
            slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f"
      using J2_integrable J2_lp final_bound by blast
  qed
  show ?thesis
    using C_positive all_J2 by blast
qed

end

end
