theory Inverse_Schrodinger_Lp_Qstar_Cutoff_Partial_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Cutoff_Partial_Annular"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_Combined_Constant"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Smooth_Far_Product"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The centered cutoff-partial Bochner integral\<close>

lemma slp_qstar_cutoff_partial_coefficient_borel_measurable:
  "(\<lambda>y. slp_real_wirtinger_partial
      (slp_global_cutoff.slp_scaled_cutoff_derivative delta c y)) \<in>
    borel_measurable borel"
proof -
  let ?chi = "slp_global_cutoff.slp_scaled_cutoff delta c"
  have chi_smooth: "smooth_on UNIV ?chi"
    by (rule slp_global_scaled_cutoff_smooth)
  have derivative_eq:
      "slp_global_cutoff.slp_scaled_cutoff_derivative delta c y =
        frechet_derivative ?chi (at y)" for y
  proof -
    have declared:
        "(?chi has_derivative
          slp_global_cutoff.slp_scaled_cutoff_derivative delta c y) (at y)"
      by (rule slp_global_cutoff.slp_scaled_cutoff_has_derivative)
    have differentiable: "?chi differentiable at y"
      by (rule differentiableI[OF declared])
    have canonical:
        "(?chi has_derivative frechet_derivative ?chi (at y)) (at y)"
      using differentiable by (simp only: frechet_derivative_works)
    show ?thesis
      by (rule has_derivative_unique[OF declared canonical])
  qed
  have coordinate_zero_smooth:
      "smooth_on UNIV
        (\<lambda>y. frechet_derivative ?chi (at y) (axis (0 :: 2) 1))"
    by (rule smooth_on_frechet_derivative[OF chi_smooth])
  have coordinate_one_smooth:
      "smooth_on UNIV
        (\<lambda>y. frechet_derivative ?chi (at y) (axis (1 :: 2) 1))"
    by (rule smooth_on_frechet_derivative[OF chi_smooth])
  have coordinate_zero_continuous:
      "continuous_on UNIV
        (\<lambda>y. frechet_derivative ?chi (at y) (axis (0 :: 2) 1))"
    by (rule higher_differentiable_on_imp_continuous_on)
      (rule smooth_onD[OF coordinate_zero_smooth], simp)
  have coordinate_one_continuous:
      "continuous_on UNIV
        (\<lambda>y. frechet_derivative ?chi (at y) (axis (1 :: 2) 1))"
    by (rule higher_differentiable_on_imp_continuous_on)
      (rule smooth_onD[OF coordinate_one_smooth], simp)
  have coordinate_zero_measurable:
      "(\<lambda>y. frechet_derivative ?chi (at y) (axis (0 :: 2) 1)) \<in>
        borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          coordinate_zero_continuous])
  have coordinate_one_measurable:
      "(\<lambda>y. frechet_derivative ?chi (at y) (axis (1 :: 2) 1)) \<in>
        borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          coordinate_one_continuous])
  have presentation:
      "(\<lambda>y. slp_real_wirtinger_partial
          (slp_global_cutoff.slp_scaled_cutoff_derivative delta c y)) =
        (\<lambda>y.
          of_real (frechet_derivative ?chi (at y) (axis (0 :: 2) 1)) / 2 -
          \<i> * of_real
            (frechet_derivative ?chi (at y) (axis (1 :: 2) 1)) / 2)"
    by (rule ext)
      (simp only: slp_real_wirtinger_partial_def derivative_eq)
  show ?thesis
    unfolding presentation
    using coordinate_zero_measurable coordinate_one_measurable by measurable
qed

definition slp_qstar_cutoff_partial_integral ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_qstar_cutoff_partial_integral delta f z =
    integral\<^sup>L lborel (slp_qstar_cutoff_partial_integrand delta f z)"

context aim_planar_riesz_hls
begin

theorem slp_qstar_cutoff_partial_integral_bound:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows output_measurable:
      "slp_qstar_cutoff_partial_integral delta f \<in>
        borel_measurable lborel"
    and fiber_integrable:
      "AE z in lborel. integrable lborel
        (slp_qstar_cutoff_partial_integrand delta f z)"
    and pointwise_bound:
      "AE z in lborel.
        norm (slp_qstar_cutoff_partial_integral delta f z) \<le>
          (slp_global_cutoff_L / delta) *
            slp_qstar_annular_combined_potential delta f z"
proof -
  have amplitude_measurable: "f \<in> borel_measurable lborel"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
  have amplitude_borel_measurable: "f \<in> borel_measurable borel"
    using amplitude_measurable by simp
  have point_lborel_measurable:
      "slp_point_as_complex \<in> borel_measurable lborel"
    using slp_point_as_complex_borel_measurable by measurable
  have point_snd_borel_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (snd pair)) \<in>
        borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by (rule measurable_snd''[OF
          slp_point_as_complex_borel_measurable])
  have point_fst_lborel_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (fst pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule measurable_fst''[OF point_lborel_measurable])
  have point_snd_lborel_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule measurable_snd''[OF point_lborel_measurable])
  have difference_joint_lborel_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (fst pair) -
            slp_point_as_complex (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using point_fst_lborel_measurable point_snd_lborel_measurable
    by measurable
  have conjugate_continuous: "continuous_on UNIV cnj"
    by (rule continuous_on_cnj[OF continuous_on_id])
  have denominator_joint_lborel_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          cnj (slp_point_as_complex (fst pair) -
            slp_point_as_complex (snd pair))) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule borel_measurable_continuous_on[OF conjugate_continuous
          difference_joint_lborel_measurable])
  have kernel_joint_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_cauchy_kernel SLP_Partial_Inverse
            (fst pair) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding slp_cauchy_kernel_def slp_cauchy_denominator_def
    using denominator_joint_lborel_measurable
    by (simp only: slp_cauchy_orientation.case
        borel_measurable_inverse)
  have partial_borel_measurable:
      "(\<lambda>y. slp_real_wirtinger_partial
          (slp_global_cutoff.slp_scaled_cutoff_derivative delta 0 y)) \<in>
        borel_measurable borel"
    by (rule slp_qstar_cutoff_partial_coefficient_borel_measurable)
  have partial_lborel_measurable:
      "(\<lambda>y. slp_real_wirtinger_partial
          (slp_global_cutoff.slp_scaled_cutoff_derivative delta 0 y)) \<in>
        borel_measurable lborel"
    using partial_borel_measurable by measurable
  have partial_snd_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_real_wirtinger_partial
            (slp_global_cutoff.slp_scaled_cutoff_derivative
              delta 0 (snd pair))) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule measurable_snd''[OF partial_lborel_measurable])
  have amplitude_snd_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point. f (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule measurable_snd''[OF amplitude_measurable])
  have inverse_snd_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          inverse (slp_point_as_complex (snd pair))) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using point_snd_borel_measurable by measurable
  have integrand_joint_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_qstar_cutoff_partial_integrand delta f
            (fst pair) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding slp_qstar_cutoff_partial_integrand_def
    using kernel_joint_measurable partial_snd_measurable
      inverse_snd_measurable amplitude_snd_measurable
    by measurable
  show "slp_qstar_cutoff_partial_integral delta f \<in>
      borel_measurable lborel"
    unfolding slp_qstar_cutoff_partial_integral_def
    by (rule lborel.borel_measurable_lebesgue_integral)
      (use integrand_joint_measurable in simp)
  have I2_fiber_integrable:
      "AE z in lborel. integrable lborel
        (slp_qstar_annular_I2_weighted_integrand delta f z)"
    using slp_qstar_annular_I2_riesz_hls exponent_lower exponent_upper
      delta_positive amplitude_lp by blast
  have coefficient_nonnegative: "0 \<le> slp_global_cutoff_L / delta"
    using slp_global_cutoff_profile_spec delta_positive by simp
  have local_data:
      "integrable lborel
          (slp_qstar_annular_I2_weighted_integrand delta f z) \<Longrightarrow>
        integrable lborel
            (slp_qstar_cutoff_partial_integrand delta f z) \<and>
        norm (slp_qstar_cutoff_partial_integral delta f z) \<le>
          (slp_global_cutoff_L / delta) *
            slp_qstar_annular_combined_potential delta f z"
    for z
  proof -
    assume I2_integrable:
      "integrable lborel
        (slp_qstar_annular_I2_weighted_integrand delta f z)"
    have I1_integrable:
        "integrable lborel
          (slp_qstar_annular_I1_integrand delta f z)"
      by (rule slp_qstar_annular_I1_envelope(2)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    let ?carrier = "\<lambda>y.
      slp_qstar_annular_I1_integrand delta f z y +
      slp_qstar_annular_I2_weighted_integrand delta f z y"
    let ?majorant = "\<lambda>y.
      (slp_global_cutoff_L / delta) * ?carrier y"
    have carrier_integrable: "integrable lborel ?carrier"
      by (rule Bochner_Integration.integrable_add[OF I1_integrable
            I2_integrable])
    have majorant_integrable: "integrable lborel ?majorant"
      using carrier_integrable by simp
    have integrand_measurable:
        "slp_qstar_cutoff_partial_integrand delta f z \<in>
          borel_measurable lborel"
      unfolding slp_qstar_cutoff_partial_integrand_def
      using slp_cauchy_kernel_borel_measurable partial_lborel_measurable
        amplitude_measurable
      apply measurable
      subgoal by (rule slp_point_as_complex_borel_measurable)
      subgoal by (rule amplitude_measurable)
      done
    have integrand_integrable:
        "integrable lborel
          (slp_qstar_cutoff_partial_integrand delta f z)"
    proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
          integrand_measurable])
      show "AE y in lborel.
          norm (slp_qstar_cutoff_partial_integrand delta f z y) \<le>
            norm (?majorant y)"
      proof (rule AE_I2)
        fix y :: slp_point
        have raw_bound:
            "norm (slp_qstar_cutoff_partial_integrand delta f z y) \<le>
              ?majorant y"
          by (rule slp_qstar_cutoff_partial_integrand_le_annular[OF
                delta_positive])
        have carrier_nonnegative: "0 \<le> ?carrier y"
          unfolding slp_qstar_annular_I1_integrand_def
          using slp_qstar_annular_I2_weighted_integrand_nonnegative by simp
        have majorant_nonnegative: "0 \<le> ?majorant y"
          by (rule mult_nonneg_nonneg[OF coefficient_nonnegative
                carrier_nonnegative])
        show "norm (slp_qstar_cutoff_partial_integrand delta f z y) \<le>
            norm (?majorant y)"
          using raw_bound majorant_nonnegative
          by (simp only: real_norm_def abs_of_nonneg)
      qed
    qed
    have norm_integrable:
        "integrable lborel
          (\<lambda>y. norm (slp_qstar_cutoff_partial_integrand delta f z y))"
      by (rule integrable_norm[OF integrand_integrable])
    have integral_mono:
        "integral\<^sup>L lborel
            (\<lambda>y. norm
              (slp_qstar_cutoff_partial_integrand delta f z y)) \<le>
          integral\<^sup>L lborel ?majorant"
    proof (rule Bochner_Integration.integral_mono[OF norm_integrable
          majorant_integrable])
      fix y :: slp_point
      assume "y \<in> space lborel"
      show "norm (slp_qstar_cutoff_partial_integrand delta f z y) \<le>
          ?majorant y"
        by (rule slp_qstar_cutoff_partial_integrand_le_annular[OF
              delta_positive])
    qed
    have integral_norm:
        "norm (integral\<^sup>L lborel
            (slp_qstar_cutoff_partial_integrand delta f z)) \<le>
          integral\<^sup>L lborel
            (\<lambda>y. norm
              (slp_qstar_cutoff_partial_integrand delta f z y))"
      by (rule Bochner_Integration.integral_norm_bound)
    have majorant_value:
        "integral\<^sup>L lborel ?majorant =
          (slp_global_cutoff_L / delta) *
            slp_qstar_annular_combined_potential delta f z"
      unfolding slp_qstar_annular_combined_potential_def
        slp_qstar_annular_I1_potential_def
        slp_qstar_annular_I2_potential_def
      using I1_integrable I2_integrable by simp
    have output_bound:
        "norm (slp_qstar_cutoff_partial_integral delta f z) \<le>
          (slp_global_cutoff_L / delta) *
            slp_qstar_annular_combined_potential delta f z"
    proof -
      have output_to_majorant:
          "norm (slp_qstar_cutoff_partial_integral delta f z) \<le>
            integral\<^sup>L lborel ?majorant"
        unfolding slp_qstar_cutoff_partial_integral_def
        by (rule order_trans[OF integral_norm integral_mono])
      show ?thesis
        by (rule order_trans[OF output_to_majorant])
          (simp only: majorant_value)
    qed
    show ?thesis
      using integrand_integrable output_bound by blast
  qed
  show "AE z in lborel. integrable lborel
      (slp_qstar_cutoff_partial_integrand delta f z)"
    using I2_fiber_integrable
  proof eventually_elim
    fix z :: slp_point
    assume "integrable lborel
      (slp_qstar_annular_I2_weighted_integrand delta f z)"
    then show "integrable lborel
      (slp_qstar_cutoff_partial_integrand delta f z)"
      using local_data by blast
  qed
  show "AE z in lborel.
      norm (slp_qstar_cutoff_partial_integral delta f z) \<le>
        (slp_global_cutoff_L / delta) *
          slp_qstar_annular_combined_potential delta f z"
    using I2_fiber_integrable
  proof eventually_elim
    fix z :: slp_point
    assume "integrable lborel
      (slp_qstar_annular_I2_weighted_integrand delta f z)"
    then show "norm (slp_qstar_cutoff_partial_integral delta f z) \<le>
        (slp_global_cutoff_L / delta) *
          slp_qstar_annular_combined_potential delta f z"
      using local_data by blast
  qed
qed

end

end
