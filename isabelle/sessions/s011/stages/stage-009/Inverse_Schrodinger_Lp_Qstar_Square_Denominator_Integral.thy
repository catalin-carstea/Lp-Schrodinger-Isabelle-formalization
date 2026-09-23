theory Inverse_Schrodinger_Lp_Qstar_Square_Denominator_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Square_Denominator_Annular"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The centered square-denominator Bochner integral\<close>

definition slp_qstar_square_denominator_integral ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_qstar_square_denominator_integral delta f z =
    integral\<^sup>L lborel
      (slp_qstar_square_denominator_integrand delta f z)"

context aim_planar_riesz_hls
begin

theorem slp_qstar_square_denominator_integral_bound:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and radius_lower: "delta \<le> R"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    and amplitude_radius: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
  shows output_measurable:
      "slp_qstar_square_denominator_integral delta f
        \<in> borel_measurable lborel"
    and fiber_integrable:
      "AE z in lborel. integrable lborel
        (slp_qstar_square_denominator_integrand delta f z)"
    and pointwise_bound:
      "AE z in lborel.
        norm (slp_qstar_square_denominator_integral delta f z) \<le>
          slp_qstar_annular_J12_potential delta R f z"
proof -
  have amplitude_measurable: "f \<in> borel_measurable lborel"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
  have amplitude_borel_measurable:
      "f \<in> borel_measurable borel"
    using amplitude_measurable by simp
  have point_fst_borel_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (fst pair)) \<in>
        borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by (rule measurable_fst''[OF
          slp_point_as_complex_borel_measurable])
  have point_snd_borel_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (snd pair)) \<in>
        borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by (rule measurable_snd''[OF
          slp_point_as_complex_borel_measurable])
  have difference_joint_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (fst pair) -
            slp_point_as_complex (snd pair)) \<in>
        borel_measurable (borel \<Otimes>\<^sub>M borel)"
    using point_fst_borel_measurable point_snd_borel_measurable
    by measurable
  have conjugate_continuous: "continuous_on UNIV cnj"
    by (rule continuous_on_cnj[OF continuous_on_id])
  have denominator_joint_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          cnj (slp_point_as_complex (fst pair) -
            slp_point_as_complex (snd pair))) \<in>
        borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by (rule borel_measurable_continuous_on[OF conjugate_continuous
          difference_joint_measurable])
  have point_lborel_measurable:
      "slp_point_as_complex \<in> borel_measurable lborel"
    using slp_point_as_complex_borel_measurable by measurable
  have point_snd_lborel_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule measurable_snd''[OF point_lborel_measurable])
  have point_fst_lborel_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (fst pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule measurable_fst''[OF point_lborel_measurable])
  have cutoff_continuous:
      "continuous_on UNIV
        (slp_global_cutoff.slp_scaled_cutoff delta 0)"
  proof (rule continuous_at_imp_continuous_on)
    show "\<forall>y \<in> UNIV.
        isCont (slp_global_cutoff.slp_scaled_cutoff delta 0) y"
      by (intro ballI has_derivative_continuous[OF
            slp_global_cutoff.slp_scaled_cutoff_has_derivative])
  qed
  have cutoff_borel_measurable:
      "slp_global_cutoff.slp_scaled_cutoff delta 0 \<in>
        borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF cutoff_continuous])
  have cutoff_snd_borel_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_global_cutoff.slp_scaled_cutoff delta 0 (snd pair)) \<in>
        borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by (rule measurable_snd''[OF cutoff_borel_measurable])
  have cutoff_lborel_measurable:
      "slp_global_cutoff.slp_scaled_cutoff delta 0 \<in>
        borel_measurable lborel"
  proof (rule borel_measurable_subalgebra[where N=borel])
    show "sets borel \<subseteq> sets (lborel :: slp_point measure)"
      by simp
    show "space borel = space (lborel :: slp_point measure)"
      by simp
    show "slp_global_cutoff.slp_scaled_cutoff delta 0 \<in>
        borel_measurable borel"
      by (rule cutoff_borel_measurable)
  qed
  have cutoff_snd_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_global_cutoff.slp_scaled_cutoff delta 0 (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule measurable_snd''[OF cutoff_lborel_measurable])
  have amplitude_snd_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point. f (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule measurable_snd''[OF amplitude_measurable])
  have amplitude_snd_borel_measurable [measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point. f (snd pair)) \<in>
        borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by (rule measurable_snd''[OF amplitude_borel_measurable])
  have difference_joint_lborel_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (fst pair) -
            slp_point_as_complex (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using point_fst_lborel_measurable point_snd_lborel_measurable
    by measurable
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
  have cutoff_complex_joint_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          (of_real (1 -
            slp_global_cutoff.slp_scaled_cutoff delta 0 (snd pair)) :: complex)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  proof -
    have complement_measurable:
        "(\<lambda>pair :: slp_point \<times> slp_point.
            1 - slp_global_cutoff.slp_scaled_cutoff delta 0 (snd pair)) \<in>
          borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      using cutoff_snd_measurable by measurable
    have complex_constructor_measurable:
        "(\<lambda>pair :: slp_point \<times> slp_point.
            Complex
              (1 - slp_global_cutoff.slp_scaled_cutoff delta 0 (snd pair))
              0) \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      unfolding borel_measurable_complex_iff
      using complement_measurable by simp
    have constructor_eq:
        "(\<lambda>pair :: slp_point \<times> slp_point.
            of_real (1 -
              slp_global_cutoff.slp_scaled_cutoff delta 0 (snd pair))) =
          (\<lambda>pair. Complex
            (1 - slp_global_cutoff.slp_scaled_cutoff delta 0 (snd pair)) 0)"
      by (rule ext) (simp add: complex_eq_iff)
    show ?thesis
      by (subst constructor_eq) (rule complex_constructor_measurable)
  qed
  have inverse_square_joint_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          inverse (slp_point_as_complex (snd pair)) ^ 2) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using point_snd_borel_measurable by measurable
  have integrand_joint_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_qstar_square_denominator_integrand delta f
            (fst pair) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding slp_qstar_square_denominator_integrand_def
    using kernel_joint_measurable cutoff_complex_joint_measurable
      inverse_square_joint_measurable amplitude_snd_borel_measurable
    by measurable
  show "slp_qstar_square_denominator_integral delta f
      \<in> borel_measurable lborel"
    unfolding slp_qstar_square_denominator_integral_def
    by (rule lborel.borel_measurable_lebesgue_integral)
      (use integrand_joint_measurable in simp)
  have J2_fiber_integrable:
      "AE z in lborel. integrable lborel
        (slp_qstar_annular_J2_weighted_integrand delta R f z)"
    using slp_qstar_annular_J2_riesz_hls exponent_lower exponent_upper
      delta_positive radius_lower amplitude_lp by blast
  have local_data:
      "integrable lborel
          (slp_qstar_annular_J2_weighted_integrand delta R f z) \<Longrightarrow>
        integrable lborel
            (slp_qstar_square_denominator_integrand delta f z) \<and>
        norm (slp_qstar_square_denominator_integral delta f z) \<le>
          slp_qstar_annular_J12_potential delta R f z"
    for z
  proof -
    assume J2_integrable:
      "integrable lborel
        (slp_qstar_annular_J2_weighted_integrand delta R f z)"
    have J1_integrable:
        "integrable lborel
          (slp_qstar_annular_J1_integrand delta R f z)"
      by (rule slp_qstar_annular_J1_envelope(1)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    let ?majorant = "\<lambda>y.
      slp_qstar_annular_J1_integrand delta R f z y +
      slp_qstar_annular_J2_weighted_integrand delta R f z y"
    have majorant_integrable: "integrable lborel ?majorant"
      by (rule Bochner_Integration.integrable_add[OF J1_integrable
            J2_integrable])
    have integrand_measurable:
        "slp_qstar_square_denominator_integrand delta f z
          \<in> borel_measurable lborel"
      unfolding slp_qstar_square_denominator_integrand_def
      using slp_cauchy_kernel_borel_measurable
      apply measurable
      subgoal by (rule slp_point_as_complex_borel_measurable)
      subgoal by (rule amplitude_measurable)
      done
    have integrand_integrable:
        "integrable lborel
          (slp_qstar_square_denominator_integrand delta f z)"
    proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
          integrand_measurable])
      show "AE y in lborel.
          norm (slp_qstar_square_denominator_integrand delta f z y) \<le>
            norm (?majorant y)"
      proof (rule AE_I2)
        fix y :: slp_point
        have raw_bound:
            "norm (slp_qstar_square_denominator_integrand delta f z y) \<le>
              ?majorant y"
          by (rule slp_qstar_square_denominator_integrand_le_annular[OF
                delta_positive amplitude_radius])
        have majorant_nonnegative: "0 \<le> ?majorant y"
          unfolding slp_qstar_annular_J1_integrand_def
          using slp_qstar_annular_J2_weighted_integrand_nonnegative by simp
        show "norm (slp_qstar_square_denominator_integrand delta f z y) \<le>
            norm (?majorant y)"
          using raw_bound majorant_nonnegative
          by (simp only: real_norm_def abs_of_nonneg)
      qed
    qed
    have norm_integrable:
        "integrable lborel
          (\<lambda>y. norm
            (slp_qstar_square_denominator_integrand delta f z y))"
      by (rule integrable_norm[OF integrand_integrable])
    have integral_mono:
        "integral\<^sup>L lborel
            (\<lambda>y. norm
              (slp_qstar_square_denominator_integrand delta f z y)) \<le>
          integral\<^sup>L lborel ?majorant"
    proof (rule Bochner_Integration.integral_mono[OF norm_integrable
          majorant_integrable])
      fix y :: slp_point
      assume "y \<in> space lborel"
      show "norm (slp_qstar_square_denominator_integrand delta f z y) \<le>
          ?majorant y"
        by (rule slp_qstar_square_denominator_integrand_le_annular[OF
              delta_positive amplitude_radius])
    qed
    have integral_norm:
        "norm (integral\<^sup>L lborel
            (slp_qstar_square_denominator_integrand delta f z)) \<le>
          integral\<^sup>L lborel
            (\<lambda>y. norm
              (slp_qstar_square_denominator_integrand delta f z y))"
      by (rule Bochner_Integration.integral_norm_bound)
    have majorant_value:
        "integral\<^sup>L lborel ?majorant =
          slp_qstar_annular_J12_potential delta R f z"
      unfolding slp_qstar_annular_J12_potential_def
        slp_qstar_annular_J1_potential_def
        slp_qstar_annular_J2_potential_def
      using J1_integrable J2_integrable by simp
    have output_bound:
        "norm (slp_qstar_square_denominator_integral delta f z) \<le>
          slp_qstar_annular_J12_potential delta R f z"
      unfolding slp_qstar_square_denominator_integral_def
      by (rule order_trans[OF integral_norm])
        (use integral_mono majorant_value in simp)
    show ?thesis
      using integrand_integrable output_bound by blast
  qed
  show "AE z in lborel. integrable lborel
      (slp_qstar_square_denominator_integrand delta f z)"
    using J2_fiber_integrable
  proof eventually_elim
    fix z :: slp_point
    assume "integrable lborel
      (slp_qstar_annular_J2_weighted_integrand delta R f z)"
    then show "integrable lborel
      (slp_qstar_square_denominator_integrand delta f z)"
      using local_data by blast
  qed
  show "AE z in lborel.
      norm (slp_qstar_square_denominator_integral delta f z) \<le>
        slp_qstar_annular_J12_potential delta R f z"
    using J2_fiber_integrable
  proof eventually_elim
    fix z :: slp_point
    assume "integrable lborel
      (slp_qstar_annular_J2_weighted_integrand delta R f z)"
    then show "norm (slp_qstar_square_denominator_integral delta f z) \<le>
        slp_qstar_annular_J12_potential delta R f z"
      using local_data by blast
  qed
qed

end

end
