theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Square_Annular_Cauchy
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Cutoff_Inverse_Delta"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Square_Denominator_Annular"
begin

section \<open>Translated annular control of the rough square source\<close>

definition slp_w1p_global_far_square_annular_majorant ::
    "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow>
      slp_point \<Rightarrow> real"
where
  "slp_w1p_global_far_square_annular_majorant delta R c z y =
    slp_annular_J1_full_integrand delta R (z - c) (y - c) +
    slp_annular_J2_full_integrand delta R (z - c) (y - c)"

lemma slp_w1p_global_far_square_annular_majorant_integral:
  assumes delta_positive: "0 < delta"
  shows majorant_integrable:
      "integrable lborel
        (slp_w1p_global_far_square_annular_majorant delta R c z)"
    and majorant_integral:
      "integral\<^sup>L lborel
          (slp_w1p_global_far_square_annular_majorant delta R c z) =
        integral\<^sup>L lborel
            (slp_annular_J1_full_integrand delta R (z - c)) +
          integral\<^sup>L lborel
            (slp_annular_J2_full_integrand delta R (z - c))"
proof -
  let ?H = "\<lambda>x.
    slp_annular_J1_full_integrand delta R (z - c) x +
    slp_annular_J2_full_integrand delta R (z - c) x"
  have J1_integrable:
      "integrable lborel
        (slp_annular_J1_full_integrand delta R (z - c))"
    by (rule slp_annular_J1_full_integrable[OF delta_positive])
  have J2_integrable:
      "integrable lborel
        (slp_annular_J2_full_integrand delta R (z - c))"
    by (rule slp_annular_J2_full_integrable[OF delta_positive])
  have H_integrable: "integrable lborel ?H"
    by (rule Bochner_Integration.integrable_add[OF
          J1_integrable J2_integrable])
  have translated_integrable:
      "integrable lborel (\<lambda>y. ?H (-c + y))"
    by (rule slp_lborel_integrable_translate[OF H_integrable])
  have translated_presentation:
      "(\<lambda>y. ?H (-c + y)) =
        slp_w1p_global_far_square_annular_majorant delta R c z"
    by (rule ext)
      (simp only: slp_w1p_global_far_square_annular_majorant_def
        diff_conv_add_uminus add.commute)
  show "integrable lborel
      (slp_w1p_global_far_square_annular_majorant delta R c z)"
    using translated_integrable
    by (simp only: translated_presentation)

  have translated_integral:
      "integral\<^sup>L lborel (\<lambda>y. ?H (-c + y)) =
        integral\<^sup>L lborel ?H"
    by (rule slp_lborel_integral_translate[OF H_integrable])
  have H_integral:
      "integral\<^sup>L lborel ?H =
        integral\<^sup>L lborel
            (slp_annular_J1_full_integrand delta R (z - c)) +
          integral\<^sup>L lborel
            (slp_annular_J2_full_integrand delta R (z - c))"
    by (rule Bochner_Integration.integral_add[OF
          J1_integrable J2_integrable])
  show "integral\<^sup>L lborel
        (slp_w1p_global_far_square_annular_majorant delta R c z) =
      integral\<^sup>L lborel
          (slp_annular_J1_full_integrand delta R (z - c)) +
        integral\<^sup>L lborel
          (slp_annular_J2_full_integrand delta R (z - c))"
    using translated_integral H_integral
    by (simp only: translated_presentation)
qed

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_global_far_square_denominator_cauchy_annular_bound:
  fixes b A R :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    and relative_radius: "\<And>y. y \<in> X \<Longrightarrow> norm (y - c) \<le> R"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows cauchy_integrable:
      "slp_cauchy_integrable_at orientation
        (slp_oscillatory_modulation tau c
          (slp_w1p_global_far_square_denominator_source delta c X u)) z"
    and annular_bound:
      "norm (slp_cauchy_transform orientation
          (slp_oscillatory_modulation tau c
            (slp_w1p_global_far_square_denominator_source delta c X u)) z)
        \<le>
        norm (inverse (of_real pi :: complex)) *
          ((norm (inverse (of_real pi :: complex)) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q)) *
            (192 * slp_w1p_norm_on b X u Du)) *
          (integral\<^sup>L lborel
              (slp_annular_J1_full_integrand delta R (z - c)) +
            integral\<^sup>L lborel
              (slp_annular_J2_full_integrand delta R (z - c)))"
proof -
  let ?S =
    "slp_w1p_global_far_square_denominator_source delta c X u"
  let ?G = "slp_oscillatory_modulation tau c ?S"
  let ?H =
    "slp_w1p_global_far_square_annular_majorant delta R c z"
  let ?M =
    "(norm (inverse (of_real pi :: complex)) *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)) *
      (192 * slp_w1p_norm_on b X u Du)"
  let ?F = "\<lambda>x. slp_restrict_field X u (c + x)"

  have restricted_lp:
      "aim_complex_lp_on_plane b (slp_restrict_field X u)"
    using zero_pair
    unfolding slp_w1p_zero_pair_on_def slp_w1p_pair_on_def
      slp_complex_lp_on_def
    by blast
  have amplitude_measurable:
      "slp_restrict_field X u \<in> borel_measurable lborel"
    using restricted_lp unfolding aim_complex_lp_on_plane_def by blast
  have source_measurable: "?S \<in> borel_measurable lborel"
    unfolding slp_w1p_global_far_square_denominator_source_def
    using slp_global_scaled_cutoff_borel_measurable[of delta c]
      amplitude_measurable
    apply measurable
    subgoal using slp_point_as_complex_borel_measurable by measurable
    subgoal by (rule amplitude_measurable)
    done
  have center_kernel_measurable:
      "slp_center_kernel tau c \<in> borel_measurable lborel"
    by (rule slp_center_kernel_measurable)
  have modulated_measurable: "?G \<in> borel_measurable lborel"
    unfolding slp_oscillatory_modulation_def
    using center_kernel_measurable source_measurable by measurable

  have M_nonnegative: "0 \<le> ?M"
    unfolding slp_w1p_norm_on_def
    by (intro mult_nonneg_nonneg) simp_all
  have amplitude_bound:
      "AE y in lborel. norm (slp_restrict_field X u y) \<le> ?M"
    unfolding q_def
    by (rule slp_w1p_zero_pair_AE_pointwise_bound_on_bounded_set[
          OF exponent_above_two radius_nonnegative set_radius zero_pair])

  have shifted_radius: "?F x \<noteq> 0 \<Longrightarrow> norm x \<le> R" for x
  proof -
    assume shifted_nonzero: "?F x \<noteq> 0"
    have shifted_in: "c + x \<in> X"
      using shifted_nonzero
      unfolding slp_restrict_field_def by (cases "c + x \<in> X") simp_all
    have "norm ((c + x) - c) \<le> R"
      by (rule relative_radius[OF shifted_in])
    then show "norm x \<le> R"
      by simp
  qed

  have integrand_bound:
      "AE y in lborel.
        norm (slp_cauchy_integrand orientation ?G z y) \<le> ?M * ?H y"
  proof (use amplitude_bound in eventually_elim)
    fix y :: slp_point
    assume amplitude_at:
        "norm (slp_restrict_field X u y) \<le> ?M"
    have cutoff_translate:
        "slp_global_cutoff.slp_scaled_cutoff delta 0 (y - c) =
          slp_global_cutoff.slp_scaled_cutoff delta c y"
      unfolding slp_global_cutoff.slp_scaled_cutoff_def
        slp_global_cutoff.slp_cutoff_argument_def
      by simp
    have norm_presentation:
        "norm (slp_cauchy_integrand orientation ?G z y) =
          norm (slp_qstar_square_denominator_integrand delta ?F
            (z - c) (y - c))"
      unfolding slp_cauchy_integrand_def
        slp_w1p_global_far_square_denominator_source_def
        slp_qstar_square_denominator_integrand_def
      by (simp only: norm_mult slp_oscillatory_modulation_norm
          slp_cauchy_kernel_norm norm_of_real norm_inverse norm_power
          slp_point_as_complex_norm cutoff_translate;
        simp add: algebra_simps)
    have centered_bound:
        "norm (slp_qstar_square_denominator_integrand delta ?F
            (z - c) (y - c)) \<le>
          slp_qstar_annular_J1_integrand delta R ?F
              (z - c) (y - c) +
            slp_qstar_annular_J2_weighted_integrand delta R ?F
              (z - c) (y - c)"
      by (rule slp_qstar_square_denominator_integrand_le_annular[
            OF delta_positive shifted_radius])
    have carriers_nonnegative:
        "0 \<le> slp_annular_J1_full_integrand delta R (z - c) (y - c) +
          slp_annular_J2_full_integrand delta R (z - c) (y - c)"
      by simp
    have weighted_presentation:
        "slp_qstar_annular_J1_integrand delta R ?F
              (z - c) (y - c) +
            slp_qstar_annular_J2_weighted_integrand delta R ?F
              (z - c) (y - c) =
          (slp_annular_J1_full_integrand delta R (z - c) (y - c) +
            slp_annular_J2_full_integrand delta R (z - c) (y - c)) *
            norm (slp_restrict_field X u y)"
      unfolding slp_qstar_annular_J1_integrand_def
        slp_qstar_annular_J2_weighted_integrand_def
      by (simp add: algebra_simps)
    have weighted_bound:
        "(slp_annular_J1_full_integrand delta R (z - c) (y - c) +
            slp_annular_J2_full_integrand delta R (z - c) (y - c)) *
            norm (slp_restrict_field X u y) \<le>
          (slp_annular_J1_full_integrand delta R (z - c) (y - c) +
            slp_annular_J2_full_integrand delta R (z - c) (y - c)) * ?M"
      by (rule mult_left_mono[OF amplitude_at carriers_nonnegative])
    show "norm (slp_cauchy_integrand orientation ?G z y) \<le> ?M * ?H y"
      unfolding norm_presentation
        slp_w1p_global_far_square_annular_majorant_def
      using centered_bound weighted_presentation weighted_bound
      by (simp only: mult.commute)
  qed

  note majorant_data =
    slp_w1p_global_far_square_annular_majorant_integral[OF delta_positive,
      of R c z]
  have majorant_integrable: "integrable lborel (\<lambda>y. ?M * ?H y)"
    by (rule integrable_mult_right[OF majorant_data(1)])
  have cauchy_integrand_measurable:
      "slp_cauchy_integrand orientation ?G z \<in> borel_measurable lborel"
    by (rule slp_cauchy_integrand_borel_measurable[OF
          modulated_measurable])
  have raw_integrable:
      "integrable lborel (slp_cauchy_integrand orientation ?G z)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        cauchy_integrand_measurable])
    show "AE y in lborel.
        norm (slp_cauchy_integrand orientation ?G z y) \<le>
          norm (?M * ?H y)"
    proof (use integrand_bound in eventually_elim)
      fix y :: slp_point
      assume pointwise:
          "norm (slp_cauchy_integrand orientation ?G z y) \<le> ?M * ?H y"
      have H_nonnegative: "0 \<le> ?H y"
        unfolding slp_w1p_global_far_square_annular_majorant_def by simp
      have product_nonnegative: "0 \<le> ?M * ?H y"
        by (rule mult_nonneg_nonneg[OF M_nonnegative H_nonnegative])
      show "norm (slp_cauchy_integrand orientation ?G z y) \<le>
          norm (?M * ?H y)"
        using pointwise
        by (simp only: real_norm_def abs_of_nonneg[OF product_nonnegative])
    qed
  qed
  show "slp_cauchy_integrable_at orientation ?G z"
    unfolding slp_cauchy_integrable_at_def by (rule raw_integrable)

  have norm_integrable:
      "integrable lborel
        (\<lambda>y. norm (slp_cauchy_integrand orientation ?G z y))"
    by (rule integrable_norm[OF raw_integrable])
  have integral_domination:
      "integral\<^sup>L lborel
          (\<lambda>y. norm (slp_cauchy_integrand orientation ?G z y)) \<le>
        integral\<^sup>L lborel (\<lambda>y. ?M * ?H y)"
    by (rule integral_mono_AE[OF norm_integrable majorant_integrable
          integrand_bound])
  have scaled_integral:
      "integral\<^sup>L lborel (\<lambda>y. ?M * ?H y) =
        ?M *
          (integral\<^sup>L lborel
              (slp_annular_J1_full_integrand delta R (z - c)) +
            integral\<^sup>L lborel
              (slp_annular_J2_full_integrand delta R (z - c)))"
  proof -
    have constant_presentation:
        "(\<lambda>y. ?M * ?H y) = (\<lambda>y. ?H y * ?M)"
      by (rule ext) (simp only: mult.commute)
    have scalar_integral:
        "integral\<^sup>L lborel (\<lambda>y. ?H y * ?M) =
          integral\<^sup>L lborel ?H * ?M"
      by (rule Bochner_Integration.integral_mult_left[OF
            majorant_data(1)])
    show ?thesis
      using scalar_integral majorant_data(2)
      by (simp only: constant_presentation mult.commute)
  qed
  have transform_raw:
      "norm (slp_cauchy_transform orientation ?G z) \<le>
        norm (inverse (of_real pi :: complex)) *
          integral\<^sup>L lborel
            (\<lambda>y. norm (slp_cauchy_integrand orientation ?G z y))"
    by (rule slp_cauchy_transform_norm_bound)
  have pi_nonnegative:
      "0 \<le> norm (inverse (of_real pi :: complex))"
    by simp
  have scaled_domination:
      "norm (inverse (of_real pi :: complex)) *
          integral\<^sup>L lborel
            (\<lambda>y. norm (slp_cauchy_integrand orientation ?G z y)) \<le>
        norm (inverse (of_real pi :: complex)) *
          integral\<^sup>L lborel (\<lambda>y. ?M * ?H y)"
    by (rule mult_left_mono[OF integral_domination pi_nonnegative])
  have combined_bound:
      "norm (slp_cauchy_transform orientation ?G z) \<le>
        norm (inverse (of_real pi :: complex)) *
          integral\<^sup>L lborel (\<lambda>y. ?M * ?H y)"
    by (rule order_trans[OF transform_raw scaled_domination])
  have final_identity:
      "norm (inverse (of_real pi :: complex)) *
          integral\<^sup>L lborel (\<lambda>y. ?M * ?H y) =
        norm (inverse (of_real pi :: complex)) * ?M *
          (integral\<^sup>L lborel
              (slp_annular_J1_full_integrand delta R (z - c)) +
            integral\<^sup>L lborel
              (slp_annular_J2_full_integrand delta R (z - c)))"
    using scaled_integral by (simp only: mult.assoc)
  show "norm (slp_cauchy_transform orientation ?G z) \<le>
      norm (inverse (of_real pi :: complex)) * ?M *
        (integral\<^sup>L lborel
            (slp_annular_J1_full_integrand delta R (z - c)) +
          integral\<^sup>L lborel
            (slp_annular_J2_full_integrand delta R (z - c)))"
    using combined_bound by (simp only: final_identity)
qed

end

end
