theory Inverse_Schrodinger_Lp_Qstar_Smooth_Near_Far_Operator_Split
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Smooth_Far_IBP"
begin

section \<open>The exact smooth near/far operator split\<close>


theorem slp_qstar_smooth_near_far_operator_split:
  assumes delta_positive: "0 < delta"
    and f_test: "slp_test_function_on UNIV f"
  shows
    "slp_partial_psi_inverse tau c f =
      (\<lambda>z.
        slp_partial_psi_inverse tau c
          (slp_global_cutoff.slp_near_cutoff_amplitude delta c f) z +
        slp_partial_psi_inverse tau c
          (slp_global_far_cutoff_amplitude delta c f) z)"
proof (rule ext)
  fix z :: slp_point
  have cutoff_profile:
      "slp_cutoff_profile slp_global_cutoff_chi
        slp_global_cutoff_Dchi slp_global_cutoff_L"
    by (rule slp_global_cutoff_profile_spec[THEN conjunct1])
  note far_definition =
    slp_cutoff_profile.slp_far_cutoff_amplitude_def[
      where chi = slp_global_cutoff_chi
        and Dchi = slp_global_cutoff_Dchi
        and L = slp_global_cutoff_L,
      OF cutoff_profile]
  note split_rule =
    slp_cutoff_profile.slp_partial_psi_inverse_near_far_split(2)[
      where chi = slp_global_cutoff_chi
        and Dchi = slp_global_cutoff_Dchi
        and L = slp_global_cutoff_L,
      OF cutoff_profile]
  let ?phi = "slp_global_cutoff.slp_far_product delta c f"
  have f_integrable: "integrable lborel f"
    by (rule slp_test_function_integrable_bounded(1)[OF f_test])
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_integrable by measurable
  have f_bounded: "bounded (range f)"
    by (rule slp_test_function_integrable_bounded(2)[OF f_test])
  obtain M where f_bound: "\<And>x. norm_class.norm (f x) \<le> M"
    using f_bounded unfolding bounded_iff by auto
  have M_nonnegative: "0 \<le> M"
  proof -
    have "0 \<le> norm_class.norm (f 0)" by simp
    then show ?thesis using f_bound[of 0] by linarith
  qed
  have phi_test: "slp_test_function_on UNIV ?phi"
    by (rule slp_global_far_product_test_function[OF delta_positive f_test])
  have source_test:
      "slp_test_function_on UNIV
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * ?phi x)"
    by (rule slp_center_coordinate_amplitude_test_function[OF phi_test])
  have source_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * ?phi x) z"
    by (rule slp_test_function_cauchy_integrable_at[OF source_test])
  have input_eq:
      "(\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * ?phi x) =
        slp_oscillatory_modulation tau c
          (slp_global_far_cutoff_amplitude delta c f)"
  proof (rule ext)
    fix x :: slp_point
    show "(slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * ?phi x =
        slp_oscillatory_modulation tau c
          (slp_global_far_cutoff_amplitude delta c f) x"
    proof (cases "x = c")
      case True
      have cutoff_one:
          "slp_global_cutoff.slp_scaled_cutoff delta c x = 1"
        unfolding True
        by (rule slp_global_cutoff.slp_scaled_cutoff_inner[
              OF delta_positive]) (use delta_positive in simp)
      have coordinate_zero: "slp_point_as_complex (x - c) = 0"
      proof (rule iffD2[OF slp_point_as_complex_eq_zero_iff])
        show "x - c = 0"
          unfolding True by (rule diff_self)
      qed
      show ?thesis
        unfolding slp_global_cutoff.slp_far_product_def
          slp_global_far_cutoff_amplitude_def
          slp_global_scaled_cutoff_def
          slp_oscillatory_modulation_def
        by (simp only: coordinate_zero cutoff_one diff_self of_real_0
              mult_zero_left mult_zero_right)
    next
      case False
      have difference_nonzero:
          "slp_point_as_complex (x - c) \<noteq> 0"
      proof
        assume zero: "slp_point_as_complex (x - c) = 0"
        then have "x - c = 0"
          by (simp only: slp_point_as_complex_eq_zero_iff)
        with False show False by simp
      qed
      have inverse_cancel:
          "slp_point_as_complex (x - c) *
              inverse (slp_point_as_complex (x - c)) = 1"
        by (rule right_inverse[OF difference_nonzero])
      have regroup:
          "(slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) *
            (of_real (1 -
                slp_global_cutoff.slp_scaled_cutoff delta c x) *
              inverse (slp_point_as_complex (x - c)) * f x) =
          (slp_center_kernel tau c x *
              (of_real (1 -
                slp_global_cutoff.slp_scaled_cutoff delta c x) * f x)) *
            (slp_point_as_complex (x - c) *
              inverse (slp_point_as_complex (x - c)))"
        by (simp only: ac_simps)
      have algebra:
          "(slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) *
            (of_real (1 -
                slp_global_cutoff.slp_scaled_cutoff delta c x) *
              inverse (slp_point_as_complex (x - c)) * f x) =
          slp_center_kernel tau c x *
            (of_real (1 -
              slp_global_cutoff.slp_scaled_cutoff delta c x) * f x)"
        by (rule trans[OF regroup])
          (simp only: inverse_cancel mult_1_right)
      show ?thesis
        unfolding slp_global_cutoff.slp_far_product_def
          slp_global_far_cutoff_amplitude_def
          slp_global_scaled_cutoff_def
          slp_oscillatory_modulation_def
        by (rule algebra)
    qed
  qed
  have far_integrable_global:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_global_far_cutoff_amplitude delta c f)) z"
    using source_integrable unfolding input_eq .
  have far_eq:
      "slp_cutoff_profile.slp_far_cutoff_amplitude
          slp_global_cutoff_chi delta c f =
        slp_global_far_cutoff_amplitude delta c f"
  proof (rule ext)
    fix y :: slp_point
    have local_formula:
      "slp_cutoff_profile.slp_far_cutoff_amplitude
          slp_global_cutoff_chi delta c f y =
          of_real (1 - slp_cutoff_profile.slp_scaled_cutoff
            slp_global_cutoff_chi delta c y) *
            f y"
      by (rule far_definition)
    have scaled_eq:
        "slp_cutoff_profile.slp_scaled_cutoff
            slp_global_cutoff_chi delta c y =
          slp_global_cutoff.slp_scaled_cutoff delta c y"
      unfolding slp_global_cutoff.slp_scaled_cutoff_def by (rule refl)
    show
        "slp_cutoff_profile.slp_far_cutoff_amplitude
            slp_global_cutoff_chi delta c f y =
          slp_global_far_cutoff_amplitude delta c f y"
      using local_formula scaled_eq
      unfolding slp_global_far_cutoff_amplitude_def
        slp_global_scaled_cutoff_def
      by simp
  qed
  have near_eq:
      "slp_cutoff_profile.slp_near_cutoff_amplitude
          slp_global_cutoff_chi delta c f =
        slp_global_cutoff.slp_near_cutoff_amplitude delta c f"
    unfolding slp_global_cutoff.slp_near_cutoff_amplitude_def
    by (rule refl)
  have far_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_cutoff_profile.slp_far_cutoff_amplitude
            slp_global_cutoff_chi delta c f)) z"
    using far_integrable_global unfolding far_eq .
  have split:
      "slp_partial_psi_inverse tau c f z =
        slp_partial_psi_inverse tau c
          (slp_cutoff_profile.slp_near_cutoff_amplitude
            slp_global_cutoff_chi delta c f) z +
        slp_partial_psi_inverse tau c
          (slp_cutoff_profile.slp_far_cutoff_amplitude
            slp_global_cutoff_chi delta c f) z"
  proof (rule split_rule[
        where delta = delta and f = f and M = M
          and tau = tau and c = c and z = z])
    show "0 < delta" by (rule delta_positive)
    show "f \<in> borel_measurable lborel" by (rule f_measurable)
    show "0 \<le> M" by (rule M_nonnegative)
    show "\<And>y. norm (f y) \<le> M" by (rule f_bound)
    show "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_cutoff_profile.slp_far_cutoff_amplitude
            slp_global_cutoff_chi delta c f)) z"
      by (rule far_integrable)
  qed
  show
      "slp_partial_psi_inverse tau c f z =
        slp_partial_psi_inverse tau c
          (slp_global_cutoff.slp_near_cutoff_amplitude delta c f) z +
        slp_partial_psi_inverse tau c
          (slp_global_far_cutoff_amplitude delta c f) z"
    apply (subst near_eq[symmetric])
    apply (subst far_eq[symmetric])
    by (rule split)
qed

end
