theory Inverse_Schrodinger_Lp_W1p_Rough_Near_Essential_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Complete_Derivative_Center"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Oscillatory_Partial_AE_Congruence"
begin

section \<open>Near-cutoff control from an essential uniform bound\<close>

theorem slp_global_near_partial_psi_inverse_AE_uniform_bound:
  assumes delta_positive: "0 < delta"
    and f_measurable: "f \<in> borel_measurable lborel"
    and M_nonnegative: "0 \<le> M"
    and f_bound: "AE y in (lborel :: slp_point measure). norm (f y) \<le> M"
  shows cauchy_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_global_cutoff.slp_near_cutoff_amplitude delta c f)) z"
    and near_bound:
      "norm (slp_partial_psi_inverse tau c
          (slp_global_cutoff.slp_near_cutoff_amplitude delta c f) z) \<le>
        norm (inverse (of_real pi :: complex)) * M * delta *
          (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
            2 * unit_ball_vol 2)"
proof -
  let ?g = "\<lambda>y. if norm (f y) \<le> M then f y else 0"
  let ?F = "slp_global_cutoff.slp_near_cutoff_amplitude delta c f"
  let ?G = "slp_global_cutoff.slp_near_cutoff_amplitude delta c ?g"
  have g_measurable: "?g \<in> borel_measurable lborel"
    using f_measurable by measurable
  have g_bound: "norm (?g y) \<le> M" for y
    using M_nonnegative by (cases "norm (f y) \<le> M") simp_all
  have g_eq_f: "AE y in (lborel :: slp_point measure). ?g y = f y"
    using f_bound by eventually_elim simp
  have near_eq: "AE y in (lborel :: slp_point measure). ?F y = ?G y"
    using g_eq_f by eventually_elim
      (simp add: slp_global_cutoff.slp_near_cutoff_amplitude_def)
  have F_measurable: "?F \<in> borel_measurable lborel"
    by (rule slp_global_cutoff.slp_near_cutoff_amplitude_measurable[
          OF f_measurable])
  have G_measurable: "?G \<in> borel_measurable lborel"
    by (rule slp_global_cutoff.slp_near_cutoff_amplitude_measurable[
          OF g_measurable])
  have G_cauchy:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c ?G) z"
    by (rule slp_cutoff_profile.slp_near_partial_psi_integrable_at[
          OF slp_global_cutoff_profile_spec[THEN conjunct1]
            delta_positive g_measurable M_nonnegative g_bound])
  have F_modulated_measurable:
      "slp_oscillatory_modulation tau c ?F \<in> borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable[OF F_measurable])
  have F_integrand_measurable:
      "slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c ?F) z
        \<in> borel_measurable lborel"
    by (rule slp_cauchy_integrand_borel_measurable[
          OF F_modulated_measurable])
  have integrand_eq:
      "AE y in (lborel :: slp_point measure).
        slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c ?G) z y =
          slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c ?F) z y"
    using near_eq by eventually_elim
      (simp add: slp_oscillatory_modulation_def slp_cauchy_integrand_def)
  have G_raw:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c ?G) z)"
    using G_cauchy unfolding slp_cauchy_integrable_at_def .
  have F_raw:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c ?F) z)"
    by (rule integrable_cong_AE_imp[
          OF G_raw F_integrand_measurable integrand_eq])
  show "slp_cauchy_integrable_at SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c ?F) z"
    unfolding slp_cauchy_integrable_at_def by (rule F_raw)

  have clipped_bound:
      "norm (slp_partial_psi_inverse tau c ?G z) \<le>
        norm (inverse (of_real pi :: complex)) * M * delta *
          (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
            2 * unit_ball_vol 2)"
    by (rule slp_cutoff_profile.slp_near_partial_psi_inverse_uniform_bound[
          OF slp_global_cutoff_profile_spec[THEN conjunct1]
            delta_positive g_measurable M_nonnegative g_bound])
  have operator_eq:
      "slp_partial_psi_inverse tau c ?F =
        slp_partial_psi_inverse tau c ?G"
    by (rule slp_partial_psi_inverse_cong_AE[
          OF F_measurable G_measurable near_eq])
  show "norm (slp_partial_psi_inverse tau c ?F z) \<le>
      norm (inverse (of_real pi :: complex)) * M * delta *
        (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
          2 * unit_ball_vol 2)"
    unfolding operator_eq by (rule clipped_bound)
qed

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_near_center_bound:
  fixes b A :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows cauchy_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_global_cutoff.slp_near_cutoff_amplitude delta c
            (slp_restrict_field X u))) c"
    and near_bound:
      "norm (slp_partial_psi_inverse tau c
          (slp_global_cutoff.slp_near_cutoff_amplitude delta c
            (slp_restrict_field X u)) c) \<le>
        norm (inverse (of_real pi :: complex)) *
          ((norm (inverse (of_real pi :: complex)) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
                powr (1 / q)) *
            (192 * slp_w1p_norm_on b X u Du)) * delta *
          (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
            2 * unit_ball_vol 2)"
proof -
  let ?f = "slp_restrict_field X u"
  let ?M =
    "(norm (inverse (of_real pi :: complex)) *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)) *
      (192 * slp_w1p_norm_on b X u Du)"
  have restricted_lp: "aim_complex_lp_on_plane b ?f"
    using zero_pair
    unfolding slp_w1p_zero_pair_on_def slp_w1p_pair_on_def
      slp_complex_lp_on_def
    by blast
  have f_measurable: "?f \<in> borel_measurable lborel"
    using restricted_lp unfolding aim_complex_lp_on_plane_def by blast
  have M_nonnegative: "0 \<le> ?M"
  proof (rule mult_nonneg_nonneg)
    show "0 \<le> norm (inverse (of_real pi :: complex)) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
            powr (1 / q)"
      by simp
    show "0 \<le> 192 * slp_w1p_norm_on b X u Du"
      unfolding slp_w1p_norm_on_def by simp
  qed
  have f_bound: "AE y in (lborel :: slp_point measure). norm (?f y) \<le> ?M"
    unfolding q_def
    by (rule slp_w1p_zero_pair_AE_pointwise_bound_on_bounded_set[
          OF exponent_above_two radius_nonnegative set_radius zero_pair])
  note near = slp_global_near_partial_psi_inverse_AE_uniform_bound[
    OF delta_positive f_measurable M_nonnegative f_bound,
      where tau=tau and c=c and z=c]
  show "slp_cauchy_integrable_at SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c
        (slp_global_cutoff.slp_near_cutoff_amplitude delta c ?f)) c"
    by (rule near(1))
  show "norm (slp_partial_psi_inverse tau c
      (slp_global_cutoff.slp_near_cutoff_amplitude delta c ?f) c) \<le>
      norm (inverse (of_real pi :: complex)) * ?M * delta *
        (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
          2 * unit_ball_vol 2)"
    by (rule near(2))
qed

end

end
