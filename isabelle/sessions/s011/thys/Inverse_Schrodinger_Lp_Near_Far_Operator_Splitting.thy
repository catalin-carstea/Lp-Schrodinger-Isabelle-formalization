theory Inverse_Schrodinger_Lp_Near_Far_Operator_Splitting
  imports Inverse_Schrodinger_Lp_Near_Center_Operator_Bridge
begin

section \<open>Exact cutoff splitting of the oscillatory Cauchy operator\<close>

context slp_cutoff_profile
begin

definition slp_far_cutoff_amplitude ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field"
where
  "slp_far_cutoff_amplitude delta c f y =
    of_real (1 - slp_scaled_cutoff delta c y) * f y"

lemma slp_far_cutoff_amplitude_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_far_cutoff_amplitude delta c f \<in>
    borel_measurable lborel"
  unfolding slp_far_cutoff_amplitude_def
  using f_measurable by measurable

lemma slp_near_far_cutoff_amplitude_split:
  "slp_near_cutoff_amplitude delta c f y +
      slp_far_cutoff_amplitude delta c f y = f y"
  unfolding slp_near_cutoff_amplitude_def
    slp_far_cutoff_amplitude_def
  by (simp add: algebra_simps)

lemma slp_far_cutoff_amplitude_inner:
  assumes delta_positive: "0 < delta"
    and inside: "norm (y - c) \<le> delta"
  shows "slp_far_cutoff_amplitude delta c f y = 0"
  using slp_scaled_cutoff_inner[OF delta_positive inside]
  by (simp add: slp_far_cutoff_amplitude_def)

lemma slp_far_cutoff_amplitude_outer:
  assumes delta_positive: "0 < delta"
    and outside: "2 * delta \<le> norm (y - c)"
  shows "slp_far_cutoff_amplitude delta c f y = f y"
  using slp_scaled_cutoff_outer[OF delta_positive outside]
  by (simp add: slp_far_cutoff_amplitude_def)

lemma slp_oscillatory_near_far_split:
  "slp_oscillatory_modulation tau c f =
    (\<lambda>y. slp_oscillatory_modulation tau c
        (slp_near_cutoff_amplitude delta c f) y +
      slp_oscillatory_modulation tau c
        (slp_far_cutoff_amplitude delta c f) y)"
proof (rule ext)
  fix y :: slp_point
  have recovery:
      "slp_near_cutoff_amplitude delta c f y +
        slp_far_cutoff_amplitude delta c f y = f y"
    by (rule slp_near_far_cutoff_amplitude_split)
  show "slp_oscillatory_modulation tau c f y =
      slp_oscillatory_modulation tau c
          (slp_near_cutoff_amplitude delta c f) y +
        slp_oscillatory_modulation tau c
          (slp_far_cutoff_amplitude delta c f) y"
    unfolding slp_oscillatory_modulation_def
    apply (subst recovery[symmetric])
    by (simp add: algebra_simps)
qed

lemma slp_near_partial_psi_integrable_at:
  assumes delta_positive: "0 < delta"
    and f_measurable: "f \<in> borel_measurable lborel"
    and M_nonnegative: "0 \<le> M"
    and f_bound: "\<And>y. norm (f y) \<le> M"
  shows "slp_cauchy_integrable_at SLP_Partial_Inverse
    (slp_oscillatory_modulation tau c
      (slp_near_cutoff_amplitude delta c f)) z"
proof (unfold slp_cauchy_integrable_at_def)
  let ?g = "slp_oscillatory_modulation tau c
    (slp_near_cutoff_amplitude delta c f)"
  let ?majorant = "\<lambda>y.
    M * slp_near_center_scalar_kernel delta c z y"
  have near_integrable:
    "integrable lborel (slp_near_center_scalar_kernel delta c z)"
    by (rule slp_near_center_scalar_integrable[OF delta_positive])
  have majorant_integrable: "integrable lborel ?majorant"
    using near_integrable by (rule integrable_mult_right)
  have g_measurable: "?g \<in> borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable)
       (rule slp_near_cutoff_amplitude_measurable[OF f_measurable])
  show "integrable lborel
      (slp_cauchy_integrand SLP_Partial_Inverse ?g z)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_cauchy_integrand SLP_Partial_Inverse ?g z \<in>
        borel_measurable lborel"
      by (rule slp_cauchy_integrand_borel_measurable[OF g_measurable])
    show "AE y in lborel.
        norm (slp_cauchy_integrand SLP_Partial_Inverse ?g z y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have bound:
        "norm (slp_cauchy_integrand SLP_Partial_Inverse ?g z y) \<le>
          ?majorant y"
        by (rule slp_near_oscillatory_integrand_norm_bound[OF
              delta_positive M_nonnegative f_bound])
      have majorant_nonnegative: "0 \<le> ?majorant y"
        using M_nonnegative by simp
      show "norm (slp_cauchy_integrand SLP_Partial_Inverse ?g z y) \<le>
          norm (?majorant y)"
        using bound majorant_nonnegative by simp
    qed
  qed
qed

lemma slp_partial_psi_inverse_near_far_split:
  assumes delta_positive: "0 < delta"
    and f_measurable: "f \<in> borel_measurable lborel"
    and M_nonnegative: "0 \<le> M"
    and f_bound: "\<And>y. norm (f y) \<le> M"
    and far_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_far_cutoff_amplitude delta c f)) z"
  shows "slp_cauchy_integrable_at SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c f) z"
    and "slp_partial_psi_inverse tau c f z =
      slp_partial_psi_inverse tau c
        (slp_near_cutoff_amplitude delta c f) z +
      slp_partial_psi_inverse tau c
        (slp_far_cutoff_amplitude delta c f) z"
proof -
  have near_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_near_cutoff_amplitude delta c f)) z"
    by (rule slp_near_partial_psi_integrable_at[OF delta_positive
          f_measurable M_nonnegative f_bound])
  have sum_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>y. slp_oscillatory_modulation tau c
            (slp_near_cutoff_amplitude delta c f) y +
          slp_oscillatory_modulation tau c
            (slp_far_cutoff_amplitude delta c f) y) z"
    by (rule slp_cauchy_integrable_at_add[OF near_integrable
          far_integrable])
  show total_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c f) z"
    apply (subst slp_oscillatory_near_far_split)
    by (rule sum_integrable)
  have transform_split:
      "slp_cauchy_transform SLP_Partial_Inverse
          (\<lambda>y. slp_oscillatory_modulation tau c
              (slp_near_cutoff_amplitude delta c f) y +
            slp_oscillatory_modulation tau c
              (slp_far_cutoff_amplitude delta c f) y) z =
        slp_cauchy_transform SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c
            (slp_near_cutoff_amplitude delta c f)) z +
        slp_cauchy_transform SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c
            (slp_far_cutoff_amplitude delta c f)) z"
    by (rule slp_cauchy_transform_add[OF near_integrable far_integrable])
  show "slp_partial_psi_inverse tau c f z =
      slp_partial_psi_inverse tau c
        (slp_near_cutoff_amplitude delta c f) z +
      slp_partial_psi_inverse tau c
        (slp_far_cutoff_amplitude delta c f) z"
    apply (subst slp_partial_psi_inverse_eq)
    apply (subst slp_partial_psi_inverse_eq)
    apply (subst slp_partial_psi_inverse_eq)
    apply (subst slp_oscillatory_near_far_split)
    by (rule transform_split)
qed

end

end
