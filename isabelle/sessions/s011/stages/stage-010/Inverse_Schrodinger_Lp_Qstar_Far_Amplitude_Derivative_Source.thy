theory Inverse_Schrodinger_Lp_Qstar_Far_Amplitude_Derivative_Source
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Complex_Lp_Bounded_Multiplier"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Smooth_Far_Pointwise_Bound"
begin

section \<open>The far amplitude-derivative source\<close>

definition slp_qstar_far_amplitude_derivative_source ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field"
where
  "slp_qstar_far_amplitude_derivative_source delta c f z =
    slp_global_far_coefficient delta c z *
      slp_classical_wirtinger_partial f z"

lemma slp_global_far_coefficient_borel_measurable:
  assumes delta_positive: "0 < delta"
  shows "slp_global_far_coefficient delta c \<in>
    borel_measurable lborel"
proof -
  have coefficient_continuous:
      "continuous_on UNIV (slp_global_far_coefficient delta c)"
    by (rule smooth_on_imp_continuous_on[OF
          slp_global_far_coefficient_smooth[OF delta_positive]])
  show ?thesis
    using borel_measurable_continuous_onI[OF coefficient_continuous]
    by simp
qed

theorem slp_global_far_coefficient_norm_bound:
  assumes delta_positive: "0 < delta"
  shows "norm (slp_global_far_coefficient delta c z) \<le> 2 / delta"
proof (cases "delta \<le> norm (z - c)")
  case True
  show ?thesis
    unfolding slp_global_far_coefficient_def
    by (rule slp_global_cutoff.slp_far_amplitude_coefficient_bound[OF
          delta_positive True])
next
  case False
  have inside: "norm (z - c) \<le> delta"
    using False by simp
  have cutoff_one:
      "slp_global_cutoff.slp_scaled_cutoff delta c z = 1"
    by (rule slp_global_cutoff.slp_scaled_cutoff_inner[OF
          delta_positive inside])
  show ?thesis
    unfolding slp_global_far_coefficient_def
    using delta_positive
    by (simp only: cutoff_one diff_self of_real_0 mult_zero_left
          norm_zero; simp)
qed

theorem slp_qstar_far_amplitude_derivative_source_complex_Lp:
  assumes exponent_positive: "0 < p"
    and delta_positive: "0 < delta"
    and derivative_lp:
      "aim_complex_lp_on_plane p (slp_classical_wirtinger_partial f)"
  shows source_lp:
      "aim_complex_lp_on_plane p
        (slp_qstar_far_amplitude_derivative_source delta c f)"
    and source_norm_bound:
      "aim_complex_lp_norm p
          (slp_qstar_far_amplitude_derivative_source delta c f) \<le>
        (2 / delta) *
          aim_complex_lp_norm p (slp_classical_wirtinger_partial f)"
proof -
  have coefficient_measurable:
      "slp_global_far_coefficient delta c \<in> borel_measurable lborel"
    by (rule slp_global_far_coefficient_borel_measurable[OF
          delta_positive])
  have coefficient_bound:
      "\<And>x. norm (slp_global_far_coefficient delta c x) \<le> 2 / delta"
    by (rule slp_global_far_coefficient_norm_bound[OF delta_positive])
  have bound_nonnegative: "0 \<le> 2 / delta"
    using delta_positive by simp
  have bounded_data:
      "aim_complex_lp_on_plane p
          (\<lambda>x. slp_global_far_coefficient delta c x *
            slp_classical_wirtinger_partial f x) \<and>
        aim_complex_lp_norm p
            (\<lambda>x. slp_global_far_coefficient delta c x *
              slp_classical_wirtinger_partial f x) \<le>
          (2 / delta) *
            aim_complex_lp_norm p (slp_classical_wirtinger_partial f)"
    using slp_complex_lp_bounded_multiplier[OF exponent_positive
        coefficient_measurable coefficient_bound bound_nonnegative
        derivative_lp] by blast
  show "aim_complex_lp_on_plane p
      (slp_qstar_far_amplitude_derivative_source delta c f)"
    using bounded_data
    unfolding slp_qstar_far_amplitude_derivative_source_def by blast
  show "aim_complex_lp_norm p
        (slp_qstar_far_amplitude_derivative_source delta c f) \<le>
      (2 / delta) *
        aim_complex_lp_norm p (slp_classical_wirtinger_partial f)"
    using bounded_data
    unfolding slp_qstar_far_amplitude_derivative_source_def by blast
qed

end
