theory Inverse_Schrodinger_Lp_Born_One_Sided_Terminal_HLS
  imports
    Inverse_Schrodinger_Lp_Born_One_Sided_Terminal_Collapse
    Inverse_Schrodinger_Lp_Born_One_Sided_Step_Riesz
begin

section \<open>The terminal weight as the localized HLS representative\<close>

lemma slp_positive_terminal_riesz_weight_eq_localized_riesz:
  assumes fiber_integrable:
    "integrable lborel
      (slp_localized_riesz_integrand R potential output)"
  shows
    "slp_positive_terminal_riesz_weight R potential output =
      ennreal (slp_localized_riesz_potential R potential output)"
proof -
  have rearrange:
    "slp_positive_terminal_riesz_weight R potential output =
      (\<integral>\<^sup>+source.
        ennreal (norm (potential source)) *
          ennreal (slp_localized_cauchy_kernel R (source - output))
        \<partial>lborel)"
    unfolding slp_positive_terminal_riesz_weight_def
  proof (rule nn_integral_cong)
    fix source :: slp_point
    show
      "ennreal (slp_localized_cauchy_kernel R (output - source)) *
          ennreal (norm (potential source)) =
        ennreal (norm (potential source)) *
          ennreal (slp_localized_cauchy_kernel R (source - output))"
      by (simp add: slp_localized_cauchy_kernel_reflect mult.commute)
  qed
  show ?thesis
    using slp_localized_riesz_nn_integral[OF fiber_integrable]
    by (simp only: rearrange)
qed

context aim_planar_riesz_hls
begin

theorem slp_positive_terminal_riesz_weight_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>R p potential. 0 \<le> R \<and> 1 < p \<and> p < 2 \<and>
        aim_complex_lp_on_plane p potential
      \<longrightarrow>
      (AE output in lborel.
        slp_positive_terminal_riesz_weight R potential output =
          ennreal (slp_localized_riesz_potential R potential output)) \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent p)
        (slp_localized_riesz_potential R potential) \<and>
      aim_real_lp_norm (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R potential)
        \<le> C / ((p - 1) * (2 - p)) *
          aim_complex_lp_norm p potential)"
proof -
  obtain C::real where C_positive: "0 < C"
    and C_bound:
      "\<forall>R p potential. 0 \<le> R \<and> 1 < p \<and> p < 2 \<and>
          aim_complex_lp_on_plane p potential
        \<longrightarrow>
        (AE output in lborel.
          integrable lborel
            (slp_localized_riesz_integrand R potential output)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R potential) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (slp_localized_riesz_potential R potential)
          \<le> C / ((p - 1) * (2 - p)) *
            aim_complex_lp_norm p potential"
    using slp_localized_riesz_hls by blast
  have all_terminal:
    "\<forall>R p potential. 0 \<le> R \<and> 1 < p \<and> p < 2 \<and>
        aim_complex_lp_on_plane p potential
      \<longrightarrow>
      (AE output in lborel.
        slp_positive_terminal_riesz_weight R potential output =
          ennreal (slp_localized_riesz_potential R potential output)) \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent p)
        (slp_localized_riesz_potential R potential) \<and>
      aim_real_lp_norm (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R potential)
        \<le> C / ((p - 1) * (2 - p)) *
          aim_complex_lp_norm p potential"
  proof (intro allI impI)
    fix R p :: real and potential :: slp_scalar_field
    assume hypotheses:
      "0 \<le> R \<and> 1 < p \<and> p < 2 \<and>
        aim_complex_lp_on_plane p potential"
    have hls_result:
      "(AE output in lborel.
          integrable lborel
            (slp_localized_riesz_integrand R potential output)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R potential) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (slp_localized_riesz_potential R potential)
          \<le> C / ((p - 1) * (2 - p)) *
            aim_complex_lp_norm p potential"
      using C_bound hypotheses by blast
    have terminal_identity:
      "AE output in lborel.
        slp_positive_terminal_riesz_weight R potential output =
          ennreal (slp_localized_riesz_potential R potential output)"
      using conjunct1[OF hls_result]
    proof eventually_elim
      fix target :: slp_point
      assume fiber_integrable:
        "integrable lborel
          (slp_localized_riesz_integrand R potential target)"
      show
        "slp_positive_terminal_riesz_weight R potential target =
          ennreal (slp_localized_riesz_potential R potential target)"
        by (rule slp_positive_terminal_riesz_weight_eq_localized_riesz[OF
              fiber_integrable])
    qed
    show
      "(AE output in lborel.
          slp_positive_terminal_riesz_weight R potential output =
            ennreal (slp_localized_riesz_potential R potential output)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R potential) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (slp_localized_riesz_potential R potential)
          \<le> C / ((p - 1) * (2 - p)) *
            aim_complex_lp_norm p potential"
      using terminal_identity hls_result by blast
  qed
  show ?thesis
    using C_positive all_terminal by blast
qed

end

end
