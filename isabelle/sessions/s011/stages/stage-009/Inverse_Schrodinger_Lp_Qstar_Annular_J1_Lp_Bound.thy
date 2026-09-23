theory Inverse_Schrodinger_Lp_Qstar_Annular_J1_Lp_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_J1_Envelope"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Convolution_L1_Power_Normalized"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Endpoint Young bound for the near-output square term\<close>

theorem slp_qstar_localized_convolution_Young:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows convolution_measurable:
      "slp_real_convolution (slp_localized_cauchy_kernel delta)
        (\<lambda>y. norm (f y)) \<in> borel_measurable lborel"
    and convolution_nonnegative:
      "0 \<le> slp_real_convolution (slp_localized_cauchy_kernel delta)
        (\<lambda>y. norm (f y)) z"
    and convolution_power_integrable:
      "integrable lborel
        (\<lambda>z. slp_real_convolution
          (slp_localized_cauchy_kernel delta)
          (\<lambda>y. norm (f y)) z powr aim_hls_target_exponent a)"
    and convolution_power_bound:
      "integral\<^sup>L lborel
          (\<lambda>z. slp_real_convolution
            (slp_localized_cauchy_kernel delta)
            (\<lambda>y. norm (f y)) z powr aim_hls_target_exponent a) \<le>
        (integral\<^sup>L lborel
          (slp_localized_cauchy_kernel delta)) powr
            aim_hls_target_exponent a *
        integral\<^sup>L lborel
          (\<lambda>y. norm (f y) powr aim_hls_target_exponent a)"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?s = "slp_qstar_holder_exponent a"
  let ?kernel = "slp_localized_cauchy_kernel delta"
  let ?amplitude = "\<lambda>y. norm (f y)"
  let ?H = "slp_real_convolution ?kernel ?amplitude"
  have q_lower: "1 < ?q"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  have s_lower: "1 < ?s"
    by (rule slp_qstar_exponent_relations(2)[OF exponent_lower
          exponent_upper])
  have conjugate: "1 / ?q + 1 / ?s = 1"
    by (rule slp_qstar_exponent_relations(4)[OF exponent_lower
          exponent_upper])
  have amplitude_measurable: "f \<in> borel_measurable lborel"
    and amplitude_power_integrable:
      "integrable lborel (\<lambda>y. norm (f y) powr ?q)"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast+
  have kernel_measurable: "?kernel \<in> borel_measurable lborel"
    by (rule slp_localized_cauchy_kernel_borel_measurable)
  have amplitude_norm_measurable:
      "?amplitude \<in> borel_measurable lborel"
    using amplitude_measurable by measurable
  have kernel_nonnegative: "0 \<le> ?kernel x" for x
    by (rule slp_localized_cauchy_kernel_nonnegative)
  have amplitude_nonnegative: "0 \<le> ?amplitude x" for x
    by (rule norm_ge_zero)
  have kernel_integrable: "integrable lborel ?kernel"
    by (rule slp_localized_cauchy_kernel_integrable)
  note young = slp_positive_convolution_L1_power_bound_normalized[OF
      q_lower s_lower conjugate kernel_measurable amplitude_norm_measurable
      kernel_nonnegative amplitude_nonnegative kernel_integrable
      amplitude_power_integrable]
  show "?H \<in> borel_measurable lborel"
    unfolding slp_real_convolution_def
    using kernel_measurable amplitude_norm_measurable by measurable
  show "0 \<le> ?H z"
    unfolding slp_real_convolution_def
    by (rule integral_nonneg_AE)
      (rule AE_I2, simp add: kernel_nonnegative amplitude_nonnegative)
  show "integrable lborel (\<lambda>z. ?H z powr ?q)"
    unfolding slp_real_convolution_def by (rule young(1))
  show "integral\<^sup>L lborel (\<lambda>z. ?H z powr ?q) \<le>
      (integral\<^sup>L lborel ?kernel) powr ?q *
        integral\<^sup>L lborel (\<lambda>y. ?amplitude y powr ?q)"
    unfolding slp_real_convolution_def by (rule young(2))
qed

theorem slp_qstar_annular_J1_Lp_bound:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows lp_membership:
      "aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_J1_potential delta R f)"
    and norm_bound:
      "aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_J1_potential delta R f) \<le>
        (1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?J = "slp_qstar_annular_J1_potential delta R f"
  let ?H =
    "slp_real_convolution (slp_localized_cauchy_kernel delta)
      (\<lambda>y. norm (f y))"
  let ?S = "1 / delta ^ 2"
  let ?M = "integral\<^sup>L lborel (slp_localized_cauchy_kernel delta)"
  let ?F = "integral\<^sup>L lborel (\<lambda>y. norm (f y) powr ?q)"
  have q_above_two: "2 < ?q"
    by (rule slp_qstar_exponent_relations(1)[OF exponent_lower
          exponent_upper])
  have q_positive: "0 < ?q"
    using q_above_two by linarith
  have q_nonzero: "?q \<noteq> 0"
    using q_positive by simp
  have inverse_q_nonnegative: "0 \<le> 1 / ?q"
    using q_positive by simp
  have amplitude_measurable: "f \<in> borel_measurable lborel"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
  have J_measurable: "?J \<in> borel_measurable lborel"
    unfolding slp_qstar_annular_J1_potential_def
      slp_qstar_annular_J1_integrand_def
      slp_annular_J1_full_integrand_def
    using amplitude_measurable by measurable
  have J_nonnegative: "0 \<le> ?J z" for z
    by (rule slp_qstar_annular_J1_envelope(2)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have J_to_H: "?J z \<le> ?S * ?H z" for z
    by (rule slp_qstar_annular_J1_envelope(3)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have H_measurable: "?H \<in> borel_measurable lborel"
    by (rule slp_qstar_localized_convolution_Young(1)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have H_nonnegative: "0 \<le> ?H z" for z
    by (rule slp_qstar_localized_convolution_Young(2)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have H_power_integrable: "integrable lborel (\<lambda>z. ?H z powr ?q)"
    by (rule slp_qstar_localized_convolution_Young(3)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have H_power_bound:
      "integral\<^sup>L lborel (\<lambda>z. ?H z powr ?q) \<le>
        ?M powr ?q * ?F"
    by (rule slp_qstar_localized_convolution_Young(4)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have S_nonnegative: "0 \<le> ?S"
    using delta_positive by simp
  have S_power_nonnegative: "0 \<le> ?S powr ?q"
    by simp
  have scaled_H_power_integrable:
      "integrable lborel (\<lambda>z. ?S powr ?q * (?H z powr ?q))"
    using H_power_integrable by (rule integrable_mult_right)
  have J_power_measurable:
      "(\<lambda>z. ?J z powr ?q) \<in> borel_measurable lborel"
    using J_measurable by measurable
  have J_power_pointwise:
      "?J z powr ?q \<le> ?S powr ?q * (?H z powr ?q)" for z
  proof -
    have scaled_nonnegative: "0 \<le> ?S * ?H z"
      by (intro mult_nonneg_nonneg S_nonnegative H_nonnegative)
    have powered: "?J z powr ?q \<le> (?S * ?H z) powr ?q"
      by (rule powr_mono2[OF less_imp_le[OF q_positive]
            J_nonnegative J_to_H])
    show ?thesis
      using powered by (simp only: powr_mult)
  qed
  have J_power_integrable: "integrable lborel (\<lambda>z. ?J z powr ?q)"
  proof (rule Bochner_Integration.integrable_bound[OF
        scaled_H_power_integrable J_power_measurable])
    show "AE z in lborel.
        norm (?J z powr ?q) \<le>
          norm (?S powr ?q * (?H z powr ?q))"
    proof (rule AE_I2)
      fix z :: slp_point
      show "norm (?J z powr ?q) \<le>
          norm (?S powr ?q * (?H z powr ?q))"
        using J_power_pointwise[of z] by simp
    qed
  qed
  have integral_to_H:
      "integral\<^sup>L lborel (\<lambda>z. ?J z powr ?q) \<le>
        ?S powr ?q * integral\<^sup>L lborel (\<lambda>z. ?H z powr ?q)"
  proof -
    have monotone:
        "integral\<^sup>L lborel (\<lambda>z. ?J z powr ?q) \<le>
          integral\<^sup>L lborel
            (\<lambda>z. ?S powr ?q * (?H z powr ?q))"
      by (rule integral_mono[OF J_power_integrable
            scaled_H_power_integrable])
        (use J_power_pointwise in auto)
    have scaled_integral:
        "integral\<^sup>L lborel
            (\<lambda>z. ?S powr ?q * (?H z powr ?q)) =
          ?S powr ?q * integral\<^sup>L lborel (\<lambda>z. ?H z powr ?q)"
      using H_power_integrable by simp
    show ?thesis
      using monotone scaled_integral by simp
  qed
  have power_bound:
      "integral\<^sup>L lborel (\<lambda>z. ?J z powr ?q) \<le>
        ?S powr ?q * (?M powr ?q * ?F)"
  proof -
    have scaled_Young:
        "?S powr ?q * integral\<^sup>L lborel (\<lambda>z. ?H z powr ?q) \<le>
          ?S powr ?q * (?M powr ?q * ?F)"
      by (rule mult_left_mono[OF H_power_bound S_power_nonnegative])
    show ?thesis
      by (rule order_trans[OF integral_to_H scaled_Young])
  qed
  have absolute_power:
      "(\<lambda>z. abs (?J z) powr ?q) = (\<lambda>z. ?J z powr ?q)"
    by (rule ext) (simp add: J_nonnegative)
  show "aim_real_lp_on_plane ?q ?J"
    unfolding aim_real_lp_on_plane_def absolute_power
    using J_measurable J_power_integrable by blast
  have J_mass_nonnegative:
      "0 \<le> integral\<^sup>L lborel (\<lambda>z. ?J z powr ?q)"
    by (rule integral_nonneg_AE) simp
  have root_bound:
      "(integral\<^sup>L lborel (\<lambda>z. ?J z powr ?q)) powr (1 / ?q) \<le>
        (?S powr ?q * (?M powr ?q * ?F)) powr (1 / ?q)"
    by (rule powr_mono2[OF inverse_q_nonnegative J_mass_nonnegative
          power_bound])
  have M_nonnegative: "0 \<le> ?M"
    by (rule integral_nonneg_AE)
      (rule AE_I2, rule slp_localized_cauchy_kernel_nonnegative)
  have F_nonnegative: "0 \<le> ?F"
    by (rule integral_nonneg_AE) simp
  have normalized_root:
      "(?S powr ?q * (?M powr ?q * ?F)) powr (1 / ?q) =
        ?S * ?M * (?F powr (1 / ?q))"
    using q_nonzero S_nonnegative M_nonnegative F_nonnegative
    by (simp add: powr_mult powr_powr)
  have scale_identity:
      "?S * ?M = (1 / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (rule slp_localized_cauchy_kernel_integral_delta_square_normalized[OF
          delta_positive])
  have scaled_root:
      "?S * ?M * (?F powr (1 / ?q)) =
        (1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
          (?F powr (1 / ?q))"
    by (simp only: scale_identity)
  have source_root_bound:
      "(integral\<^sup>L lborel (\<lambda>z. ?J z powr ?q)) powr (1 / ?q) \<le>
        (1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
          (?F powr (1 / ?q))"
    using root_bound normalized_root scaled_root by simp
  show "aim_real_lp_norm ?q ?J \<le>
      (1 / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
        aim_complex_lp_norm ?q f"
    unfolding aim_real_lp_norm_def aim_complex_lp_norm_def absolute_power
    by (rule source_root_bound)
qed

end
