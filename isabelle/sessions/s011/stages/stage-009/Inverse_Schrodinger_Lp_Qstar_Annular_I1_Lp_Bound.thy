theory Inverse_Schrodinger_Lp_Qstar_Annular_I1_Lp_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_I1_Output_Power"
begin

section \<open>Delta-independent Lp bound for the first annular term\<close>

lemma slp_qstar_annular_I1_scale_root:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and K_nonnegative: "0 \<le> K"
    and F_nonnegative: "0 \<le> F"
  shows
    "(pi * (3 * delta) ^ 2 *
        (((1 / delta) *
          (delta powr (2 / slp_qstar_holder_exponent a - 1) * K * F))
          powr aim_hls_target_exponent a))
        powr (1 / aim_hls_target_exponent a) =
      (9 * pi) powr (1 / aim_hls_target_exponent a) * K * F"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?s = "slp_qstar_holder_exponent a"
  let ?M =
    "(1 / delta) * (delta powr (2 / ?s - 1) * K * F)"
  have q_lower: "1 < ?q"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  have q_positive: "0 < ?q"
    using q_lower by linarith
  have q_nonzero: "?q \<noteq> 0"
    using q_positive by simp
  have inverse_q_nonnegative: "0 \<le> 1 / ?q"
    using q_positive by simp
  have M_nonnegative: "0 \<le> ?M"
    by (intro mult_nonneg_nonneg)
      (use delta_positive K_nonnegative F_nonnegative in simp_all)
  have q_inverse: "?q * (1 / ?q) = 1"
    using q_nonzero by simp
  have volume_factor:
      "pi * (3 * delta) ^ 2 = (9 * pi) * delta ^ 2"
    by (simp add: power2_eq_square algebra_simps)
  have square_as_powr: "delta ^ 2 = delta powr (real 2)"
    using delta_positive by (simp add: powr_realpow)
  have volume_root:
      "(pi * (3 * delta) ^ 2) powr (1 / ?q) =
        (9 * pi) powr (1 / ?q) * delta powr (2 / ?q)"
    unfolding volume_factor
    by (simp add: square_as_powr powr_mult powr_powr algebra_simps)
  have M_power_root: "(?M powr ?q) powr (1 / ?q) = ?M"
    using M_nonnegative q_inverse
    by (simp only: powr_powr q_inverse powr_one)
  have inverse_delta: "1 / delta = delta powr (- 1)"
    using delta_positive
    by (simp add: powr_minus powr_one divide_inverse)
  have M_scale:
      "?M = delta powr (2 / ?s - 2) * K * F"
  proof -
    have exponent_identity:
        "(- 1) + (2 / ?s - 1) = 2 / ?s - 2"
      by linarith
    have
        "?M =
          (delta powr (- 1) *
            delta powr (2 / ?s - 1)) * K * F"
      unfolding inverse_delta by (simp only: mult.assoc)
    also have "... =
        delta powr ((- 1) + (2 / ?s - 1)) * K * F"
      by (simp only: powr_add)
    also have "... = delta powr (2 / ?s - 2) * K * F"
      by (simp only: exponent_identity)
    finally show ?thesis .
  qed
  have scale_balance: "2 / ?q + 2 / ?s = 2"
    by (rule slp_qstar_exponent_relations(6)[OF exponent_lower
          exponent_upper])
  have scale_exponent_zero: "2 / ?q + (2 / ?s - 2) = 0"
    using scale_balance by linarith
  have delta_cancel:
      "delta powr (2 / ?q) * delta powr (2 / ?s - 2) = 1"
  proof -
    have "delta powr (2 / ?q) * delta powr (2 / ?s - 2) =
        delta powr (2 / ?q + (2 / ?s - 2))"
      by (rule powr_add[symmetric])
    also have "... = delta powr 0"
      by (simp only: scale_exponent_zero)
    also have "... = 1"
      using delta_positive by simp
    finally show ?thesis .
  qed
  have product_root:
      "(pi * (3 * delta) ^ 2 * (?M powr ?q)) powr (1 / ?q) =
        (pi * (3 * delta) ^ 2) powr (1 / ?q) *
          (?M powr ?q) powr (1 / ?q)"
    by (rule powr_mult)
  have
      "(pi * (3 * delta) ^ 2 * (?M powr ?q)) powr (1 / ?q) =
        ((9 * pi) powr (1 / ?q) * delta powr (2 / ?q)) * ?M"
    by (simp only: product_root volume_root M_power_root)
  also have "... =
      ((9 * pi) powr (1 / ?q) * delta powr (2 / ?q)) *
        (delta powr (2 / ?s - 2) * K * F)"
    by (simp only: M_scale)
  also have "... =
      (9 * pi) powr (1 / ?q) *
        (delta powr (2 / ?q) * delta powr (2 / ?s - 2)) * K * F"
    by (simp only: mult.assoc)
  also have "... = (9 * pi) powr (1 / ?q) * K * F"
    by (simp only: delta_cancel mult_1)
  finally show ?thesis .
qed

theorem slp_qstar_annular_I1_Lp_bound:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows lp_membership:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (\<lambda>z. (of_real
          (slp_qstar_annular_I1_potential delta f z) :: complex))"
    and root_bound:
      "(integral\<^sup>L lborel
          (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr
            aim_hls_target_exponent a))
          powr (1 / aim_hls_target_exponent a) \<le>
        (9 * pi) powr (1 / aim_hls_target_exponent a) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
              slp_qstar_holder_exponent a))
            powr (1 / slp_qstar_holder_exponent a) *
          (integral\<^sup>L lborel
            (\<lambda>y. norm (f y) powr aim_hls_target_exponent a))
            powr (1 / aim_hls_target_exponent a)"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?s = "slp_qstar_holder_exponent a"
  let ?K =
    "(integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr ?s))
      powr (1 / ?s)"
  let ?F =
    "(integral\<^sup>L lborel (\<lambda>y. norm (f y) powr ?q))
      powr (1 / ?q)"
  let ?A =
    "integral\<^sup>L lborel
      (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q)"
  let ?B =
    "pi * (3 * delta) ^ 2 *
      (((1 / delta) *
        (delta powr (2 / ?s - 1) * ?K * ?F)) powr ?q)"
  have q_lower: "1 < ?q"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  have q_positive: "0 < ?q"
    using q_lower by linarith
  have potential_measurable:
      "slp_qstar_annular_I1_potential delta f
        \<in> borel_measurable lborel"
    by (rule slp_qstar_annular_I1_output_power(2)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have potential_nonnegative:
      "0 \<le> slp_qstar_annular_I1_potential delta f z" for z
    by (rule slp_qstar_annular_I1_envelope(3)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have embedded_measurable:
      "(\<lambda>z. (of_real
          (slp_qstar_annular_I1_potential delta f z) :: complex))
        \<in> borel_measurable lborel"
    using potential_measurable by measurable
  have embedded_power:
      "(\<lambda>z. norm (of_real
          (slp_qstar_annular_I1_potential delta f z) :: complex) powr ?q) =
        (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q)"
    by (rule ext) (simp add: potential_nonnegative)
  have output_power_integrable:
      "integrable lborel
        (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q)"
    by (rule slp_qstar_annular_I1_output_power(3)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  show "aim_complex_lp_on_plane ?q
      (\<lambda>z. (of_real
        (slp_qstar_annular_I1_potential delta f z) :: complex))"
    unfolding aim_complex_lp_on_plane_def
    using embedded_measurable output_power_integrable
    by (simp only: embedded_power)
  have power_bound: "?A \<le> ?B"
    by (rule slp_qstar_annular_I1_output_power(4)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have A_nonnegative: "0 \<le> ?A"
    by (rule integral_nonneg_AE) simp
  have inverse_q_nonnegative: "0 \<le> 1 / ?q"
    using q_positive by simp
  have root_mono: "?A powr (1 / ?q) \<le> ?B powr (1 / ?q)"
    by (rule powr_mono2[OF inverse_q_nonnegative A_nonnegative power_bound])
  have K_nonnegative: "0 \<le> ?K"
    by simp
  have F_nonnegative: "0 \<le> ?F"
    by simp
  have normalized:
      "?B powr (1 / ?q) = (9 * pi) powr (1 / ?q) * ?K * ?F"
    by (rule slp_qstar_annular_I1_scale_root[OF exponent_lower
          exponent_upper delta_positive K_nonnegative F_nonnegative])
  show "?A powr (1 / ?q) \<le>
      (9 * pi) powr (1 / ?q) * ?K * ?F"
    using root_mono normalized by simp
qed

end
