theory Inverse_Schrodinger_Lp_Qstar_Near_Cutoff_Amplitude_Complex_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Quantitative_Complex_Lp_Product"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Scaled_Smooth_Cutoff_L2"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Exponent_Arithmetic"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Near_Center_Operator_Bridge"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_HLS"
begin

section \<open>Complex Lp bound for the canonical near cutoff\<close>

theorem slp_qstar_near_cutoff_amplitude_complex_Lp:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows near_lp:
      "aim_complex_lp_on_plane a
        (slp_global_cutoff.slp_near_cutoff_amplitude delta c f)"
    and near_norm:
      "aim_complex_lp_norm a
          (slp_global_cutoff.slp_near_cutoff_amplitude delta c f) \<le>
        (2 * sqrt pi * delta) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?h = "\<lambda>x :: slp_point.
    (of_real (slp_global_scaled_cutoff delta c x) :: complex)"
  have a_positive: "0 < a" and a_nonzero: "a \<noteq> 0"
    using exponent_lower by linarith+
  have q_above_two: "2 < ?q"
    by (rule slp_qstar_exponent_relations(1)[OF exponent_lower
          exponent_upper])
  have q_positive: "0 < ?q" and q_nonzero: "?q \<noteq> 0"
    using q_above_two by linarith+
  have two_scale: "1 < 2 / a"
    apply (rule iffD2[OF pos_less_divide_eq[OF a_positive]])
    using exponent_upper by simp
  have target_scale: "1 < ?q / a"
    apply (rule iffD2[OF pos_less_divide_eq[OF a_positive]])
    using q_above_two exponent_upper by linarith
  have reciprocal:
      "1 / ?q = 1 / a - 1 / 2"
    by (rule slp_hls_target_exponent_reciprocal[OF exponent_lower
          exponent_upper])
  have a_over_q: "a / ?q = 1 - a / 2"
  proof -
    have scaled: "a * (1 / ?q) = a * (1 / a - 1 / 2)"
      using reciprocal by simp
    show ?thesis
      using scaled a_nonzero by (simp add: algebra_simps)
  qed
  have scaled_conjugacy:
      "1 / (2 / a) + 1 / (?q / a) = 1"
  proof -
    have inv_two_scale: "1 / (2 / a) = a / 2"
      by (simp only: divide_divide_eq_right mult.left_neutral)
    have inv_target_scale: "1 / (?q / a) = a / ?q"
      by (simp only: divide_divide_eq_right mult.left_neutral)
    show ?thesis
      unfolding inv_two_scale inv_target_scale a_over_q
      by simp
  qed
  have h_measurable: "?h \<in> borel_measurable lborel"
    by measurable
  have cutoff_power_integrable:
      "integrable lborel (slp_global_scaled_cutoff_power 2 delta c)"
    by (rule slp_global_scaled_cutoff_power_integrable[OF delta_positive])
      simp
  have h_power_integrable:
      "integrable lborel (\<lambda>x. norm (?h x) powr 2)"
    using cutoff_power_integrable
    unfolding slp_global_scaled_cutoff_power_def
    by simp
  have h_lp: "aim_complex_lp_on_plane 2 ?h"
    unfolding aim_complex_lp_on_plane_def
    using h_measurable h_power_integrable by blast
  have h_norm_bound:
      "aim_complex_lp_norm 2 ?h \<le> 2 * sqrt pi * delta"
  proof -
    have cutoff_root:
        "(integral\<^sup>L lborel
            (slp_global_scaled_cutoff_power 2 delta c)) powr (1 / 2) \<le>
          2 * sqrt pi * delta"
      by (rule slp_global_scaled_cutoff_L2_root_le[OF delta_positive])
    show ?thesis
      using cutoff_root
      unfolding aim_complex_lp_norm_def
        slp_global_scaled_cutoff_power_def
      by simp
  qed
  note product_data = slp_aim_complex_lp_on_plane_product_norm_bound[
      OF a_positive two_scale target_scale scaled_conjugacy h_lp amplitude_lp]
  have near_eq:
      "slp_global_cutoff.slp_near_cutoff_amplitude delta c f =
        (\<lambda>x. ?h x * f x)"
    unfolding slp_global_cutoff.slp_near_cutoff_amplitude_def
      slp_global_scaled_cutoff_def
    by (rule refl)
  show near_lp:
      "aim_complex_lp_on_plane a
        (slp_global_cutoff.slp_near_cutoff_amplitude delta c f)"
    unfolding near_eq
    by (rule product_data(1))
  have amplitude_norm_nonnegative:
      "0 \<le> aim_complex_lp_norm ?q f"
    unfolding aim_complex_lp_norm_def by simp
  have product_bound:
      "aim_complex_lp_norm 2 ?h * aim_complex_lp_norm ?q f \<le>
        (2 * sqrt pi * delta) * aim_complex_lp_norm ?q f"
    by (rule mult_right_mono[OF h_norm_bound
          amplitude_norm_nonnegative])
  show near_norm:
      "aim_complex_lp_norm a
          (slp_global_cutoff.slp_near_cutoff_amplitude delta c f) \<le>
        (2 * sqrt pi * delta) * aim_complex_lp_norm ?q f"
    unfolding near_eq
    by (rule order_trans[OF product_data(2) product_bound])
qed

end
