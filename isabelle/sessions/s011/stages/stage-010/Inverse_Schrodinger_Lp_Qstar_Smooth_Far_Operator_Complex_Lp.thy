theory Inverse_Schrodinger_Lp_Qstar_Smooth_Far_Operator_Complex_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Positive_Tau_Inverse_Scalar_Complex_Lp"
begin

section \<open>Complex Lp assembly of the smooth far operator\<close>

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_qstar_smooth_far_operator_complex_Lp:
  assumes exponent_one_le: "1 \<le> p"
    and tau_positive: "0 < tau"
    and delta_positive: "0 < delta"
    and f_test: "slp_test_function_on UNIV f"
    and amplitude_lp: "aim_complex_lp_on_plane p f"
    and derivative_output_lp:
      "aim_complex_lp_on_plane p
        (slp_partial_psi_inverse tau c
          (slp_classical_wirtinger_partial
            (slp_global_cutoff.slp_far_product delta c f)))"
  shows far_output_lp:
      "aim_complex_lp_on_plane p
        (slp_partial_psi_inverse tau c
          (slp_global_far_cutoff_amplitude delta c f))"
    and far_output_norm:
      "aim_complex_lp_norm p
          (slp_partial_psi_inverse tau c
            (slp_global_far_cutoff_amplitude delta c f)) \<le>
        (1 / tau) *
          (4 *
            ((2 / delta) * aim_complex_lp_norm p f +
              aim_complex_lp_norm p
                (slp_partial_psi_inverse tau c
                  (slp_classical_wirtinger_partial
                    (slp_global_cutoff.slp_far_product delta c f)))))"
proof -
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  let ?value = "\<lambda>x. slp_center_kernel tau c x *
    slp_global_cutoff.slp_far_product delta c f x"
  let ?derivative = "slp_partial_psi_inverse tau c
    (slp_classical_wirtinger_partial
      (slp_global_cutoff.slp_far_product delta c f))"
  let ?bracket = "\<lambda>x. ?value x - ?derivative x"
  let ?scaled = "\<lambda>x. (1 / (\<i> * of_real tau)) * ?bracket x"
  note value_data = slp_qstar_smooth_far_product_complex_Lp[
      OF exponent_positive delta_positive amplitude_lp]
  note difference_data = slp_complex_lp_diff_norm_coarse_triangle[
      OF exponent_one_le value_data(3) derivative_output_lp]
  note scaled_data = slp_positive_tau_inverse_scalar_complex_Lp[
      OF exponent_positive tau_positive difference_data(1)]
  have operator_eq:
      "slp_partial_psi_inverse tau c
          (slp_global_far_cutoff_amplitude delta c f) = ?scaled"
  proof (rule ext)
    fix z :: slp_point
    show "slp_partial_psi_inverse tau c
          (slp_global_far_cutoff_amplitude delta c f) z = ?scaled z"
      by (rule slp_qstar_smooth_far_ibp[OF tau_positive delta_positive
            f_test])
  qed
  show far_output_lp:
      "aim_complex_lp_on_plane p
        (slp_partial_psi_inverse tau c
          (slp_global_far_cutoff_amplitude delta c f))"
    unfolding operator_eq
    by (rule scaled_data(1))
  have sum_bound:
      "aim_complex_lp_norm p ?value + aim_complex_lp_norm p ?derivative \<le>
        (2 / delta) * aim_complex_lp_norm p f +
          aim_complex_lp_norm p ?derivative"
    by (rule add_right_mono[OF value_data(4)])
  have four_sum_bound:
      "4 * (aim_complex_lp_norm p ?value +
          aim_complex_lp_norm p ?derivative) \<le>
        4 * ((2 / delta) * aim_complex_lp_norm p f +
          aim_complex_lp_norm p ?derivative)"
    by (rule mult_left_mono[OF sum_bound]) simp
  have bracket_bound:
      "aim_complex_lp_norm p ?bracket \<le>
        4 * ((2 / delta) * aim_complex_lp_norm p f +
          aim_complex_lp_norm p ?derivative)"
    by (rule order_trans[OF difference_data(2) four_sum_bound])
  have scaled_bracket_bound:
      "(1 / tau) * aim_complex_lp_norm p ?bracket \<le>
        (1 / tau) *
          (4 * ((2 / delta) * aim_complex_lp_norm p f +
            aim_complex_lp_norm p ?derivative))"
    by (rule mult_left_mono[OF bracket_bound])
      (use tau_positive in simp)
  have final_bound:
      "aim_complex_lp_norm p ?scaled \<le>
        (1 / tau) *
          (4 * ((2 / delta) * aim_complex_lp_norm p f +
            aim_complex_lp_norm p ?derivative))"
    by (rule order_trans[OF scaled_data(2) scaled_bracket_bound])
  show far_output_norm:
      "aim_complex_lp_norm p
          (slp_partial_psi_inverse tau c
            (slp_global_far_cutoff_amplitude delta c f)) \<le>
        (1 / tau) *
          (4 *
            ((2 / delta) * aim_complex_lp_norm p f +
              aim_complex_lp_norm p ?derivative))"
    unfolding operator_eq
    by (rule final_bound)
qed

end

end
