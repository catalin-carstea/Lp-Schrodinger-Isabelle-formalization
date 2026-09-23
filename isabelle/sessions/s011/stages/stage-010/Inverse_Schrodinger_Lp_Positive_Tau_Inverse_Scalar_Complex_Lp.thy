theory Inverse_Schrodinger_Lp_Positive_Tau_Inverse_Scalar_Complex_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Smooth_Far_Product_Complex_Lp"
begin

section \<open>Complex Lp scaling by the positive-frequency inverse scalar\<close>

theorem slp_positive_tau_inverse_scalar_complex_Lp:
  assumes exponent_positive: "0 < p"
    and tau_positive: "0 < tau"
    and function_lp: "aim_complex_lp_on_plane p f"
  shows scaled_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. (1 / (\<i> * of_real tau)) * f x)"
    and scaled_norm_bound:
      "aim_complex_lp_norm p
          (\<lambda>x. (1 / (\<i> * of_real tau)) * f x) \<le>
        (1 / tau) * aim_complex_lp_norm p f"
proof -
  let ?s = "(1 / (\<i> * of_real tau) :: complex)"
  have scalar_norm: "norm ?s = 1 / tau"
    using tau_positive
    by (simp only: norm_divide norm_one norm_mult norm_ii norm_of_real
          abs_of_pos)
  have multiplier_measurable:
      "(\<lambda>_ :: slp_point. ?s) \<in> borel_measurable lborel"
    by measurable
  have multiplier_bound: "\<And>x :: slp_point. norm ?s \<le> 1 / tau"
    unfolding scalar_norm by (rule order_refl)
  have bound_nonnegative: "0 \<le> 1 / tau"
    using tau_positive by simp
  note scaled_data = slp_complex_lp_bounded_multiplier[
      OF exponent_positive multiplier_measurable multiplier_bound
        bound_nonnegative function_lp]
  show scaled_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. ?s * f x)"
    by (rule scaled_data(1))
  show scaled_norm_bound:
      "aim_complex_lp_norm p (\<lambda>x. ?s * f x) \<le>
        (1 / tau) * aim_complex_lp_norm p f"
    by (rule scaled_data(2))
qed

end
