theory Inverse_Schrodinger_Lp_W1p_Wirtinger_Coordinate_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Smooth_Sobolev_HLS"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Complex_Lp_Coarse_Triangle"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Cartesian-to-Wirtinger coordinate norm comparison\<close>

theorem slp_classical_wirtinger_partial_lp_coordinate_bound:
  fixes f :: slp_scalar_field
  assumes exponent_one_le: "1 \<le> p"
    and component_zero_lp:
      "aim_complex_lp_on_plane p (slp_complex_partial_derivative f 0)"
    and component_one_lp:
      "aim_complex_lp_on_plane p (slp_complex_partial_derivative f 1)"
  shows partial_lp:
      "aim_complex_lp_on_plane p (slp_classical_wirtinger_partial f)"
    and partial_norm_bound:
      "aim_complex_lp_norm p (slp_classical_wirtinger_partial f) \<le>
        2 *
          (aim_complex_lp_norm p (slp_complex_partial_derivative f 0) +
            aim_complex_lp_norm p (slp_complex_partial_derivative f 1))"
proof -
  let ?d0 = "slp_complex_partial_derivative f 0"
  let ?d1 = "slp_complex_partial_derivative f 1"
  let ?rotated = "\<lambda>x. (- \<i>) * ?d1 x"
  let ?sum = "\<lambda>x. ?d0 x + ?rotated x"
  let ?halved = "\<lambda>x. (of_real (1 / 2) :: complex) * ?sum x"
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  note rotated = slp_complex_lp_bounded_multiplier[
      where p = p and multiplier = "\<lambda>_::slp_point. - \<i>"
        and C = 1 and f = ?d1,
      OF exponent_positive _ _ _ component_one_lp]
  have rotated_measurable:
      "(\<lambda>_::slp_point. - \<i>) \<in> borel_measurable lborel"
    by measurable
  have rotated_bound: "\<And>x::slp_point. norm (- \<i>) \<le> (1::real)"
    by simp
  have rotated_nonnegative: "0 \<le> (1::real)"
    by simp
  note rotated_data = rotated[OF rotated_measurable rotated_bound
      rotated_nonnegative]
  note summed = slp_complex_lp_add_norm_coarse_triangle[OF exponent_one_le
      component_zero_lp rotated_data(1)]
  have half_measurable:
      "(\<lambda>_::slp_point. (of_real (1 / 2) :: complex))
        \<in> borel_measurable lborel"
    by measurable
  have half_bound:
      "\<And>x::slp_point. norm (of_real (1 / 2) :: complex) \<le> (1 / 2::real)"
    by simp
  have half_nonnegative: "0 \<le> (1 / 2::real)"
    by simp
  note halved = slp_complex_lp_bounded_multiplier[
      where p = p
        and multiplier = "\<lambda>_::slp_point. (of_real (1 / 2) :: complex)"
        and C = "1 / 2" and f = ?sum,
      OF exponent_positive half_measurable half_bound half_nonnegative
        summed(1)]
  have presentation: "?halved = slp_classical_wirtinger_partial f"
  proof (rule ext)
    fix x :: slp_point
    show "?halved x = slp_classical_wirtinger_partial f x"
      unfolding slp_classical_wirtinger_partial_def
      by (simp add: field_simps)
  qed
  show "aim_complex_lp_on_plane p (slp_classical_wirtinger_partial f)"
    unfolding presentation[symmetric] by (rule halved(1))
  have rotated_norm_bound:
      "aim_complex_lp_norm p ?rotated \<le>
        aim_complex_lp_norm p ?d1"
    using rotated_data(2) by simp
  have sum_norm_bound:
      "aim_complex_lp_norm p ?sum \<le>
        4 * (aim_complex_lp_norm p ?d0 + aim_complex_lp_norm p ?d1)"
  proof (rule order_trans[OF summed(2)])
    show "4 * (aim_complex_lp_norm p ?d0 +
          aim_complex_lp_norm p ?rotated) \<le>
        4 * (aim_complex_lp_norm p ?d0 + aim_complex_lp_norm p ?d1)"
      by (intro mult_left_mono add_left_mono rotated_norm_bound) simp
  qed
  have halved_norm_bound:
      "aim_complex_lp_norm p ?halved \<le>
        (1 / 2) * aim_complex_lp_norm p ?sum"
    using halved(2) by simp
  have scaled_sum_bound:
      "(1 / 2) * aim_complex_lp_norm p ?sum \<le>
        (1 / 2) *
          (4 * (aim_complex_lp_norm p ?d0 + aim_complex_lp_norm p ?d1))"
    by (rule mult_left_mono[OF sum_norm_bound]) simp
  show "aim_complex_lp_norm p (slp_classical_wirtinger_partial f) \<le>
      2 *
        (aim_complex_lp_norm p (slp_complex_partial_derivative f 0) +
          aim_complex_lp_norm p (slp_complex_partial_derivative f 1))"
    unfolding presentation[symmetric]
    using order_trans[OF halved_norm_bound scaled_sum_bound] by simp
qed

end
