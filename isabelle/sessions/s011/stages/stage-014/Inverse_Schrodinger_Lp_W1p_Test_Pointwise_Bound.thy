theory Inverse_Schrodinger_Lp_W1p_Test_Pointwise_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Cauchy_Bounded_Support_Pointwise"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Test_Sobolev_Gain"
begin

section \<open>Compact-smooth pointwise control in the reviewed Sobolev norm\<close>

theorem slp_test_function_wirtinger_partial_lp_w1p_bound:
  assumes exponent_one_le: "1 \<le> p"
    and f_test: "slp_test_function_on X f"
    and f_pair:
      "slp_w1p_pair_on p X f (slp_classical_gradient f)"
  shows
    "aim_complex_lp_on_plane p (slp_classical_wirtinger_partial f) \<and>
      aim_complex_lp_norm p (slp_classical_wirtinger_partial f) \<le>
        4 * slp_w1p_norm_on p X f (slp_classical_gradient f)"
proof -
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  have gradient_zero:
      "(\<lambda>x. slp_classical_gradient f x $ 0) =
        slp_complex_partial_derivative f 0"
    by (rule ext) (simp add: slp_classical_gradient_def)
  have gradient_one:
      "(\<lambda>x. slp_classical_gradient f x $ 1) =
        slp_complex_partial_derivative f 1"
    by (rule ext) (simp add: slp_classical_gradient_def)
  have derivative_zero_restriction:
      "slp_restrict_field X
          (\<lambda>x. slp_classical_gradient f x $ 0) =
        slp_complex_partial_derivative f 0"
    unfolding gradient_zero
    by (rule slp_test_function_partial_restrict_field_eq[OF f_test])
  have derivative_one_restriction:
      "slp_restrict_field X
          (\<lambda>x. slp_classical_gradient f x $ 1) =
        slp_complex_partial_derivative f 1"
    unfolding gradient_one
    by (rule slp_test_function_partial_restrict_field_eq[OF f_test])
  note components = slp_w1p_norm_on_component_bounds[
    OF exponent_positive f_pair]
  have derivative_zero_lp:
      "aim_complex_lp_on_plane p (slp_complex_partial_derivative f 0)"
    using components(2) unfolding derivative_zero_restriction by blast
  have derivative_one_lp:
      "aim_complex_lp_on_plane p (slp_complex_partial_derivative f 1)"
    using components(3) unfolding derivative_one_restriction by blast
  have derivative_zero_bound:
      "aim_complex_lp_norm p (slp_complex_partial_derivative f 0) \<le>
        slp_w1p_norm_on p X f (slp_classical_gradient f)"
    using components(2) unfolding derivative_zero_restriction by blast
  have derivative_one_bound:
      "aim_complex_lp_norm p (slp_complex_partial_derivative f 1) \<le>
        slp_w1p_norm_on p X f (slp_classical_gradient f)"
    using components(3) unfolding derivative_one_restriction by blast
  note partial = slp_classical_wirtinger_partial_lp_coordinate_bound[
    OF exponent_one_le derivative_zero_lp derivative_one_lp]
  have coordinate_sum_bound:
      "aim_complex_lp_norm p (slp_complex_partial_derivative f 0) +
          aim_complex_lp_norm p (slp_complex_partial_derivative f 1)
        \<le> slp_w1p_norm_on p X f (slp_classical_gradient f) +
          slp_w1p_norm_on p X f (slp_classical_gradient f)"
    by (rule add_mono[OF derivative_zero_bound derivative_one_bound])
  have partial_bound:
      "aim_complex_lp_norm p (slp_classical_wirtinger_partial f) \<le>
        4 * slp_w1p_norm_on p X f (slp_classical_gradient f)"
  proof (rule order_trans[OF partial(2)])
    have scaled_coordinate_sum_bound:
        "2 * (aim_complex_lp_norm p
              (slp_complex_partial_derivative f 0) +
            aim_complex_lp_norm p
              (slp_complex_partial_derivative f 1))
          \<le> 2 *
            (slp_w1p_norm_on p X f (slp_classical_gradient f) +
              slp_w1p_norm_on p X f (slp_classical_gradient f))"
      by (rule mult_left_mono[OF coordinate_sum_bound]) simp
    show "2 * (aim_complex_lp_norm p
            (slp_complex_partial_derivative f 0) +
          aim_complex_lp_norm p
            (slp_complex_partial_derivative f 1))
        \<le> 4 * slp_w1p_norm_on p X f (slp_classical_gradient f)"
      using scaled_coordinate_sum_bound by simp
  qed
  show ?thesis
    by (rule conjI[OF partial(1) partial_bound])
qed

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_test_function_w1p_pointwise_bound_on_bounded_set:
  fixes b A :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    and output_in: "z \<in> X"
    and f_test: "slp_test_function_on X f"
    and f_pair:
      "slp_w1p_pair_on b X f (slp_classical_gradient f)"
  defines "q \<equiv> slp_holder_conjugate b"
  shows
    "norm (f z) \<le>
      (norm (inverse (of_real pi :: complex)) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
            powr (1 / q)) *
        (4 * slp_w1p_norm_on b X f (slp_classical_gradient f))"
proof -
  have exponent_one_le: "1 \<le> b"
    using exponent_above_two by linarith
  have partial_lp:
      "aim_complex_lp_on_plane b (slp_classical_wirtinger_partial f)"
    and partial_norm_bound:
      "aim_complex_lp_norm b (slp_classical_wirtinger_partial f) \<le>
        4 * slp_w1p_norm_on b X f (slp_classical_gradient f)"
    using slp_test_function_wirtinger_partial_lp_w1p_bound[
      OF exponent_one_le f_test f_pair]
    by blast+
  have partial_test:
      "slp_test_function_on X (slp_classical_wirtinger_partial f)"
    by (rule slp_classical_wirtinger_partial_test_function[OF f_test])
  have partial_support:
      "slp_classical_wirtinger_partial f y \<noteq> 0 \<Longrightarrow>
        norm (z - y) \<le> 2 * A" for y
  proof -
    assume partial_nonzero:
        "slp_classical_wirtinger_partial f y \<noteq> 0"
    have support_within:
        "closure {x. slp_classical_wirtinger_partial f x \<noteq> 0} \<subseteq> X"
      using partial_test unfolding slp_test_function_on_def by blast
    have y_in: "y \<in> X"
      using partial_nonzero closure_subset support_within by blast
    have z_bound: "norm z \<le> A"
      by (rule set_radius[OF output_in])
    have y_bound: "norm y \<le> A"
      by (rule set_radius[OF y_in])
    have triangle: "norm (z - y) \<le> norm z + norm y"
      by (rule norm_triangle_ineq4)
    show "norm (z - y) \<le> 2 * A"
      using triangle z_bound y_bound by linarith
  qed
  have doubled_radius_nonnegative: "0 \<le> 2 * A"
    using radius_nonnegative by simp
  note cauchy = slp_cauchy_transform_bounded_support_lp_pointwise[
    OF exponent_above_two doubled_radius_nonnegative partial_lp
      partial_support, where orientation=SLP_Partial_Inverse]
  have f_test_UNIV: "slp_test_function_on UNIV f"
    using f_test unfolding slp_test_function_on_def by blast
  have left_inverse:
      "slp_partial_inverse (slp_classical_wirtinger_partial f) = f"
    by (rule slp_partial_inverse_classical_partial_left_inverse[OF
          f_test_UNIV])
  let ?K = "norm (inverse (of_real pi :: complex)) *
    (integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
        powr (1 / q)"
  have coefficient_nonnegative: "0 \<le> ?K"
    by (rule mult_nonneg_nonneg) simp_all
  have scaled_partial_bound:
      "?K * aim_complex_lp_norm b (slp_classical_wirtinger_partial f) \<le>
        ?K * (4 * slp_w1p_norm_on b X f (slp_classical_gradient f))"
    by (rule mult_left_mono[OF partial_norm_bound coefficient_nonnegative])
  have transform_bound:
      "norm (slp_partial_inverse (slp_classical_wirtinger_partial f) z) \<le>
        ?K * aim_complex_lp_norm b (slp_classical_wirtinger_partial f)"
    unfolding q_def by (rule cauchy[THEN conjunct2])
  have left_inverse_at:
      "slp_partial_inverse (slp_classical_wirtinger_partial f) z = f z"
    by (rule fun_cong[OF left_inverse])
  have final_bound:
      "norm (slp_partial_inverse (slp_classical_wirtinger_partial f) z) \<le>
        ?K * (4 * slp_w1p_norm_on b X f (slp_classical_gradient f))"
    by (rule order_trans[OF transform_bound scaled_partial_bound])
  show ?thesis
    using final_bound by (simp only: left_inverse_at)
qed

end

end
