theory Inverse_Schrodinger_Lp_W1p_Rough_Global_Far_IBP_Center
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Near_Far_Split"
begin

section \<open>Exact center-diagonal rough global-far integration by parts\<close>

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_w1p_zero_pair_partial_psi_inverse_rough_global_far_center:
  fixes p :: real
  assumes tau_positive: "0 < tau"
    and exponent_above_two: "2 < p"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on p X u Du"
  shows
    "slp_partial_psi_inverse tau c
        (slp_global_far_cutoff_amplitude delta c
          (slp_restrict_field X u)) c =
      (1 / (\<i> * of_real tau)) *
        (0 - slp_partial_psi_inverse tau c
          (slp_restrict_field X
            (slp_gradient_wirtinger_partial
              (\<lambda>x. \<chi> i.
                slp_global_far_coefficient delta c x * Du x $ i +
                u x * slp_complex_partial_derivative
                  (slp_global_far_coefficient delta c) i x))) c)"
proof -
  let ?a = "slp_global_far_coefficient delta c"
  let ?v = "\<lambda>x. ?a x * u x"
  let ?Dv = "\<lambda>x. \<chi> i. ?a x * Du x $ i +
    u x * slp_complex_partial_derivative ?a i x"
  let ?A = "2 / delta"
  let ?B = "slp_global_cutoff_L / delta ^ 2 + 2 / delta ^ 2"
  let ?C = "4 * (9 * ?A + 4 * ?B + 4 * ?B)"
  have exponent_one_le: "1 \<le> p"
    using exponent_above_two by linarith
  have exponent_positive: "0 < p"
    using exponent_above_two by linarith
  have base_pair: "slp_w1p_pair_on p X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have multiplier_smooth: "smooth_on UNIV ?a"
    by (rule slp_global_far_coefficient_smooth[OF delta_positive])
  have value_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (?a x) \<le> ?A"
    by (rule slp_global_far_coefficient_norm_bound[OF delta_positive])
  have derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative ?a 0 x) \<le> ?B"
    by (rule slp_global_far_coefficient_partial_norm_bound[OF delta_positive])
  have derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative ?a 1 x) \<le> ?B"
    by (rule slp_global_far_coefficient_partial_norm_bound[OF delta_positive])
  have A_nonnegative: "0 \<le> ?A"
    using delta_positive by simp
  have cutoff_nonnegative: "0 \<le> slp_global_cutoff_L"
    by (rule slp_global_cutoff_profile_spec[THEN conjunct2,
          THEN conjunct2, THEN conjunct1])
  have delta_square_positive: "0 < delta ^ 2"
    using delta_positive by simp
  have cutoff_term_nonnegative:
      "0 \<le> slp_global_cutoff_L / delta ^ 2"
    by (rule divide_nonneg_pos[OF cutoff_nonnegative delta_square_positive])
  have square_term_nonnegative: "0 \<le> 2 / delta ^ 2"
    using delta_positive by simp
  have B_nonnegative: "0 \<le> ?B"
    by (rule add_nonneg_nonneg[OF cutoff_term_nonnegative
          square_term_nonnegative])
  have output_pair: "slp_w1p_pair_on p X ?v ?Dv"
    by (rule slp_w1p_pair_on_mult_smooth_bounded[OF
          exponent_one_le X_measurable X_bounded base_pair
          multiplier_smooth])

  obtain phi :: "nat \<Rightarrow> slp_scalar_field" where
    phi_test: "\<And>n. slp_test_function_on X (phi n)"
    and phi_pair:
      "\<And>n. slp_w1p_pair_on p X (phi n)
        (slp_classical_gradient (phi n))"
    and source_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  let ?psi = "\<lambda>n x. ?a x * phi n x"
  let ?e = "\<lambda>n x. phi n x - u x"
  let ?De = "\<lambda>n x. slp_classical_gradient (phi n) x - Du x"
  let ?me = "\<lambda>n x. ?a x * ?e n x"
  let ?Dme = "\<lambda>n x. \<chi> i. ?a x * ?De n x $ i +
    ?e n x * slp_complex_partial_derivative ?a i x"
  let ?W = "\<lambda>n. slp_w1p_norm_on p X (?e n) (?De n)"
  let ?N = "\<lambda>n. slp_w1p_norm_on p X
    (\<lambda>x. ?psi n x - ?v x)
    (\<lambda>x. slp_classical_gradient (?psi n) x - ?Dv x)"
  have psi_test: "slp_test_function_on X (?psi n)" for n
    by (rule slp_test_function_on_mult_left[OF
          multiplier_smooth phi_test[of n]])
  have psi_pair:
      "slp_w1p_pair_on p X (?psi n)
        (slp_classical_gradient (?psi n))" for n
    by (rule slp_test_function_w1p_pair[OF exponent_positive psi_test])
  have error_pairs:
      "slp_w1p_pair_on p X
        (\<lambda>x. ?psi n x - ?v x)
        (\<lambda>x. slp_classical_gradient (?psi n) x - ?Dv x)" for n
    by (rule slp_w1p_pair_on_diff[OF
          exponent_one_le psi_pair output_pair])
  have base_error_pair: "slp_w1p_pair_on p X (?e n) (?De n)" for n
    by (rule slp_w1p_pair_on_diff[OF
          exponent_one_le phi_pair[of n] base_pair])
  have classical_product:
      "slp_classical_gradient (?psi n) =
        (\<lambda>x. \<chi> i.
          ?a x * slp_classical_gradient (phi n) x $ i +
          phi n x * slp_complex_partial_derivative ?a i x)" for n
  proof -
    have phi_smooth: "smooth_on UNIV (phi n)"
      using phi_test[of n] unfolding slp_test_function_on_def by blast
    have derivative_product:
        "slp_complex_partial_derivative
            (\<lambda>y. ?a y * phi n y) i x =
          ?a x * slp_complex_partial_derivative (phi n) i x +
            phi n x * slp_complex_partial_derivative ?a i x" for i x
      using slp_complex_partial_derivative_mult[
        OF multiplier_smooth phi_smooth, of i x]
      by (simp only: mult.commute)
    show ?thesis
      by (rule ext)
        (simp only: slp_classical_gradient_def derivative_product
          vec_lambda_beta)
  qed
  have value_error: "(\<lambda>x. ?psi n x - ?v x) = ?me n" for n
    by (rule ext) (simp add: algebra_simps)
  have gradient_error:
      "(\<lambda>x. slp_classical_gradient (?psi n) x - ?Dv x) =
        ?Dme n" for n
  proof (rule ext)
    fix x :: slp_point
    have product_at:
        "slp_classical_gradient (?psi n) x =
          (\<chi> i.
            ?a x * slp_classical_gradient (phi n) x $ i +
            phi n x * slp_complex_partial_derivative ?a i x)"
      using fun_cong[OF classical_product[of n], of x] .
    show "slp_classical_gradient (?psi n) x - ?Dv x = ?Dme n x"
      apply (subst product_at)
      by (simp add: vec_eq_iff algebra_simps)
  qed
  have error_bound:
      "slp_w1p_norm_on p X (?me n) (?Dme n) \<le> ?C * ?W n" for n
    by (rule slp_w1p_norm_on_mult_smooth_bounded[OF
          exponent_one_le X_measurable X_bounded base_error_pair[of n]
          multiplier_smooth value_bound derivative_zero_bound
          derivative_one_bound A_nonnegative B_nonnegative B_nonnegative])
  have N_bound: "?N n \<le> ?C * ?W n" for n
    unfolding value_error gradient_error by (rule error_bound)
  have tail_limit: "(G \<longlongrightarrow> 0) sequentially"
    if nonnegative: "\<And>n. 0 \<le> G n"
      and tails: "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N. G n < epsilon"
    for G :: "nat \<Rightarrow> real"
  proof (rule metric_LIMSEQ_I)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail: "\<forall>n\<ge>N. G n < epsilon"
      using tails epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N. dist (G n) 0 < epsilon"
      by (rule exI[of _ N]) (use tail nonnegative in auto)
  qed
  have W_nonnegative: "0 \<le> ?W n" for n
    unfolding slp_w1p_norm_on_def by simp
  have W_tends: "(?W \<longlongrightarrow> 0) sequentially"
    by (rule tail_limit[OF W_nonnegative source_tail])
  have scaled_tends: "((\<lambda>n. ?C * ?W n) \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const W_tends] by simp
  have N_nonnegative: "0 \<le> ?N n" for n
    unfolding slp_w1p_norm_on_def by simp
  have error_norm_tends: "(?N \<longlongrightarrow> 0) sequentially"
    by (rule tendsto_sandwich[
          where f = "\<lambda>_. 0" and h = "\<lambda>n. ?C * ?W n"])
      (use N_nonnegative N_bound scaled_tends in auto)

  have cutoff_one:
      "slp_global_cutoff.slp_scaled_cutoff delta c c = 1"
    by (rule slp_global_cutoff.slp_scaled_cutoff_inner[OF delta_positive])
      (use delta_positive in simp)
  have coefficient_center: "?a c = 0"
    unfolding slp_global_far_coefficient_def
    by (simp only: cutoff_one diff_self of_real_0 mult_zero_left)
  have psi_center: "?psi n c = 0" for n
    by (simp only: coefficient_center mult_zero_left)
  have v_center: "slp_restrict_field X ?v c = 0"
    by (simp add: slp_restrict_field_def coefficient_center)
  have pointwise_limit:
      "((\<lambda>n. ?psi n c) \<longlongrightarrow>
        slp_restrict_field X ?v c) sequentially"
    by (simp only: psi_center v_center tendsto_const)

  obtain M :: real where M_bound:
      "\<And>y. y \<in> X \<Longrightarrow> Real_Vector_Spaces.norm y \<le> M"
    using X_bounded unfolding bounded_iff by blast
  let ?R = "Real_Vector_Spaces.norm c + max 0 M"
  have radius_nonnegative: "0 \<le> ?R"
    by simp
  have X_radius: "Real_Vector_Spaces.norm (c - y) \<le> ?R"
    if "y \<in> X" for y
  proof -
    have "Real_Vector_Spaces.norm (c - y) \<le>
        Real_Vector_Spaces.norm c + Real_Vector_Spaces.norm y"
      by (rule norm_triangle_ineq4)
    also have "... \<le> Real_Vector_Spaces.norm c + max 0 M"
      using M_bound[OF that] by linarith
    finally show ?thesis .
  qed
  have divided:
      "slp_partial_inverse
          (\<lambda>x. (slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * slp_restrict_field X ?v x) c =
        (1 / (\<i> * of_real tau)) *
          (slp_center_kernel tau c c * slp_restrict_field X ?v c -
            slp_partial_inverse
              (\<lambda>x. slp_center_kernel tau c x *
                slp_restrict_field X
                  (slp_gradient_wirtinger_partial ?Dv) x) c)"
    by (rule
        slp_w1p_partial_inverse_oscillatory_divided_rough_far_product_of_pair[
          OF tau_positive exponent_above_two radius_nonnegative psi_test
            error_pairs error_norm_tends output_pair X_radius
            pointwise_limit])
  have input_eq:
      "(\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * slp_restrict_field X ?v x) =
        slp_oscillatory_modulation tau c
          (slp_global_far_cutoff_amplitude delta c
            (slp_restrict_field X u))"
    by (rule slp_w1p_global_far_modulated_source_eq[OF delta_positive])
  have derivative_input_eq:
      "(\<lambda>x. slp_center_kernel tau c x *
          slp_restrict_field X
            (slp_gradient_wirtinger_partial ?Dv) x) =
        slp_oscillatory_modulation tau c
          (slp_restrict_field X
            (slp_gradient_wirtinger_partial ?Dv))"
    unfolding slp_oscillatory_modulation_def by (rule refl)
  have boundary_zero:
      "slp_center_kernel tau c c * slp_restrict_field X ?v c = 0"
    by (simp only: v_center mult_zero_right)
  have normalized:
      "slp_partial_inverse
          (slp_oscillatory_modulation tau c
            (slp_global_far_cutoff_amplitude delta c
              (slp_restrict_field X u))) c =
        (1 / (\<i> * of_real tau)) *
          (0 - slp_partial_inverse
            (slp_oscillatory_modulation tau c
              (slp_restrict_field X
                (slp_gradient_wirtinger_partial ?Dv))) c)"
    using divided unfolding input_eq derivative_input_eq boundary_zero .
  show ?thesis
    unfolding slp_partial_psi_inverse_def by (rule normalized)
qed

end

end
