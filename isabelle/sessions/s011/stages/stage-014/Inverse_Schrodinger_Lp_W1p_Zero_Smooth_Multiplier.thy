theory Inverse_Schrodinger_Lp_W1p_Zero_Smooth_Multiplier
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Local_Smooth_Multiplier_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Pair_Difference"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Test_W1p_Membership"
begin

section \<open>Zero-Sobolev closure under smooth multiplication\<close>

theorem slp_w1p_zero_pair_on_mult_smooth_bounded:
  assumes exponent_one_le: "1 \<le> p"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and zero_pair: "slp_w1p_zero_pair_on p X u Du"
    and multiplier_smooth: "smooth_on UNIV a"
    and value_bound:
      "\<And>x. x \<in> X \<Longrightarrow> Real_Vector_Spaces.norm (a x) \<le> A"
    and derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (slp_complex_partial_derivative a 0 x) \<le> B0"
    and derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (slp_complex_partial_derivative a 1 x) \<le> B1"
    and A_nonnegative: "0 \<le> A"
    and B0_nonnegative: "0 \<le> B0"
    and B1_nonnegative: "0 \<le> B1"
  shows "slp_w1p_zero_pair_on p X
    (\<lambda>x. a x * u x)
    (\<lambda>x. \<chi> i. a x * Du x $ i +
      u x * slp_complex_partial_derivative a i x)"
proof -
  let ?v = "\<lambda>x. a x * u x"
  let ?Dv = "\<lambda>x. \<chi> i. a x * Du x $ i +
    u x * slp_complex_partial_derivative a i x"
  let ?C = "4 * (9 * A + 4 * B0 + 4 * B1)"
  let ?K = "1 + ?C"
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  have base_pair: "slp_w1p_pair_on p X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have output_pair: "slp_w1p_pair_on p X ?v ?Dv"
    by (rule slp_w1p_pair_on_mult_smooth_bounded[OF
      exponent_one_le X_measurable X_bounded base_pair multiplier_smooth])
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" where
    phi_test: "\<And>n. slp_test_function_on X (phi n)"
    and phi_pair:
      "\<And>n. slp_w1p_pair_on p X (phi n) (slp_classical_gradient (phi n))"
    and source_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  let ?psi = "\<lambda>n x. a x * phi n x"
  let ?e = "\<lambda>n x. phi n x - u x"
  let ?De = "\<lambda>n x. slp_classical_gradient (phi n) x - Du x"
  let ?me = "\<lambda>n x. a x * ?e n x"
  let ?Dme = "\<lambda>n x. \<chi> i. a x * ?De n x $ i +
    ?e n x * slp_complex_partial_derivative a i x"
  have psi_test: "slp_test_function_on X (?psi n)" for n
    by (rule slp_test_function_on_mult_left[OF
      multiplier_smooth phi_test[of n]])
  have psi_pair:
      "slp_w1p_pair_on p X (?psi n) (slp_classical_gradient (?psi n))"
    for n
    by (rule slp_test_function_w1p_pair[OF exponent_positive psi_test])
  have error_pair: "slp_w1p_pair_on p X (?e n) (?De n)" for n
    by (rule slp_w1p_pair_on_diff[OF
      exponent_one_le phi_pair[of n] base_pair])
  have classical_product:
      "slp_classical_gradient (?psi n) =
        (\<lambda>x. \<chi> i. a x * slp_classical_gradient (phi n) x $ i +
          phi n x * slp_complex_partial_derivative a i x)"
    for n
  proof -
    have phi_smooth: "smooth_on UNIV (phi n)"
      using phi_test[of n] unfolding slp_test_function_on_def by blast
    show ?thesis
      by (rule ext)
        (simp add: slp_classical_gradient_def
          slp_complex_partial_derivative_mult[OF
            multiplier_smooth phi_smooth]
          mult.commute)
  qed
  have value_error: "(\<lambda>x. ?psi n x - ?v x) = ?me n" for n
    by (rule ext) (simp add: algebra_simps)
  have gradient_error:
      "(\<lambda>x. slp_classical_gradient (?psi n) x - ?Dv x) = ?Dme n"
    for n
    by (rule ext)
      (simp add: classical_product vec_eq_iff algebra_simps)
  have error_bound:
      "slp_w1p_norm_on p X (?me n) (?Dme n) \<le>
        ?C * slp_w1p_norm_on p X (?e n) (?De n)"
    for n
    by (rule slp_w1p_norm_on_mult_smooth_bounded[OF
      exponent_one_le X_measurable X_bounded error_pair[of n]
      multiplier_smooth value_bound derivative_zero_bound
      derivative_one_bound A_nonnegative B0_nonnegative B1_nonnegative])
  have C_nonnegative: "0 \<le> ?C"
    using A_nonnegative B0_nonnegative B1_nonnegative
    by (intro mult_nonneg_nonneg add_nonneg_nonneg; simp)
  have K_positive: "0 < ?K"
    using C_nonnegative by linarith
  have C_le_K: "?C \<le> ?K"
    by simp
  have cancel_division: "k * (e / k) = e"
    if k_nonzero: "k \<noteq> 0" for k e :: real
  proof -
    have "k * (e / k) = (k * e) / k"
      by (rule times_divide_eq_right)
    also have "... = (e * k) / k"
      by (simp only: mult.commute)
    also have "... = e * (k / k)"
      by (rule sym, rule times_divide_eq_right)
    also have "... = e"
      by (simp only: divide_self[OF k_nonzero] mult.right_neutral)
    finally show ?thesis .
  qed
  have product_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X (\<lambda>x. ?psi n x - ?v x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - ?Dv x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    have scaled_epsilon_positive: "0 < epsilon / ?K"
      by (rule divide_pos_pos[OF epsilon_positive K_positive])
    obtain N where source_small:
        "\<And>n. n \<ge> N \<Longrightarrow>
          slp_w1p_norm_on p X (?e n) (?De n) < epsilon / ?K"
      using source_tail[rule_format, OF scaled_epsilon_positive] by blast
    show "\<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X (\<lambda>x. ?psi n x - ?v x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - ?Dv x) < epsilon"
    proof (rule exI[of _ N], intro allI impI)
      fix n
      assume n_large: "N \<le> n"
      have source_nonnegative:
          "0 \<le> slp_w1p_norm_on p X (?e n) (?De n)"
        unfolding slp_w1p_norm_on_def by (rule powr_ge_zero)
      have coefficient_comparison:
          "?C * slp_w1p_norm_on p X (?e n) (?De n) \<le>
            ?K * slp_w1p_norm_on p X (?e n) (?De n)"
        by (rule mult_right_mono[OF C_le_K source_nonnegative])
      have scaled_small:
          "?K * slp_w1p_norm_on p X (?e n) (?De n) <
            ?K * (epsilon / ?K)"
        by (rule mult_strict_left_mono[OF source_small[OF n_large] K_positive])
      have K_nonzero: "?K \<noteq> 0"
        using K_positive by simp
      have normalized: "?K * (epsilon / ?K) = epsilon"
        by (rule cancel_division[OF K_nonzero])
      show "slp_w1p_norm_on p X (\<lambda>x. ?psi n x - ?v x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - ?Dv x) < epsilon"
        unfolding value_error gradient_error
        using error_bound[of n] coefficient_comparison scaled_small normalized
        by linarith
    qed
  qed
  show ?thesis
    unfolding slp_w1p_zero_pair_on_def
  proof (rule conjI[OF output_pair])
    show "\<exists>psi::nat \<Rightarrow> slp_scalar_field.
        (\<forall>n. slp_test_function_on X (psi n) \<and>
          slp_w1p_pair_on p X (psi n) (slp_classical_gradient (psi n))) \<and>
        (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          slp_w1p_norm_on p X (\<lambda>x. psi n x - ?v x)
            (\<lambda>x. slp_classical_gradient (psi n) x - ?Dv x) < epsilon)"
      by (rule exI[of _ ?psi])
        (use psi_test psi_pair product_tail in blast)
  qed
qed

end
