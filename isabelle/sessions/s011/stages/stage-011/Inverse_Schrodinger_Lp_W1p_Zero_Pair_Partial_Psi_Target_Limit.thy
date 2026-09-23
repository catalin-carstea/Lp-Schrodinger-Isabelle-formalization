theory Inverse_Schrodinger_Lp_W1p_Zero_Pair_Partial_Psi_Target_Limit
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Smooth_Qstar_Pairwise_Error"
begin

section \<open>Target-norm convergence to the literal rough partial-qstar output\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_partial_psi_target_limit:
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and X_bounded: "bounded X"
    and zero_pair: "slp_w1p_zero_pair_on a X u Du"
  shows "\<exists>psi :: nat \<Rightarrow> slp_scalar_field.
    (\<forall>n. slp_test_function_on X (psi n) \<and>
      slp_w1p_pair_on a X (psi n) (slp_classical_gradient (psi n))) \<and>
    (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
      slp_w1p_norm_on a X
        (\<lambda>x. psi n x - u x)
        (\<lambda>x. slp_classical_gradient (psi n) x - Du x) < epsilon) \<and>
    (\<forall>tau\<ge>2. \<forall>c.
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c (slp_restrict_field X u)) \<and>
      (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>z. slp_partial_psi_inverse tau c (psi n) z -
            slp_partial_psi_inverse tau c (slp_restrict_field X u) z)
          < epsilon))"
proof -
  obtain psi :: "nat \<Rightarrow> slp_scalar_field" where psi_pairs:
      "\<forall>n. slp_test_function_on X (psi n) \<and>
        slp_w1p_pair_on a X (psi n) (slp_classical_gradient (psi n))"
    and psi_source_converges:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a X
          (\<lambda>x. psi n x - u x)
          (\<lambda>x. slp_classical_gradient (psi n) x - Du x) < epsilon"
    and psi_pointwise:
      "\<forall>tau c z.
        ((\<lambda>n. slp_partial_psi_inverse tau c (psi n) z)
          \<longlongrightarrow> slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) sequentially"
    using slp_w1p_zero_pair_partial_psi_pointwise_limit[
      OF a_lower a_upper X_bounded zero_pair] by blast
  have rough_pair: "slp_w1p_pair_on a X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have rough_source_lp: "aim_complex_lp_on_plane a (slp_restrict_field X u)"
    using slp_w1p_pair_onD(2)[OF rough_pair]
    unfolding slp_complex_lp_on_def .
  have a_positive: "0 < a" using a_lower by linarith
  have target_positive: "0 < aim_hls_target_exponent a"
    using slp_qstar_exponent_relations(1)[OF a_lower a_upper] by linarith
  obtain H::real where H_positive: "0 < H"
    and hls:
      "\<And>p tau c f. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_psi_inverse tau c f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_psi_inverse tau c f)
          \<le> H / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_partial_psi_inverse_hls by blast
  have psi_source_lp: "aim_complex_lp_on_plane a (psi n)" for n
  proof -
    have psi_test_UNIV: "slp_test_function_on UNIV (psi n)"
      using psi_pairs unfolding slp_test_function_on_def by blast
    show ?thesis
      by (rule slp_test_function_aim_complex_lp_on_plane[
            OF a_positive psi_test_UNIV])
  qed
  obtain B::real where B_positive: "0 < B"
    and pairwise_gain:
      "\<And>tau R c f g.
        2 \<le> tau \<Longrightarrow> 1 \<le> R * sqrt tau \<Longrightarrow>
        slp_test_function_on X f \<Longrightarrow>
        slp_w1p_pair_on a X f (slp_classical_gradient f) \<Longrightarrow>
        slp_test_function_on X g \<Longrightarrow>
        slp_w1p_pair_on a X g (slp_classical_gradient g) \<Longrightarrow>
        (\<And>y. f y - g y \<noteq> 0 \<Longrightarrow>
          norm_class.norm (y - c) \<le> R) \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (\<lambda>z. slp_partial_psi_inverse tau c f z -
            slp_partial_psi_inverse tau c g z) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>z. slp_partial_psi_inverse tau c f z -
            slp_partial_psi_inverse tau c g z)
          \<le> B * inverse (sqrt tau) *
            (slp_w1p_norm_on a X
                (\<lambda>x. f x - u x)
                (\<lambda>x. slp_classical_gradient f x - Du x) +
              slp_w1p_norm_on a X
                (\<lambda>x. g x - u x)
                (\<lambda>x. slp_classical_gradient g x - Du x))"
    using slp_test_function_pairwise_error_partial_psi_gain[
      OF a_lower a_upper rough_pair] by blast
  obtain A::real where X_bound:
      "\<And>y. y \<in> X \<Longrightarrow> norm_class.norm y \<le> A"
    using X_bounded unfolding bounded_iff by blast
  have psi_nonzero_in: "psi n y \<noteq> 0 \<Longrightarrow> y \<in> X" for n y
  proof -
    assume nonzero: "psi n y \<noteq> 0"
    have support_within: "closure {x. psi n x \<noteq> 0} \<subseteq> X"
      using psi_pairs unfolding slp_test_function_on_def by blast
    have "y \<in> closure {x. psi n x \<noteq> 0}"
      by (rule subsetD[OF closure_subset]) (use nonzero in simp)
    then show "y \<in> X" by (rule subsetD[OF support_within])
  qed
  let ?E = "\<lambda>n. slp_w1p_norm_on a X
    (\<lambda>x. psi n x - u x)
    (\<lambda>x. slp_classical_gradient (psi n) x - Du x)"
  have output_limit:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c (slp_restrict_field X u)) \<and>
      (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>z. slp_partial_psi_inverse tau c (psi n) z -
            slp_partial_psi_inverse tau c (slp_restrict_field X u) z)
          < epsilon)"
    if tau_lower: "2 \<le> tau" for tau c
  proof -
    let ?F = "\<lambda>n. slp_partial_psi_inverse tau c (psi n)"
    let ?f = "slp_partial_psi_inverse tau c (slp_restrict_field X u)"
    let ?R = "1 + max 0 A + norm_class.norm c"
    let ?L = "B * inverse (sqrt tau)"
    have R_lower: "1 \<le> ?R" by simp
    have R_nonnegative: "0 \<le> ?R" by simp
    have tau_positive: "0 < tau" using tau_lower by linarith
    have sqrt_positive: "0 < sqrt tau" using tau_positive by simp
    have sqrt_lower: "1 \<le> sqrt tau"
      by (rule real_sqrt_ge_one) (use tau_lower in linarith)
    have R_le_product: "?R \<le> ?R * sqrt tau"
      using mult_left_mono[OF sqrt_lower R_nonnegative] by simp
    have normalized: "1 \<le> ?R * sqrt tau"
      by (rule order_trans[OF R_lower R_le_product])
    have L_positive: "0 < ?L"
      using B_positive sqrt_positive by simp
    have support_difference:
        "norm_class.norm (y - c) \<le> ?R"
      if difference_nonzero: "psi m y - psi n y \<noteq> 0" for m n y
    proof -
      have y_in: "y \<in> X"
      proof (cases "psi m y = 0")
        case True
        have n_nonzero: "psi n y \<noteq> 0"
          using difference_nonzero True by simp
        show ?thesis by (rule psi_nonzero_in[OF n_nonzero])
      next
        case False
        show ?thesis by (rule psi_nonzero_in[OF False])
      qed
      have y_bound: "norm_class.norm y \<le> max 0 A"
        using X_bound[OF y_in] by linarith
      have triangle: "norm_class.norm (y - c) \<le>
          norm_class.norm y + norm_class.norm c"
        by (rule norm_triangle_ineq4)
      show ?thesis using triangle y_bound by linarith
    qed
    have pairwise:
        "aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>z. ?F m z - ?F n z) \<le> ?L * (?E m + ?E n)" for m n
      by (rule conjunct2[OF pairwise_gain[OF tau_lower normalized
            conjunct1[OF spec[OF psi_pairs]]
            conjunct2[OF spec[OF psi_pairs]]
            conjunct1[OF spec[OF psi_pairs]]
            conjunct2[OF spec[OF psi_pairs]] support_difference]])
    have output_cauchy:
        "\<forall>epsilon>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
          aim_complex_lp_norm (aim_hls_target_exponent a)
            (\<lambda>z. ?F m z - ?F n z) < epsilon"
    proof (intro allI impI)
      fix epsilon :: real
      assume epsilon_positive: "0 < epsilon"
      let ?delta = "epsilon / (2 * ?L)"
      have two_L_positive: "0 < 2 * ?L" using L_positive by simp
      have delta_positive: "0 < ?delta"
        by (rule divide_pos_pos[OF epsilon_positive two_L_positive])
      obtain N where tail: "\<forall>n\<ge>N. ?E n < ?delta"
        using psi_source_converges delta_positive by blast
      show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
          aim_complex_lp_norm (aim_hls_target_exponent a)
            (\<lambda>z. ?F m z - ?F n z) < epsilon"
      proof (rule exI[of _ N], intro allI impI)
        fix m
        assume m_tail: "N \<le> m"
        fix n
        assume n_tail: "N \<le> n"
        have error_sum: "?E m + ?E n < 2 * ?delta"
        proof -
          have "?E m + ?E n < ?delta + ?delta"
            by (rule add_strict_mono[OF tail[rule_format, OF m_tail]
                  tail[rule_format, OF n_tail]])
          then show ?thesis by simp
        qed
        have scaled_error: "?L * (?E m + ?E n) < ?L * (2 * ?delta)"
          by (rule mult_strict_left_mono[OF error_sum L_positive])
        have factors_nonzero: "B \<noteq> 0 \<and> tau \<noteq> 0"
          using B_positive tau_positive by auto
        have normalization: "?L * (2 * ?delta) = epsilon"
          using factors_nonzero by (simp add: algebra_simps)
        show "aim_complex_lp_norm (aim_hls_target_exponent a)
            (\<lambda>z. ?F m z - ?F n z) < epsilon"
          by (rule le_less_trans[OF pairwise])
            (use scaled_error normalization in simp)
      qed
    qed
    have sequence_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) (?F n)" for n
      by (rule conjunct1[OF hls[OF a_lower a_upper psi_source_lp]])
    have rough_output_lp: "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?f"
      by (rule conjunct1[OF hls[OF a_lower a_upper rough_source_lp]])
    have rough_output_measurable: "?f \<in> borel_measurable lborel"
      using rough_output_lp unfolding aim_complex_lp_on_plane_def by blast
    have pointwise_AE: "AE z in lborel. (\<lambda>n. ?F n z) \<longlonglongrightarrow> ?f z"
      using psi_pointwise by simp
    show ?thesis
      by (rule aim_complex_lp_norm_cauchy_AE_limit[OF target_positive
            sequence_lp rough_output_measurable output_cauchy pointwise_AE])
  qed
  show ?thesis
    by (rule exI[of _ psi], rule conjI[OF psi_pairs],
        rule conjI[OF psi_source_converges])
      (use output_limit in blast)
qed

end

end
