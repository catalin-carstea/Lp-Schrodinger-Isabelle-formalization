theory Inverse_Schrodinger_Lp_W1p_Zero_Pair_Partial_Psi_Pointwise_Limit
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Cauchy_Bounded_Support_Lp_Continuity"
begin

section \<open>Literal pointwise oscillatory-Cauchy limit of zero-pair approximants\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_partial_psi_pointwise_limit:
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and X_bounded: "bounded X"
    and zero_pair: "slp_w1p_zero_pair_on a X u Du"
  shows "aim_complex_lp_on_plane (aim_hls_target_exponent a)
      (slp_restrict_field X u) \<and>
    (\<exists>psi :: nat \<Rightarrow> slp_scalar_field.
      (\<forall>n. slp_test_function_on X (psi n) \<and>
        slp_w1p_pair_on a X (psi n) (slp_classical_gradient (psi n))) \<and>
      (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a X
          (\<lambda>x. psi n x - u x)
          (\<lambda>x. slp_classical_gradient (psi n) x - Du x) < epsilon) \<and>
      (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. psi n x - slp_restrict_field X u x) < epsilon) \<and>
      (\<forall>tau c z.
        ((\<lambda>n. slp_partial_psi_inverse tau c (psi n) z)
          \<longlongrightarrow> slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) sequentially))"
proof -
  note approximation = slp_w1p_zero_pair_target_limit[OF
    a_lower a_upper zero_pair]
  have rough_target_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_restrict_field X u)"
    by (rule approximation[THEN conjunct1])
  obtain psi :: "nat \<Rightarrow> slp_scalar_field" where psi_pairs:
      "\<forall>n. slp_test_function_on X (psi n) \<and>
        slp_w1p_pair_on a X (psi n) (slp_classical_gradient (psi n))"
    and psi_source_converges:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a X
          (\<lambda>x. psi n x - u x)
          (\<lambda>x. slp_classical_gradient (psi n) x - Du x) < epsilon"
    and psi_target_converges:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. psi n x - slp_restrict_field X u x) < epsilon"
    using approximation by blast
  have target_above_two: "2 < aim_hls_target_exponent a"
    by (rule slp_qstar_exponent_relations(1)[OF a_lower a_upper])
  have target_positive: "0 < aim_hls_target_exponent a"
    using target_above_two by linarith
  have psi_target_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) (psi n)" for n
  proof -
    have psi_test_UNIV: "slp_test_function_on UNIV (psi n)"
      using psi_pairs unfolding slp_test_function_on_def by blast
    show ?thesis
      by (rule slp_test_function_aim_complex_lp_on_plane[OF
            target_positive psi_test_UNIV])
  qed
  let ?E = "\<lambda>n. aim_complex_lp_norm (aim_hls_target_exponent a)
    (\<lambda>x. psi n x - slp_restrict_field X u x)"
  have error_norm_nonnegative: "0 \<le> ?E n" for n
    unfolding aim_complex_lp_norm_def by simp
  have error_norm_tends: "(?E \<longlongrightarrow> 0) sequentially"
  proof (rule metric_LIMSEQ_I)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail: "\<forall>n\<ge>N. ?E n < epsilon"
      using psi_target_converges epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N. dist (?E n) 0 < epsilon"
      by (rule exI[of _ N])
        (use tail error_norm_nonnegative in auto)
  qed
  obtain A::real where X_bound:
      "\<And>y. y \<in> X \<Longrightarrow> norm_class.norm y \<le> A"
    using X_bounded unfolding bounded_iff by blast
  have psi_nonzero_in:
      "psi n y \<noteq> 0 \<Longrightarrow> y \<in> X" for n y
  proof -
    assume psi_nonzero: "psi n y \<noteq> 0"
    have support_within: "closure {x. psi n x \<noteq> 0} \<subseteq> X"
      using psi_pairs unfolding slp_test_function_on_def by blast
    have "y \<in> closure {x. psi n x \<noteq> 0}"
      by (rule subsetD[OF closure_subset]) (use psi_nonzero in simp)
    then show "y \<in> X"
      by (rule subsetD[OF support_within])
  qed
  have rough_nonzero_in:
      "slp_restrict_field X u y \<noteq> 0 \<Longrightarrow> y \<in> X" for y
    unfolding slp_restrict_field_def by (cases "y \<in> X") auto
  have phase_error:
      "(\<lambda>x. slp_oscillatory_modulation tau c (psi n) x -
        slp_oscillatory_modulation tau c (slp_restrict_field X u) x) =
      slp_oscillatory_modulation tau c
        (\<lambda>x. psi n x - slp_restrict_field X u x)" for tau c n
    by (rule ext)
      (simp add: slp_oscillatory_modulation_def algebra_simps)
  have pointwise_operator_limit:
      "((\<lambda>n. slp_partial_psi_inverse tau c (psi n) z)
        \<longlongrightarrow> slp_partial_psi_inverse tau c
          (slp_restrict_field X u) z) sequentially" for tau c z
  proof -
    let ?R = "norm_class.norm z + max 0 A"
    have R_nonnegative: "0 \<le> ?R"
      by simp
    have source_support:
        "\<And>n y. slp_oscillatory_modulation tau c (psi n) y \<noteq> 0
          \<Longrightarrow> norm_class.norm (z - y) \<le> ?R"
    proof -
      fix n y
      assume modulated_nonzero:
        "slp_oscillatory_modulation tau c (psi n) y \<noteq> 0"
      have psi_nonzero: "psi n y \<noteq> 0"
        using modulated_nonzero
        unfolding slp_oscillatory_modulation_def by auto
      have y_in: "y \<in> X"
        by (rule psi_nonzero_in[OF psi_nonzero])
      have y_bound: "norm_class.norm y \<le> max 0 A"
        using X_bound[OF y_in] by linarith
      have triangle:
          "norm_class.norm (z - y) \<le>
            norm_class.norm z + norm_class.norm y"
        by (rule norm_triangle_ineq4)
      show "norm_class.norm (z - y) \<le> ?R"
        using triangle y_bound by linarith
    qed
    have target_support:
        "\<And>y. slp_oscillatory_modulation tau c
          (slp_restrict_field X u) y \<noteq> 0
          \<Longrightarrow> norm_class.norm (z - y) \<le> ?R"
    proof -
      fix y
      assume modulated_nonzero:
        "slp_oscillatory_modulation tau c
          (slp_restrict_field X u) y \<noteq> 0"
      have rough_nonzero: "slp_restrict_field X u y \<noteq> 0"
        using modulated_nonzero
        unfolding slp_oscillatory_modulation_def by auto
      have y_in: "y \<in> X"
        by (rule rough_nonzero_in[OF rough_nonzero])
      have y_bound: "norm_class.norm y \<le> max 0 A"
        using X_bound[OF y_in] by linarith
      have triangle:
          "norm_class.norm (z - y) \<le>
            norm_class.norm z + norm_class.norm y"
        by (rule norm_triangle_ineq4)
      show "norm_class.norm (z - y) \<le> ?R"
        using triangle y_bound by linarith
    qed
    have modulated_source_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_oscillatory_modulation tau c (psi n))" for n
      using psi_target_lp[of n] by simp
    have modulated_target_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_oscillatory_modulation tau c (slp_restrict_field X u))"
      using rough_target_lp by simp
    have modulated_error_tends:
        "((\<lambda>n. aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. slp_oscillatory_modulation tau c (psi n) x -
            slp_oscillatory_modulation tau c
              (slp_restrict_field X u) x)) \<longlongrightarrow> 0) sequentially"
      using error_norm_tends
      by (simp only: phase_error slp_oscillatory_modulation_lp_norm)
    have ordinary_limit:
        "((\<lambda>n. slp_cauchy_transform SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c (psi n)) z)
          \<longlongrightarrow> slp_cauchy_transform SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c
              (slp_restrict_field X u)) z) sequentially"
      by (rule slp_cauchy_transform_tendsto_of_bounded_support_lp_norm[OF
            target_above_two R_nonnegative modulated_source_lp
            modulated_target_lp source_support target_support
            modulated_error_tends])
    show ?thesis
      using ordinary_limit unfolding slp_partial_psi_inverse_def .
  qed
  show ?thesis
    by (rule conjI[OF rough_target_lp], rule exI[of _ psi])
      (use psi_pairs psi_source_converges psi_target_converges
        pointwise_operator_limit in blast)
qed

end

end
