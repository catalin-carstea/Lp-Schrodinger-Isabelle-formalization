theory Inverse_Schrodinger_Lp_W1p_Zero_AE_Pointwise_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Test_Pointwise_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Zero_Pair_AE_Subsequence"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Coarse_Triangle"
begin

section \<open>Almost-everywhere pointwise control of zero Sobolev pairs\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_AE_pointwise_bound_on_bounded_set:
  fixes b A :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows
    "AE z in lborel.
      norm (slp_restrict_field X u z) \<le>
        (norm (inverse (of_real pi :: complex)) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
              powr (1 / q)) *
          (192 * slp_w1p_norm_on b X u Du)"
proof -
  have exponent_lower: "1 < b"
    and exponent_one_le: "1 \<le> b"
    using exponent_above_two by linarith+
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" and r :: "nat \<Rightarrow> nat"
    where phi_pairs:
        "\<forall>n. slp_test_function_on X (phi n) \<and>
          slp_w1p_pair_on b X (phi n) (slp_classical_gradient (phi n))"
      and phi_converges:
        "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          slp_w1p_norm_on b X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
      and r_strict: "strict_mono r"
      and phi_AE:
        "AE z in lborel.
          (\<lambda>n. phi (r n) z - slp_restrict_field X u z)
            \<longlonglongrightarrow> 0"
    using slp_w1p_zero_pair_function_AE_subsequence[
      OF exponent_lower zero_pair]
    by blast
  let ?psi = "\<lambda>n. phi (r n)"
  let ?E = "\<lambda>n. slp_w1p_norm_on b X
    (\<lambda>x. ?psi n x - u x)
    (\<lambda>x. slp_classical_gradient (?psi n) x - Du x)"
  let ?W = "slp_w1p_norm_on b X u Du"
  let ?K = "norm (inverse (of_real pi :: complex)) *
    (integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
        powr (1 / q)"
  have coefficient_nonnegative: "0 \<le> ?K"
    by (rule mult_nonneg_nonneg) simp_all
  have rough_norm_nonnegative: "0 \<le> ?W"
    unfolding slp_w1p_norm_on_def by simp
  have r_lower: "n \<le> r n" for n
    using r_strict by (rule seq_suble)
  have psi_test: "slp_test_function_on X (?psi n)" for n
    using phi_pairs by blast
  have psi_pair:
      "slp_w1p_pair_on b X (?psi n) (slp_classical_gradient (?psi n))"
      for n
    using phi_pairs by blast
  have rough_pair: "slp_w1p_pair_on b X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have psi_converges:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N. ?E n < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail:
        "\<forall>n\<ge>N. slp_w1p_norm_on b X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
      using phi_converges epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N. ?E n < epsilon"
    proof (rule exI[of _ N], intro allI impI)
      fix n
      assume n_tail: "N \<le> n"
      have rn_tail: "N \<le> r n"
        using n_tail r_lower[of n] by linarith
      show "?E n < epsilon"
        using tail rn_tail by blast
    qed
  qed
  have error_norm_nonnegative: "0 \<le> ?E n" for n
    unfolding slp_w1p_norm_on_def by simp
  have error_norm_tends: "(?E \<longlongrightarrow> 0) sequentially"
  proof (rule metric_LIMSEQ_I)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail: "\<forall>n\<ge>N. ?E n < epsilon"
      using psi_converges epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N. dist (?E n) 0 < epsilon"
      by (rule exI[of _ N])
        (use tail error_norm_nonnegative in auto)
  qed
  have error_pair:
      "slp_w1p_pair_on b X
        (\<lambda>x. ?psi n x - u x)
        (\<lambda>x. slp_classical_gradient (?psi n) x - Du x)" for n
    by (rule slp_w1p_pair_on_diff[OF
          exponent_one_le psi_pair rough_pair])
  have reverse_error_pair:
      "slp_w1p_pair_on b X
        (\<lambda>x. u x - ?psi n x)
        (\<lambda>x. Du x - slp_classical_gradient (?psi n) x)" for n
    by (rule slp_w1p_pair_on_diff[OF
          exponent_one_le rough_pair psi_pair])
  have reverse_function_power:
      "norm (slp_restrict_field X (\<lambda>y. u y - ?psi n y) x) powr b =
        norm (slp_restrict_field X (\<lambda>y. ?psi n y - u y) x) powr b"
      for n x
    unfolding slp_restrict_field_def
    by (cases "x \<in> X") (simp_all add: norm_minus_commute)
  have reverse_derivative_power:
      "norm (slp_restrict_field X
          (\<lambda>y. (Du y - slp_classical_gradient (?psi n) y) $ i) x)
          powr b =
        norm (slp_restrict_field X
          (\<lambda>y. (slp_classical_gradient (?psi n) y - Du y) $ i) x)
          powr b"
      for n x and i :: 2
    unfolding slp_restrict_field_def
    by (cases "x \<in> X") (simp_all add: norm_minus_commute)
  have reverse_error_norm:
      "slp_w1p_norm_on b X
          (\<lambda>x. u x - ?psi n x)
          (\<lambda>x. Du x - slp_classical_gradient (?psi n) x) = ?E n"
      for n
    unfolding slp_w1p_norm_on_def
    by (simp only: reverse_function_power reverse_derivative_power)
  have psi_norm_bound:
      "slp_w1p_norm_on b X (?psi n) (slp_classical_gradient (?psi n)) \<le>
        48 * (?W + ?E n)" for n
  proof -
    note reconstruction = slp_w1p_norm_on_diff_coarse_triangle[
      OF exponent_one_le rough_pair reverse_error_pair[of n]]
    have function_reconstruction:
        "(\<lambda>x. u x - (u x - ?psi n x)) = ?psi n"
      by (rule ext) simp
    have gradient_reconstruction:
        "(\<lambda>x. Du x -
          (Du x - slp_classical_gradient (?psi n) x)) =
          slp_classical_gradient (?psi n)"
      by (rule ext) simp
    show ?thesis
      using reconstruction
      by (simp only: function_reconstruction gradient_reconstruction
          reverse_error_norm)
  qed
  have psi_pointwise:
      "AE z in lborel.
        (\<lambda>n. ?psi n z) \<longlonglongrightarrow> slp_restrict_field X u z"
  proof (use phi_AE in eventually_elim)
    fix z
    assume error_tends:
        "(\<lambda>n. ?psi n z - slp_restrict_field X u z)
          \<longlonglongrightarrow> 0"
    show "(\<lambda>n. ?psi n z) \<longlonglongrightarrow> slp_restrict_field X u z"
      using error_tends Lim_null by auto
  qed
  show ?thesis
  proof (use psi_pointwise in eventually_elim)
    fix z
    assume pointwise:
        "(\<lambda>n. ?psi n z) \<longlonglongrightarrow> slp_restrict_field X u z"
    show "norm (slp_restrict_field X u z) \<le> ?K * (192 * ?W)"
    proof (cases "z \<in> X")
      case False
      then show ?thesis
        unfolding slp_restrict_field_def
        using coefficient_nonnegative rough_norm_nonnegative
        by simp
    next
      case True
      have smooth_bound:
          "norm (?psi n z) \<le>
            ?K *
              (4 * slp_w1p_norm_on b X (?psi n)
                (slp_classical_gradient (?psi n)))" for n
        unfolding q_def
        by (rule slp_test_function_w1p_pointwise_bound_on_bounded_set[
              OF exponent_above_two radius_nonnegative set_radius True
                psi_test psi_pair])
      have pointwise_bound:
          "norm (?psi n z) \<le>
            ?K * (4 * (48 * (?W + ?E n)))" for n
      proof (rule order_trans[OF smooth_bound])
        have four_bound:
            "4 * slp_w1p_norm_on b X (?psi n)
                (slp_classical_gradient (?psi n)) \<le>
              4 * (48 * (?W + ?E n))"
          by (rule mult_left_mono[OF psi_norm_bound]) simp
        show "?K *
              (4 * slp_w1p_norm_on b X (?psi n)
                (slp_classical_gradient (?psi n))) \<le>
            ?K * (4 * (48 * (?W + ?E n)))"
          by (rule mult_left_mono[OF four_bound coefficient_nonnegative])
      qed
      have norm_tends:
          "((\<lambda>n. norm (?psi n z)) \<longlongrightarrow>
            norm (slp_restrict_field X u z)) sequentially"
        by (rule tendsto_norm[OF pointwise])
      have rhs_tends:
          "((\<lambda>n. ?K * (4 * (48 * (?W + ?E n)))) \<longlongrightarrow>
            ?K * (192 * ?W)) sequentially"
      proof -
        have raw:
            "((\<lambda>n. ?K * (4 * (48 * (?W + ?E n)))) \<longlongrightarrow>
              ?K * (4 * (48 * (?W + 0)))) sequentially"
          by (intro tendsto_intros error_norm_tends)
        show ?thesis
          using raw by simp
      qed
      have eventually_bound:
          "\<forall>\<^sub>F n in sequentially.
            norm (?psi n z) \<le> ?K * (4 * (48 * (?W + ?E n)))"
        using pointwise_bound by simp
      show ?thesis
        by (rule tendsto_le[OF trivial_limit_sequentially rhs_tends
              norm_tends eventually_bound])
    qed
  qed
qed

end

end
