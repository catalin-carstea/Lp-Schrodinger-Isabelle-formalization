theory Inverse_Schrodinger_Lp_W1p_Rough_Far_AE
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Target_Integrability"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Zero_Pair_AE_Subsequence"
begin

section \<open>Almost-everywhere rough far-product identity\<close>

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_w1p_zero_pair_partial_inverse_oscillatory_divided_rough_far_product_AE:
  fixes p :: real
  assumes tau_positive: "0 < tau"
    and exponent_above_two: "2 < p"
    and X_bounded: "bounded X"
    and zero_pair: "slp_w1p_zero_pair_on p X u Du"
  shows "AE z in lborel.
    slp_partial_inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * slp_restrict_field X u x) z =
      (1 / (\<i> * of_real tau)) *
        (slp_center_kernel tau c z * slp_restrict_field X u z -
          slp_partial_inverse
            (\<lambda>x. slp_center_kernel tau c x *
              slp_restrict_field X
                (slp_gradient_wirtinger_partial Du) x) z)"
proof -
  have exponent_lower: "1 < p"
    using exponent_above_two by linarith
  have exponent_one_le: "1 \<le> p"
    using exponent_above_two by linarith
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" and r :: "nat \<Rightarrow> nat"
    where phi_pairs:
        "\<forall>n. slp_test_function_on X (phi n) \<and>
          slp_w1p_pair_on p X (phi n) (slp_classical_gradient (phi n))"
      and phi_converges:
        "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          slp_w1p_norm_on p X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
      and r_strict: "strict_mono r"
      and phi_AE:
        "AE x in lborel.
          (\<lambda>n. phi (r n) x - slp_restrict_field X u x)
            \<longlonglongrightarrow> 0"
    using slp_w1p_zero_pair_function_AE_subsequence[OF
      exponent_lower zero_pair]
    by blast
  let ?psi = "\<lambda>n. phi (r n)"
  have r_lower: "n \<le> r n" for n
    using r_strict by (rule seq_suble)
  have psi_test: "slp_test_function_on X (?psi n)" for n
    using phi_pairs by blast
  have psi_pair:
      "slp_w1p_pair_on p X (?psi n) (slp_classical_gradient (?psi n))"
      for n
    using phi_pairs by blast
  have rough_pair: "slp_w1p_pair_on p X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have error_pairs:
      "slp_w1p_pair_on p X
        (\<lambda>x. ?psi n x - u x)
        (\<lambda>x. slp_classical_gradient (?psi n) x - Du x)" for n
    by (rule slp_w1p_pair_on_diff[OF
          exponent_one_le psi_pair rough_pair])
  have psi_converges:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X
          (\<lambda>x. ?psi n x - u x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - Du x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail:
        "\<forall>n\<ge>N.
          slp_w1p_norm_on p X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
      using phi_converges epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X
          (\<lambda>x. ?psi n x - u x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - Du x) < epsilon"
    proof (rule exI[of _ N], intro allI impI)
      fix n
      assume n_tail: "N \<le> n"
      have rn_tail: "N \<le> r n"
        using n_tail r_lower[of n] by linarith
      show "slp_w1p_norm_on p X
          (\<lambda>x. ?psi n x - u x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - Du x) < epsilon"
        using tail rn_tail by blast
    qed
  qed
  have error_norm_nonnegative:
      "0 \<le> slp_w1p_norm_on p X
        (\<lambda>x. ?psi n x - u x)
        (\<lambda>x. slp_classical_gradient (?psi n) x - Du x)" for n
    unfolding slp_w1p_norm_on_def by simp
  have error_norm_tends:
      "((\<lambda>n. slp_w1p_norm_on p X
          (\<lambda>x. ?psi n x - u x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - Du x))
        \<longlongrightarrow> 0) sequentially"
  proof (rule metric_LIMSEQ_I)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail:
        "\<forall>n\<ge>N.
          slp_w1p_norm_on p X
            (\<lambda>x. ?psi n x - u x)
            (\<lambda>x. slp_classical_gradient (?psi n) x - Du x) < epsilon"
      using psi_converges epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N.
        dist (slp_w1p_norm_on p X
          (\<lambda>x. ?psi n x - u x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - Du x)) 0 < epsilon"
      by (rule exI[of _ N])
        (use tail error_norm_nonnegative in auto)
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
  obtain A where A_bound: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    using X_bounded unfolding bounded_iff by blast
  show ?thesis
  proof (use psi_pointwise in eventually_elim)
    fix z
    assume pointwise_limit:
        "(\<lambda>n. ?psi n z) \<longlonglongrightarrow> slp_restrict_field X u z"
    let ?R = "norm z + max 0 A"
    have radius_nonnegative: "0 \<le> ?R"
      by simp
    have X_radius: "norm (z - y) \<le> ?R" if "y \<in> X" for y
    proof -
      have "norm (z - y) \<le> norm z + norm y"
        by (rule norm_triangle_ineq4)
      also have "... \<le> norm z + max 0 A"
        using A_bound[OF that] by linarith
      finally show ?thesis .
    qed
    show "slp_partial_inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * slp_restrict_field X u x) z =
      (1 / (\<i> * of_real tau)) *
        (slp_center_kernel tau c z * slp_restrict_field X u z -
          slp_partial_inverse
            (\<lambda>x. slp_center_kernel tau c x *
              slp_restrict_field X
                (slp_gradient_wirtinger_partial Du) x) z)"
      by (rule
          slp_w1p_partial_inverse_oscillatory_divided_rough_far_product_of_pair[
            OF tau_positive exponent_above_two radius_nonnegative psi_test
              error_pairs error_norm_tends rough_pair X_radius pointwise_limit])
  qed
qed

end

end
