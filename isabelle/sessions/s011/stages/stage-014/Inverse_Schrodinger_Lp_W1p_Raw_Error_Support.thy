theory Inverse_Schrodinger_Lp_W1p_Raw_Error_Support
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Raw_Wirtinger_Derivative_Data"
begin

section \<open>Raw value presentation and common support\<close>

lemma slp_test_function_on_UNIV_from_set:
  assumes f_test: "slp_test_function_on X f"
  shows "slp_test_function_on UNIV f"
  using f_test unfolding slp_test_function_on_def by blast

lemma slp_raw_value_approximation_error_restricted:
  assumes phi_test: "slp_test_function_on X (phi n)"
  shows "slp_raw_value_approximation_error phi
      (slp_restrict_field X u) n =
    slp_restrict_field X (\<lambda>x. phi n x - u x)"
proof (rule ext)
  fix x :: slp_point
  show "slp_raw_value_approximation_error phi
      (slp_restrict_field X u) n x =
    slp_restrict_field X (\<lambda>y. phi n y - u y) x"
  proof (cases "x \<in> X")
    case True
    then show ?thesis
      by (simp add: slp_raw_value_approximation_error_def
            slp_restrict_field_def)
  next
    case False
    have phi_zero: "phi n x = 0"
    proof -
      have restriction:
          "slp_restrict_field X (phi n) x = phi n x"
        by (rule fun_cong[OF slp_test_function_restrict_field_eq[OF
              phi_test]])
      show ?thesis
        using restriction False by (simp add: slp_restrict_field_def)
    qed
    show ?thesis
      using False phi_zero
      by (simp add: slp_raw_value_approximation_error_def
            slp_restrict_field_def)
  qed
qed

lemma slp_raw_value_approximation_error_restricted_outside:
  assumes phi_test: "slp_test_function_on X (phi n)"
    and outside: "y \<notin> X"
  shows "slp_raw_value_approximation_error phi
      (slp_restrict_field X u) n y = 0"
  using fun_cong[OF
      slp_raw_value_approximation_error_restricted[
        where phi=phi and X=X and u=u and n=n, OF phi_test], of y]
    outside
  by (simp add: slp_restrict_field_def)

lemma slp_raw_partial_approximation_error_restricted_outside:
  assumes phi_test: "slp_test_function_on X (phi n)"
    and outside: "y \<notin> X"
  shows "slp_raw_partial_approximation_error phi
      (slp_restrict_field X (slp_gradient_wirtinger_partial Du)) n y = 0"
proof -
  have presentation:
      "slp_raw_partial_approximation_error phi
          (slp_restrict_field X (slp_gradient_wirtinger_partial Du)) n =
        slp_gradient_wirtinger_partial
          (slp_restrict_gradient X
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x))"
    by (rule slp_raw_partial_approximation_error_restricted_wirtinger[
          where phi=phi and X=X and Du=Du and n=n, OF phi_test])
  show ?thesis
    using fun_cong[OF presentation, of y] outside
    by (simp add: slp_gradient_wirtinger_partial_def
          slp_restrict_gradient_def slp_restrict_field_def)
qed

theorem slp_w1p_raw_restricted_value_and_support_data:
  assumes exponent_positive: "0 < p"
    and phi_test: "\<And>n. slp_test_function_on X (phi n)"
    and error_pairs:
      "\<And>n. slp_w1p_pair_on p X
        (\<lambda>x. phi n x - u x)
        (\<lambda>x. slp_classical_gradient (phi n) x - Du x)"
    and error_norm_tends:
      "((\<lambda>n. slp_w1p_norm_on p X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x))
        \<longlongrightarrow> 0) sequentially"
    and X_radius: "\<And>y. y \<in> X \<Longrightarrow> norm (z - y) \<le> R"
  shows phi_test_UNIV: "\<And>n. slp_test_function_on UNIV (phi n)"
    and raw_value_lp:
      "\<And>n. aim_complex_lp_on_plane p
        (slp_raw_value_approximation_error phi
          (slp_restrict_field X u) n)"
    and raw_value_power:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_raw_value_approximation_error phi
            (slp_restrict_field X u) n x) powr p))
        \<longlongrightarrow> 0) sequentially"
    and raw_value_support:
      "\<And>n y. slp_raw_value_approximation_error phi
          (slp_restrict_field X u) n y \<noteq> 0
        \<Longrightarrow> norm (z - y) \<le> R"
    and raw_partial_support:
      "\<And>n y. slp_raw_partial_approximation_error phi
          (slp_restrict_field X (slp_gradient_wirtinger_partial Du)) n y
          \<noteq> 0
        \<Longrightarrow> norm (z - y) \<le> R"
proof -
  show "slp_test_function_on UNIV (phi n)" for n
    by (rule slp_test_function_on_UNIV_from_set[
          where X=X and f="phi n", OF phi_test])
  have presentation:
      "slp_raw_value_approximation_error phi
          (slp_restrict_field X u) n =
        slp_restrict_field X (\<lambda>x. phi n x - u x)" for n
    by (rule slp_raw_value_approximation_error_restricted[
          where phi=phi and X=X and u=u and n=n, OF phi_test])
  show "aim_complex_lp_on_plane p
      (slp_raw_value_approximation_error phi
        (slp_restrict_field X u) n)" for n
    unfolding presentation[of n]
    using slp_w1p_norm_on_component_bounds[OF exponent_positive
      error_pairs[of n]] by blast
  have value_power:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. phi n y - u y) x) powr p))
        \<longlongrightarrow> 0) sequentially"
    by (rule slp_w1p_function_power_integral_tendsto_zero[OF
          exponent_positive error_pairs error_norm_tends])
  show "((\<lambda>n. integral\<^sup>L lborel
      (\<lambda>x. Real_Vector_Spaces.norm
        (slp_raw_value_approximation_error phi
          (slp_restrict_field X u) n x) powr p))
      \<longlongrightarrow> 0) sequentially"
    using value_power by (simp only: presentation)
  show "norm (z - y) \<le> R"
    if nonzero: "slp_raw_value_approximation_error phi
        (slp_restrict_field X u) n y \<noteq> 0" for n y
  proof (rule X_radius)
    show "y \<in> X"
    proof (rule ccontr)
      assume "y \<notin> X"
      then have "slp_raw_value_approximation_error phi
          (slp_restrict_field X u) n y = 0"
        by (rule slp_raw_value_approximation_error_restricted_outside[
              where phi=phi and X=X and u=u and n=n, OF phi_test])
      then show False using nonzero by contradiction
    qed
  qed
  show "norm (z - y) \<le> R"
    if nonzero: "slp_raw_partial_approximation_error phi
        (slp_restrict_field X (slp_gradient_wirtinger_partial Du)) n y
        \<noteq> 0" for n y
  proof (rule X_radius)
    show "y \<in> X"
    proof (rule ccontr)
      assume "y \<notin> X"
      then have "slp_raw_partial_approximation_error phi
          (slp_restrict_field X (slp_gradient_wirtinger_partial Du)) n y = 0"
        by (rule slp_raw_partial_approximation_error_restricted_outside[
              where phi=phi and X=X and Du=Du and n=n, OF phi_test])
      then show False using nonzero by contradiction
    qed
  qed
qed

end
