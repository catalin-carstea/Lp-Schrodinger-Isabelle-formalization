theory Inverse_Schrodinger_Lp_Local_W1s_Cutoff_Zero_Pair
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Esssup_Bounded_Multiplier"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Local_W1s"
    "Paper_ISLP_Evans_Compact_Support_W1p_Zero_Density.Evans_Compact_Support_W1p_Zero_Density_Interface"
begin

section \<open>Localizing whole-plane weak gradients\<close>

lemma slp_weak_gradient_on_UNIV_imp_on:
  assumes weak: "slp_weak_gradient_on UNIV u Du"
  shows "slp_weak_gradient_on X u Du"
  unfolding slp_weak_gradient_on_def
proof (intro allI impI)
  fix phi i
  assume phi_test: "slp_test_function_on X phi"
  let ?dphi = "slp_complex_partial_derivative phi i"
  let ?left = "\<lambda>x. u x * ?dphi x"
  let ?right = "\<lambda>x. Du x $ i * phi x"

  have phi_test_UNIV: "slp_test_function_on UNIV phi"
    by (rule slp_test_function_on_UNIV_from_set[OF phi_test])
  have global:
      "set_integrable lborel UNIV ?left \<and>
        set_integrable lborel UNIV ?right \<and>
        set_lebesgue_integral lborel UNIV ?left =
          - set_lebesgue_integral lborel UNIV ?right"
    using weak phi_test_UNIV
    unfolding slp_weak_gradient_on_def by blast

  have phi_restriction: "slp_restrict_field X phi = phi"
    by (rule slp_test_function_restrict_field_eq[OF phi_test])
  have derivative_restriction:
      "slp_restrict_field X ?dphi = ?dphi"
    by (rule slp_test_function_partial_restrict_field_eq[OF phi_test])
  have left_indicator:
      "(\<lambda>x. indicator X x *\<^sub>R ?left x) = ?left"
  proof (rule ext)
    fix x
    have derivative_point:
        "slp_restrict_field X ?dphi x = ?dphi x"
      using fun_cong[OF derivative_restriction, of x] .
    show "indicator X x *\<^sub>R ?left x = ?left x"
      using derivative_point
      by (cases "x \<in> X")
         (simp_all add: indicator_def slp_restrict_field_def)
  qed
  have right_indicator:
      "(\<lambda>x. indicator X x *\<^sub>R ?right x) = ?right"
  proof (rule ext)
    fix x
    have phi_point: "slp_restrict_field X phi x = phi x"
      using fun_cong[OF phi_restriction, of x] .
    show "indicator X x *\<^sub>R ?right x = ?right x"
      using phi_point
      by (cases "x \<in> X")
         (simp_all add: indicator_def slp_restrict_field_def)
  qed

  have local_left: "set_integrable lborel X ?left"
    using global
    unfolding set_integrable_def
    by (simp only: left_indicator indicator_UNIV scaleR_one)
  have local_right: "set_integrable lborel X ?right"
    using global
    unfolding set_integrable_def
    by (simp only: right_indicator indicator_UNIV scaleR_one)
  have left_integral:
      "set_lebesgue_integral lborel X ?left =
        set_lebesgue_integral lborel UNIV ?left"
    unfolding set_lebesgue_integral_def
    by (simp only: left_indicator indicator_UNIV scaleR_one)
  have right_integral:
      "set_lebesgue_integral lborel X ?right =
        set_lebesgue_integral lborel UNIV ?right"
    unfolding set_lebesgue_integral_def
    by (simp only: right_indicator indicator_UNIV scaleR_one)
  have global_identity:
      "set_lebesgue_integral lborel UNIV ?left =
        - set_lebesgue_integral lborel UNIV ?right"
    using global by blast
  show "set_integrable lborel X ?left \<and>
      set_integrable lborel X ?right \<and>
      set_lebesgue_integral lborel X ?left =
        - set_lebesgue_integral lborel X ?right"
  proof (intro conjI)
    show "set_integrable lborel X ?left"
      by (rule local_left)
    show "set_integrable lborel X ?right"
      by (rule local_right)
    show "set_lebesgue_integral lborel X ?left =
        - set_lebesgue_integral lborel X ?right"
      using global_identity left_integral right_integral by simp
  qed
qed

theorem slp_local_w1s_certificate_w1p_pair_on:
  assumes certificate: "slp_local_w1s_certificate p X u Du"
  shows "slp_w1p_pair_on p X u Du"
proof -
  have weak_UNIV: "slp_weak_gradient_on UNIV u Du"
    using certificate unfolding slp_local_w1s_certificate_def by blast
  have weak_X: "slp_weak_gradient_on X u Du"
    by (rule slp_weak_gradient_on_UNIV_imp_on[OF weak_UNIV])
  show ?thesis
    using certificate weak_X
    unfolding slp_local_w1s_certificate_def slp_w1p_pair_on_def
    by blast
qed

section \<open>Compact-smooth cutoff products in W1p zero\<close>

context evans_compact_support_w1p_zero_density
begin

theorem slp_local_w1s_certificate_mult_test_w1p_zero_pair:
  fixes p :: real
    and X :: "slp_point set"
    and u cutoff :: slp_scalar_field
    and Du :: slp_gradient_field
  assumes exponent_one_le: "1 \<le> p"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and certificate: "slp_local_w1s_certificate p X u Du"
    and cutoff_test: "slp_test_function_on X cutoff"
  shows "slp_w1p_zero_pair_on p X
    (\<lambda>x. cutoff x * u x)
    (\<lambda>x. \<chi> i. cutoff x * Du x $ i +
      u x * slp_complex_partial_derivative cutoff i x)"
proof -
  let ?v = "\<lambda>x. cutoff x * u x"
  let ?Dv = "\<lambda>x. \<chi> i. cutoff x * Du x $ i +
    u x * slp_complex_partial_derivative cutoff i x"
  let ?K = "closure {x. cutoff x \<noteq> 0}"

  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have pair: "slp_w1p_pair_on p X u Du"
    by (rule slp_local_w1s_certificate_w1p_pair_on[OF certificate])
  have cutoff_smooth: "smooth_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have product_pair: "slp_w1p_pair_on p X ?v ?Dv"
    by (rule slp_w1p_pair_on_mult_smooth_bounded[OF
          exponent_one_le X_measurable X_bounded pair cutoff_smooth])
  have K_compact: "compact ?K"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have K_subset: "?K \<subseteq> X"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have product_zero:
      "\<forall>x \<in> X - ?K. ?v x = 0 \<and> (\<forall>i. ?Dv x $ i = 0)"
  proof (intro ballI conjI allI)
    fix x
    assume x_outside: "x \<in> X - ?K"
    have x_not_K: "x \<notin> ?K"
      using x_outside by blast
    have cutoff_zero: "cutoff x = 0"
      using x_not_K closure_subset by blast
    show "?v x = 0"
      using cutoff_zero by simp
    fix i :: 2
    have derivative_support:
        "closure {y. slp_complex_partial_derivative cutoff i y \<noteq> 0}
          \<subseteq> ?K"
      by (rule slp_complex_partial_derivative_support_subset[OF cutoff_smooth])
    have derivative_zero:
        "slp_complex_partial_derivative cutoff i x = 0"
      using x_not_K derivative_support closure_subset by blast
    show "?Dv x $ i = 0"
      using cutoff_zero derivative_zero by simp
  qed
  show ?thesis
    using evans_compact_support_w1p_zero_density exponent_one_le X_open
      K_compact K_subset product_pair product_zero
    unfolding evans_compact_support_w1p_zero_density_claim_def
    by blast
qed

end

end
