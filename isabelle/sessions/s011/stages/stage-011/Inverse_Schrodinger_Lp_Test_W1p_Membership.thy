theory Inverse_Schrodinger_Lp_Test_W1p_Membership
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Test_Derivative_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Weak_Test_Multiplier"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Cauchy_Principal_Decay"
begin

section \<open>Classical smooth gradients satisfy the weak definition\<close>

theorem slp_smooth_classical_weak_gradient:
  fixes f :: slp_scalar_field
  assumes f_smooth: "smooth_on UNIV f"
  shows "slp_weak_gradient_on X f (slp_classical_gradient f)"
  unfolding slp_weak_gradient_on_def
proof (intro allI impI)
  fix phi :: slp_scalar_field and i :: 2
  assume phi_test: "slp_test_function_on X phi"
  have global_test: "slp_test_function_on UNIV h"
    if h_test: "slp_test_function_on X h" for h :: slp_scalar_field
    using h_test unfolding slp_test_function_on_def by blast
  have indicator_eq: "(\<lambda>x. indicator X x *\<^sub>R h x) = h"
    if h_test: "slp_test_function_on X h" for h :: slp_scalar_field
  proof -
    have "(\<lambda>x. indicator X x *\<^sub>R h x) = slp_restrict_field X h"
      by (rule ext) (simp add: indicator_def slp_restrict_field_def)
    also have "... = h"
      by (rule slp_test_function_restrict_field_eq[OF h_test])
    finally show ?thesis .
  qed
  have set_test_integrable: "set_integrable lborel X h"
    if h_test: "slp_test_function_on X h" for h :: slp_scalar_field
    using slp_test_function_integrable_bounded(1)[OF global_test[OF h_test]]
    unfolding set_integrable_def
    by (simp only: indicator_eq[OF h_test])
  have set_test_integral:
      "set_lebesgue_integral lborel X h = integral\<^sup>L lborel h"
    if h_test: "slp_test_function_on X h" for h :: slp_scalar_field
    by (simp only: set_lebesgue_integral_def indicator_eq[OF h_test])
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  let ?A = "\<lambda>x. f x * slp_complex_partial_derivative phi i x"
  let ?B = "\<lambda>x. slp_complex_partial_derivative f i x * phi x"
  have A_test: "slp_test_function_on X ?A"
    by (rule slp_test_function_on_mult_left[OF f_smooth
          slp_test_function_on_partial_derivative[OF phi_test]])
  have B_test: "slp_test_function_on X ?B"
    by (rule slp_test_function_on_mult_left[OF
          slp_complex_partial_derivative_smooth[OF f_smooth] phi_test])
  have product_test: "slp_test_function_on X (\<lambda>x. f x * phi x)"
    by (rule slp_test_function_on_mult_left[OF f_smooth phi_test])
  have A_integrable: "integrable lborel ?A"
    by (rule slp_test_function_integrable_bounded(1)[OF global_test[OF A_test]])
  have B_integrable: "integrable lborel ?B"
    by (rule slp_test_function_integrable_bounded(1)[OF global_test[OF B_test]])
  have derivative_eq:
      "slp_complex_partial_derivative (\<lambda>x. f x * phi x) i =
        (\<lambda>x. ?A x + ?B x)"
    by (rule ext, rule slp_complex_partial_derivative_mult[OF f_smooth phi_smooth])
  have derivative_integral_zero:
      "integral\<^sup>L lborel
        (slp_complex_partial_derivative (\<lambda>x. f x * phi x) i) = 0"
    by (rule slp_test_function_partial_integral_zero[OF global_test[OF product_test]])
  have sum_zero:
      "integral\<^sup>L lborel ?A + integral\<^sup>L lborel ?B = 0"
    using derivative_integral_zero
    by (simp only: derivative_eq Bochner_Integration.integral_add[OF A_integrable B_integrable])
  have ordinary_identity:
      "integral\<^sup>L lborel ?A = - integral\<^sup>L lborel ?B"
    using sum_zero by (simp only: eq_neg_iff_add_eq_0)
  have set_identity:
      "set_lebesgue_integral lborel X ?A =
        - set_lebesgue_integral lborel X ?B"
    by (simp only: set_test_integral[OF A_test] set_test_integral[OF B_test]
          ordinary_identity)
  show "set_integrable lborel X
          (\<lambda>x. f x * slp_complex_partial_derivative phi i x) \<and>
        set_integrable lborel X
          (\<lambda>x. slp_classical_gradient f x $ i * phi x) \<and>
        set_lebesgue_integral lborel X
          (\<lambda>x. f x * slp_complex_partial_derivative phi i x) =
          - set_lebesgue_integral lborel X
            (\<lambda>x. slp_classical_gradient f x $ i * phi x)"
    using set_test_integrable[OF A_test] set_test_integrable[OF B_test] set_identity
    by (simp add: slp_classical_gradient_def)
qed

section \<open>Compact tests are valid Sobolev pairs\<close>

theorem slp_test_function_w1p_pair:
  assumes p_positive: "0 < p" and f_test: "slp_test_function_on X f"
  shows "slp_w1p_pair_on p X f (slp_classical_gradient f)"
proof -
  have f_smooth: "smooth_on UNIV f"
    using f_test unfolding slp_test_function_on_def by blast
  have weak: "slp_weak_gradient_on X f (slp_classical_gradient f)"
    by (rule slp_smooth_classical_weak_gradient[OF f_smooth])
  have test_lp: "slp_complex_lp_on p X h"
    if h_test: "slp_test_function_on X h" for h :: slp_scalar_field
  proof -
    have h_global_test: "slp_test_function_on UNIV h"
      using h_test unfolding slp_test_function_on_def by blast
    have h_lp: "aim_complex_lp_on_plane p h"
      by (rule slp_test_function_aim_complex_lp_on_plane[OF p_positive h_global_test])
    show ?thesis
      unfolding slp_complex_lp_on_def
      by (simp only: slp_test_function_restrict_field_eq[OF h_test] h_lp)
  qed
  have f_lp: "slp_complex_lp_on p X f"
    by (rule test_lp[OF f_test])
  have derivative_lp: "slp_complex_lp_on p X (slp_complex_partial_derivative f i)"
    for i :: 2
    by (rule test_lp[OF slp_test_function_on_partial_derivative[OF f_test]])
  show ?thesis
    unfolding slp_w1p_pair_on_def
    using weak f_lp derivative_lp[of 0] derivative_lp[of 1]
    by (simp add: slp_classical_gradient_def)
qed

section \<open>The constant sequence gives zero-boundary membership\<close>

theorem slp_test_function_w1p_zero_pair:
  assumes p_positive: "0 < p" and f_test: "slp_test_function_on X f"
  shows "slp_w1p_zero_pair_on p X f (slp_classical_gradient f)"
proof -
  have f_pair: "slp_w1p_pair_on p X f (slp_classical_gradient f)"
    by (rule slp_test_function_w1p_pair[OF p_positive f_test])
  have approximation:
      "\<forall>epsilon>0. \<exists>N::nat. \<forall>n\<ge>N.
        slp_w1p_norm_on p X (\<lambda>x. f x - f x)
          (\<lambda>x. slp_classical_gradient f x - slp_classical_gradient f x)
          < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    show "\<exists>N::nat. \<forall>n\<ge>N.
        slp_w1p_norm_on p X (\<lambda>x. f x - f x)
          (\<lambda>x. slp_classical_gradient f x - slp_classical_gradient f x)
          < epsilon"
      using epsilon_positive
      by (intro exI[of _ "0::nat"]) (simp add: slp_w1p_norm_on_def slp_restrict_field_def)
  qed
  show ?thesis
    unfolding slp_w1p_zero_pair_on_def
  proof (rule conjI[OF f_pair])
    show "\<exists>phi::nat \<Rightarrow> slp_scalar_field.
        (\<forall>n. slp_test_function_on X (phi n) \<and>
          slp_w1p_pair_on p X (phi n) (slp_classical_gradient (phi n))) \<and>
        (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          slp_w1p_norm_on p X (\<lambda>x. phi n x - f x)
            (\<lambda>x. slp_classical_gradient (phi n) x - slp_classical_gradient f x)
            < epsilon)"
    proof (rule exI[of _ "\<lambda>n::nat. f"])
      show "(\<forall>n::nat. slp_test_function_on X f \<and>
          slp_w1p_pair_on p X f (slp_classical_gradient f)) \<and>
        (\<forall>epsilon>0. \<exists>N::nat. \<forall>n\<ge>N.
          slp_w1p_norm_on p X (\<lambda>x. f x - f x)
            (\<lambda>x. slp_classical_gradient f x - slp_classical_gradient f x)
            < epsilon)"
        using f_test f_pair approximation by simp
    qed
  qed
qed

end
