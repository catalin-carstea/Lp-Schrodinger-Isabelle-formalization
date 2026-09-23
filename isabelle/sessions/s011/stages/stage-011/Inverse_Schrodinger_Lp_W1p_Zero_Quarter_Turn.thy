theory Inverse_Schrodinger_Lp_W1p_Zero_Quarter_Turn
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Quarter_Turn_Pair"
begin

section \<open>Classical derivatives of the inverse-turn pullback\<close>

theorem slp_classical_gradient_inverse_quarter_turn:
  fixes v :: slp_scalar_field
  assumes v_smooth: "smooth_on UNIV v"
  shows "slp_classical_gradient (\<lambda>x. v (- slp_quarter_turn x)) =
    (\<lambda>x. \<chi> i. if i = 0
      then - slp_classical_gradient v (- slp_quarter_turn x) $ 1
      else slp_classical_gradient v (- slp_quarter_turn x) $ 0)"
proof -
  let ?R = "\<lambda>x. - slp_quarter_turn x"
  have R_bounded: "bounded_linear ?R"
    by (rule bounded_linear_minus)
      (simp only: linear_conv_bounded_linear[symmetric] slp_quarter_turn_linear)
  have R_diff: "?R differentiable (at x)" for x
    by (rule bounded_linear_imp_differentiable[OF R_bounded])
  have R_derivative: "frechet_derivative ?R (at x) = ?R" for x
    using frechet_derivative_at[OF bounded_linear_imp_has_derivative[OF R_bounded]]
    by simp
  have index_cases: "i = (0::2) \<or> i = 1" for i
    using exhaust_2[of i] by auto
  have axis_zero: "?R (axis 0 1) = - axis 1 1"
    unfolding vec_eq_iff
  proof (intro allI)
    fix i :: 2
    show "?R (axis 0 1) $ i = (- axis 1 1) $ i"
      using index_cases[of i]
      by (auto simp: axis_def slp_quarter_turn_def)
  qed
  have axis_one: "?R (axis 1 1) = axis 0 1"
    unfolding vec_eq_iff
  proof (intro allI)
    fix i :: 2
    show "?R (axis 1 1) $ i = axis 0 1 $ i"
      using index_cases[of i]
      by (auto simp: axis_def slp_quarter_turn_def)
  qed
  have v_diff: "v differentiable (at x)" for x
    using smooth_on_imp_differentiable_on[OF v_smooth]
    by (simp add: differentiable_on_def)
  have chain:
      "frechet_derivative (\<lambda>x. v (?R x)) (at x) =
        frechet_derivative v (at (?R x)) \<circ> ?R" for x
    using frechet_derivative_compose[OF R_diff[of x] v_diff[of "?R x"]]
    by (simp add: comp_def R_derivative)
  have partial_zero:
      "slp_complex_partial_derivative (\<lambda>x. v (?R x)) 0 x =
        - slp_complex_partial_derivative v 1 (?R x)" for x
    unfolding slp_complex_partial_derivative_def
    by (simp add: chain axis_zero
          linear_neg[OF linear_frechet_derivative[OF v_diff]])
  have partial_one:
      "slp_complex_partial_derivative (\<lambda>x. v (?R x)) 1 x =
        slp_complex_partial_derivative v 0 (?R x)" for x
    unfolding slp_complex_partial_derivative_def
    by (simp add: chain axis_one)
  show ?thesis
  proof (rule ext)
    fix x
    show "slp_classical_gradient (\<lambda>x. v (?R x)) x =
        (\<chi> i. if i = 0 then - slp_classical_gradient v (?R x) $ 1
          else slp_classical_gradient v (?R x) $ 0)"
      unfolding vec_eq_iff
    proof (intro allI)
      fix i :: 2
      show "slp_classical_gradient (\<lambda>x. v (?R x)) x $ i =
          (\<chi> j. if j = 0 then - slp_classical_gradient v (?R x) $ 1
            else slp_classical_gradient v (?R x) $ 0) $ i"
        using index_cases[of i]
        by (auto simp: slp_classical_gradient_def partial_zero partial_one)
    qed
  qed
qed

section \<open>Transport of the compact-smooth closure\<close>

theorem slp_w1p_zero_pair_inverse_quarter_turn:
  assumes exponent_one_le: "1 \<le> p"
    and zero_pair: "slp_w1p_zero_pair_on p X u Du"
  shows "slp_w1p_zero_pair_on p (image slp_quarter_turn X)
      (\<lambda>x. u (- slp_quarter_turn x))
      (\<lambda>x. \<chi> i. if i = 0 then - Du (- slp_quarter_turn x) $ 1
        else Du (- slp_quarter_turn x) $ 0) \<and>
    slp_w1p_norm_on p (image slp_quarter_turn X)
      (\<lambda>x. u (- slp_quarter_turn x))
      (\<lambda>x. \<chi> i. if i = 0 then - Du (- slp_quarter_turn x) $ 1
        else Du (- slp_quarter_turn x) $ 0) =
      slp_w1p_norm_on p X u Du"
proof -
  let ?R = "\<lambda>x. - slp_quarter_turn x"
  let ?Y = "image slp_quarter_turn X"
  let ?Ru = "\<lambda>x. u (?R x)"
  let ?RDu = "(\<lambda>x. \<chi> i. if i = 0 then - Du (?R x) $ 1
    else Du (?R x) $ 0) :: slp_gradient_field"
  have base_pair: "slp_w1p_pair_on p X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  note rotated_base = slp_w1p_pair_inverse_quarter_turn[OF base_pair]
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" where
    phi_test: "\<And>n. slp_test_function_on X (phi n)"
    and phi_pair:
      "\<And>n. slp_w1p_pair_on p X (phi n) (slp_classical_gradient (phi n))"
    and source_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have phi_smooth: "smooth_on UNIV (phi n)" for n
    using phi_test[of n] unfolding slp_test_function_on_def by blast
  let ?psi = "\<lambda>n x. phi n (?R x)"
  have psi_test: "slp_test_function_on ?Y (?psi n)" for n
    by (rule conjunct1[OF slp_test_function_on_quarter_turn_domains[OF phi_test]])
  have psi_pair:
      "slp_w1p_pair_on p ?Y (?psi n) (slp_classical_gradient (?psi n))"
    for n
    using conjunct1[OF slp_w1p_pair_inverse_quarter_turn[OF phi_pair[of n]]]
    by (simp only: slp_classical_gradient_inverse_quarter_turn[OF phi_smooth])
  have error_norm:
      "slp_w1p_norm_on p ?Y (\<lambda>x. ?psi n x - ?Ru x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - ?RDu x) =
        slp_w1p_norm_on p X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x)"
    for n
  proof -
    have error_pair:
        "slp_w1p_pair_on p X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x)"
      by (rule slp_w1p_pair_on_diff[OF exponent_one_le phi_pair[of n] base_pair])
    have gradient_difference:
        "(\<lambda>x. \<chi> i. if i = 0
            then - (slp_classical_gradient (phi n) (?R x) - Du (?R x)) $ 1
            else (slp_classical_gradient (phi n) (?R x) - Du (?R x)) $ 0) =
          (\<lambda>x. slp_classical_gradient (?psi n) x - ?RDu x)"
      by (rule ext)
        (auto simp: slp_classical_gradient_inverse_quarter_turn[OF phi_smooth]
          vec_eq_iff algebra_simps split: if_splits)
    show ?thesis
      using conjunct2[OF slp_w1p_pair_inverse_quarter_turn[OF error_pair]]
      by (simp only: gradient_difference)
  qed
  have rotated_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p ?Y (\<lambda>x. ?psi n x - ?Ru x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - ?RDu x) < epsilon"
    using source_tail by (simp only: error_norm)
  have rotated_zero: "slp_w1p_zero_pair_on p ?Y ?Ru ?RDu"
    unfolding slp_w1p_zero_pair_on_def
    by (rule conjI[OF conjunct1[OF rotated_base]], rule exI[of _ ?psi])
      (use psi_test psi_pair rotated_tail in blast)
  show ?thesis by (rule conjI[OF rotated_zero conjunct2[OF rotated_base]])
qed

end
