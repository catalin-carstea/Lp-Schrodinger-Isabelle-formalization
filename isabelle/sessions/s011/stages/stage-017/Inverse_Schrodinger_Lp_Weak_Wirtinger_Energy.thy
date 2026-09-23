theory Inverse_Schrodinger_Lp_Weak_Wirtinger_Energy
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Field_H1"
    "Ordinary_Differential_Equations.Multivariate_Taylor"
begin

section \<open>Smooth-test conversion of weak Wirtinger equations\<close>

lemma slp_test_mixed_partial_commute:
  assumes phi_test: "slp_test_function_on U phi"
  shows
    "slp_complex_partial_derivative
        (slp_complex_partial_derivative phi 0) 1 x =
      slp_complex_partial_derivative
        (slp_complex_partial_derivative phi 1) 0 x"
proof -
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have first_fderiv:
      "(phi has_derivative frechet_derivative phi (at a))
        (at a within UNIV)" for a
  proof -
    have phi_differentiable: "phi differentiable at a"
      using smooth_on_imp_differentiable_on[OF phi_smooth]
      by (simp add: differentiable_on_def)
    show ?thesis
      using phi_differentiable
      by (simp add: frechet_derivative_works)
  qed
  have second_fderiv:
      "((\<lambda>y. frechet_derivative phi (at y) i) has_derivative
          frechet_derivative
            (\<lambda>y. frechet_derivative phi (at y) i) (at x))
        (at x within UNIV)" for i
  proof -
    have derivative_smooth:
        "smooth_on UNIV (\<lambda>y. frechet_derivative phi (at y) i)"
      by (rule smooth_on_frechet_derivative[OF phi_smooth])
    have derivative_differentiable:
        "(\<lambda>y. frechet_derivative phi (at y) i) differentiable at x"
      using smooth_on_imp_differentiable_on[OF derivative_smooth]
      by (simp add: differentiable_on_def)
    show ?thesis
      using derivative_differentiable
      by (simp add: frechet_derivative_works)
  qed
  have symmetric:
      "frechet_derivative
          (\<lambda>y. frechet_derivative phi (at y) (axis (0 :: 2) 1))
          (at x) (axis (1 :: 2) 1) =
        frechet_derivative
          (\<lambda>y. frechet_derivative phi (at y) (axis (1 :: 2) 1))
          (at x) (axis (0 :: 2) 1)"
  proof (rule symmetric_second_derivative_aux[
      where G=UNIV and f=phi
        and f'="\<lambda>a. frechet_derivative phi (at a)"
        and f''="\<lambda>j i. frechet_derivative
          (\<lambda>y. frechet_derivative phi (at y) i) (at x) j"
        and a=x and i="axis (0 :: 2) 1" and j="axis (1 :: 2) 1"])
    show "\<And>a. a \<in> UNIV \<Longrightarrow>
        (phi has_derivative frechet_derivative phi (at a))
          (at a within UNIV)"
      by (rule first_fderiv)
    show "\<And>i. ((\<lambda>y. frechet_derivative phi (at y) i) has_derivative
          (\<lambda>j. frechet_derivative
            (\<lambda>y. frechet_derivative phi (at y) i) (at x) j))
        (at x within UNIV)"
      by (rule second_fderiv)
    show "axis (0 :: 2) (1 :: real) \<noteq> axis (1 :: 2) 1"
    proof
      assume same:
        "axis (0 :: 2) (1 :: real) = axis (1 :: 2) 1"
      have same_zero:
          "(axis (0 :: 2) (1 :: real) :: slp_point) $ 0 =
            axis (1 :: 2) 1 $ 0"
        by (rule arg_cong[OF same])
      show False
        using same_zero by simp
    qed
    show "axis (0 :: 2) (1 :: real) \<noteq> 0"
      by simp
    show "axis (1 :: 2) (1 :: real) \<noteq> 0"
      by simp
    show "x \<in> (UNIV :: slp_point set)"
      by simp
    show "\<And>s t. s \<in> {0..1} \<Longrightarrow> t \<in> {0..1} \<Longrightarrow>
        x + s *\<^sub>R (axis (0 :: 2) (1 :: real)) +
          t *\<^sub>R (axis (1 :: 2) 1) \<in> (UNIV :: slp_point set)"
      by simp
  qed
  show ?thesis
    using symmetric unfolding slp_complex_partial_derivative_def .
qed

theorem slp_weak_partial_dbar_smooth_test_energy:
  assumes u_weak: "slp_weak_gradient_on U u Du"
    and projected_weak:
      "slp_weak_gradient_on U
        (slp_gradient_wirtinger_partial Du) Dprojected"
    and phi_test: "slp_test_function_on U phi"
  shows
    "set_integrable lborel U
        (\<lambda>x. \<Sum>i\<in>UNIV.
          Du x $ i * slp_classical_gradient phi x $ i) \<and>
      set_integrable lborel U
        (\<lambda>x. slp_gradient_wirtinger_dbar Dprojected x * phi x) \<and>
      set_lebesgue_integral lborel U
          (\<lambda>x. \<Sum>i\<in>UNIV.
            Du x $ i * slp_classical_gradient phi x $ i) =
        - 4 * set_lebesgue_integral lborel U
          (\<lambda>x. slp_gradient_wirtinger_dbar Dprojected x * phi x)"
proof -
  let ?d0 = "slp_complex_partial_derivative phi 0"
  let ?d1 = "slp_complex_partial_derivative phi 1"
  let ?h = "slp_gradient_wirtinger_partial Du"
  let ?q = "slp_gradient_wirtinger_dbar Dprojected"
  let ?A = "\<lambda>x. Du x $ 0 * ?d0 x"
  let ?B = "\<lambda>x. Du x $ 1 * ?d1 x"
  let ?C = "\<lambda>x. Du x $ 0 * ?d1 x"
  let ?D = "\<lambda>x. Du x $ 1 * ?d0 x"
  let ?P = "\<lambda>x. ?h x * ?d0 x"
  let ?Q = "\<lambda>x. ?h x * ?d1 x"
  let ?R = "\<lambda>x. Dprojected x $ 0 * phi x"
  let ?S = "\<lambda>x. Dprojected x $ 1 * phi x"
  let ?energy = "\<lambda>x. \<Sum>i\<in>UNIV.
    Du x $ i * slp_classical_gradient phi x $ i"
  let ?source = "\<lambda>x. ?q x * phi x"

  have d0_test: "slp_test_function_on U ?d0"
    by (rule slp_test_function_on_partial_derivative[OF phi_test])
  have d1_test: "slp_test_function_on U ?d1"
    by (rule slp_test_function_on_partial_derivative[OF phi_test])
  have u_data:
      "\<And>psi i. slp_test_function_on U psi \<Longrightarrow>
        set_integrable lborel U
          (\<lambda>x. u x * slp_complex_partial_derivative psi i x) \<and>
        set_integrable lborel U (\<lambda>x. Du x $ i * psi x) \<and>
        set_lebesgue_integral lborel U
            (\<lambda>x. u x * slp_complex_partial_derivative psi i x) =
          - set_lebesgue_integral lborel U
            (\<lambda>x. Du x $ i * psi x)"
    using u_weak unfolding slp_weak_gradient_on_def by blast
  have h_data:
      "\<And>psi i. slp_test_function_on U psi \<Longrightarrow>
        set_integrable lborel U
          (\<lambda>x. ?h x * slp_complex_partial_derivative psi i x) \<and>
        set_integrable lborel U
          (\<lambda>x. Dprojected x $ i * psi x) \<and>
        set_lebesgue_integral lborel U
            (\<lambda>x. ?h x * slp_complex_partial_derivative psi i x) =
          - set_lebesgue_integral lborel U
            (\<lambda>x. Dprojected x $ i * psi x)"
    using projected_weak unfolding slp_weak_gradient_on_def by blast

  note u00 = u_data[OF d0_test, of 0]
  note u11 = u_data[OF d1_test, of 1]
  note u01 = u_data[OF d1_test, of 0]
  note u10 = u_data[OF d0_test, of 1]
  note h0 = h_data[OF phi_test, of 0]
  note h1 = h_data[OF phi_test, of 1]
  have A_integrable: "set_integrable lborel U ?A"
    using u00 by blast
  have B_integrable: "set_integrable lborel U ?B"
    using u11 by blast
  have C_integrable: "set_integrable lborel U ?C"
    using u01 by blast
  have D_integrable: "set_integrable lborel U ?D"
    using u10 by blast
  have P_integrable: "set_integrable lborel U ?P"
    using h0 by blast
  have Q_integrable: "set_integrable lborel U ?Q"
    using h1 by blast
  have R_integrable: "set_integrable lborel U ?R"
    using h0 by blast
  have S_integrable: "set_integrable lborel U ?S"
    using h1 by blast
  have iD_integrable: "set_integrable lborel U (\<lambda>x. \<i> * ?D x)"
    using D_integrable by simp
  have iB_integrable: "set_integrable lborel U (\<lambda>x. \<i> * ?B x)"
    using B_integrable by simp
  have iS_integrable: "set_integrable lborel U (\<lambda>x. \<i> * ?S x)"
    using S_integrable by simp

  have mixed_function:
      "(\<lambda>x. u x * slp_complex_partial_derivative ?d1 0 x) =
        (\<lambda>x. u x * slp_complex_partial_derivative ?d0 1 x)"
  proof (rule ext)
    fix x
    note mixed = slp_test_mixed_partial_commute[OF phi_test, of x]
    show "u x * slp_complex_partial_derivative ?d1 0 x =
        u x * slp_complex_partial_derivative ?d0 1 x"
      by (simp only: mixed)
  qed
  have cross_integral:
      "set_lebesgue_integral lborel U ?C =
        set_lebesgue_integral lborel U ?D"
  proof -
    have negative_cross:
        "- set_lebesgue_integral lborel U ?C =
          - set_lebesgue_integral lborel U ?D"
      using u01 u10 mixed_function by simp
    show ?thesis
      using negative_cross by simp
  qed

  have distribute_difference:
      "\<And>a b d :: complex.
        ((a - b) / 2) * d = (a * d - b * d) / 2"
    apply (simp only: divide_inverse right_diff_distrib)
    by (simp only: left_diff_distrib right_diff_distrib mult_ac)
  have distribute_sum:
      "\<And>a b d :: complex.
        ((a + b) / 2) * d = (a * d + b * d) / 2"
    apply (simp only: divide_inverse distrib_right)
    by (simp only: distrib_left distrib_right mult_ac)

  have P_function:
      "?P = (\<lambda>x. (?A x - \<i> * ?D x) / 2)"
  proof (rule ext)
    fix x
    show "?P x = (?A x - \<i> * ?D x) / 2"
      unfolding slp_gradient_wirtinger_partial_def
      by (simp only: distribute_difference mult.assoc)
  qed
  have Q_function:
      "?Q = (\<lambda>x. (?C x - \<i> * ?B x) / 2)"
  proof (rule ext)
    fix x
    show "?Q x = (?C x - \<i> * ?B x) / 2"
      unfolding slp_gradient_wirtinger_partial_def
      by (simp only: distribute_difference mult.assoc)
  qed
  have P_integral:
      "set_lebesgue_integral lborel U ?P =
        (set_lebesgue_integral lborel U ?A -
          \<i> * set_lebesgue_integral lborel U ?D) / 2"
  proof -
    have diff_integral:
        "set_lebesgue_integral lborel U
            (\<lambda>x. ?A x - \<i> * ?D x) =
          set_lebesgue_integral lborel U ?A -
            set_lebesgue_integral lborel U (\<lambda>x. \<i> * ?D x)"
      by (rule set_integral_diff(2)[OF A_integrable iD_integrable])
    show ?thesis
      by (simp only: P_function set_integral_divide_zero diff_integral
            set_integral_mult_right)
  qed
  have Q_integral:
      "set_lebesgue_integral lborel U ?Q =
        (set_lebesgue_integral lborel U ?C -
          \<i> * set_lebesgue_integral lborel U ?B) / 2"
  proof -
    have diff_integral:
        "set_lebesgue_integral lborel U
            (\<lambda>x. ?C x - \<i> * ?B x) =
          set_lebesgue_integral lborel U ?C -
            set_lebesgue_integral lborel U (\<lambda>x. \<i> * ?B x)"
      by (rule set_integral_diff(2)[OF C_integrable iB_integrable])
    show ?thesis
      by (simp only: Q_function set_integral_divide_zero diff_integral
            set_integral_mult_right)
  qed
  have h0_integral:
      "set_lebesgue_integral lborel U ?P =
        - set_lebesgue_integral lborel U ?R"
    using h0 by blast
  have h1_integral:
      "set_lebesgue_integral lborel U ?Q =
        - set_lebesgue_integral lborel U ?S"
    using h1 by blast

  have two_is_zero: "(2 :: 2) = 0"
    by simp
  have energy_function: "?energy = (\<lambda>x. ?A x + ?B x)"
  proof (rule ext)
    fix x
    show "?energy x = ?A x + ?B x"
      unfolding slp_classical_gradient_def
      by (simp only: sum_2 two_is_zero vec_lambda_beta add.commute)
  qed
  have energy_integrable: "set_integrable lborel U ?energy"
    using set_integral_add(1)[OF A_integrable B_integrable]
    by (simp only: energy_function)
  have energy_integral:
      "set_lebesgue_integral lborel U ?energy =
        set_lebesgue_integral lborel U ?A +
          set_lebesgue_integral lborel U ?B"
    by (simp only: energy_function
          set_integral_add(2)[OF A_integrable B_integrable])

  have source_function:
      "?source = (\<lambda>x. (?R x + \<i> * ?S x) / 2)"
  proof (rule ext)
    fix x
    show "?source x = (?R x + \<i> * ?S x) / 2"
      unfolding slp_gradient_wirtinger_dbar_def
      by (simp only: distribute_sum mult.assoc)
  qed
  have source_sum_integrable:
      "set_integrable lborel U (\<lambda>x. (?R x + \<i> * ?S x) / 2)"
    by (rule set_integrable_divide,
        rule set_integral_add(1)[OF R_integrable iS_integrable])
  have source_integrable: "set_integrable lborel U ?source"
    using source_sum_integrable by (simp only: source_function)
  have source_integral:
      "set_lebesgue_integral lborel U ?source =
        (set_lebesgue_integral lborel U ?R +
          \<i> * set_lebesgue_integral lborel U ?S) / 2"
  proof -
    have sum_integral:
        "set_lebesgue_integral lborel U
            (\<lambda>x. ?R x + \<i> * ?S x) =
          set_lebesgue_integral lborel U ?R +
            set_lebesgue_integral lborel U (\<lambda>x. \<i> * ?S x)"
      by (rule set_integral_add(2)[OF R_integrable iS_integrable])
    show ?thesis
      by (simp only: source_function set_integral_divide_zero sum_integral
            set_integral_mult_right)
  qed

  have P_scaled:
      "2 * set_lebesgue_integral lborel U ?P =
        set_lebesgue_integral lborel U ?A -
          \<i> * set_lebesgue_integral lborel U ?D"
    using P_integral by (simp add: mult.commute)
  have Q_scaled:
      "2 * set_lebesgue_integral lborel U ?Q =
        set_lebesgue_integral lborel U ?C -
          \<i> * set_lebesgue_integral lborel U ?B"
    using Q_integral by (simp add: mult.commute)
  have energy_mixed:
      "set_lebesgue_integral lborel U ?A +
          set_lebesgue_integral lborel U ?B =
        (set_lebesgue_integral lborel U ?A -
          \<i> * set_lebesgue_integral lborel U ?D) +
        \<i> * (set_lebesgue_integral lborel U ?C -
          \<i> * set_lebesgue_integral lborel U ?B)"
    using cross_integral
    by (simp only: cross_integral right_diff_distrib
          complex_i_mult_minus diff_minus_eq_add add.assoc[symmetric]
          diff_add_cancel)
  have energy_scaled:
      "(set_lebesgue_integral lborel U ?A -
          \<i> * set_lebesgue_integral lborel U ?D) +
        \<i> * (set_lebesgue_integral lborel U ?C -
          \<i> * set_lebesgue_integral lborel U ?B) =
        2 * set_lebesgue_integral lborel U ?P +
          \<i> * (2 * set_lebesgue_integral lborel U ?Q)"
    by (simp only: P_scaled Q_scaled)
  have energy_factored:
      "2 * set_lebesgue_integral lborel U ?P +
          \<i> * (2 * set_lebesgue_integral lborel U ?Q) =
        2 * (set_lebesgue_integral lborel U ?P +
          \<i> * set_lebesgue_integral lborel U ?Q)"
    by (simp only: distrib_left mult_ac)
  have energy_via_h:
      "set_lebesgue_integral lborel U ?A +
          set_lebesgue_integral lborel U ?B =
        2 * (set_lebesgue_integral lborel U ?P +
          \<i> * set_lebesgue_integral lborel U ?Q)"
    by (simp only: energy_mixed energy_scaled energy_factored)
  have weak_substitution:
      "2 * (set_lebesgue_integral lborel U ?P +
          \<i> * set_lebesgue_integral lborel U ?Q) =
        2 * (- set_lebesgue_integral lborel U ?R +
          \<i> * (- set_lebesgue_integral lborel U ?S))"
    by (simp only: h0_integral h1_integral)
  have signed_half:
      "2 * (- set_lebesgue_integral lborel U ?R +
          \<i> * (- set_lebesgue_integral lborel U ?S)) =
        - 4 * ((set_lebesgue_integral lborel U ?R +
          \<i> * set_lebesgue_integral lborel U ?S) / 2)"
    by (simp add: algebra_simps)
  have final_integral:
      "set_lebesgue_integral lborel U ?energy =
        - 4 * set_lebesgue_integral lborel U ?source"
    by (simp only: energy_integral energy_via_h weak_substitution signed_half
          source_integral)
  show ?thesis
    using energy_integrable source_integrable final_integral by blast
qed

theorem slp_weak_dbar_partial_smooth_test_energy:
  assumes u_weak: "slp_weak_gradient_on U u Du"
    and projected_weak:
      "slp_weak_gradient_on U
        (slp_gradient_wirtinger_dbar Du) Dprojected"
    and phi_test: "slp_test_function_on U phi"
  shows
    "set_integrable lborel U
        (\<lambda>x. \<Sum>i\<in>UNIV.
          Du x $ i * slp_classical_gradient phi x $ i) \<and>
      set_integrable lborel U
        (\<lambda>x. slp_gradient_wirtinger_partial Dprojected x * phi x) \<and>
      set_lebesgue_integral lborel U
          (\<lambda>x. \<Sum>i\<in>UNIV.
            Du x $ i * slp_classical_gradient phi x $ i) =
        - 4 * set_lebesgue_integral lborel U
          (\<lambda>x. slp_gradient_wirtinger_partial Dprojected x * phi x)"
proof -
  let ?d0 = "slp_complex_partial_derivative phi 0"
  let ?d1 = "slp_complex_partial_derivative phi 1"
  let ?h = "slp_gradient_wirtinger_dbar Du"
  let ?q = "slp_gradient_wirtinger_partial Dprojected"
  let ?A = "\<lambda>x. Du x $ 0 * ?d0 x"
  let ?B = "\<lambda>x. Du x $ 1 * ?d1 x"
  let ?C = "\<lambda>x. Du x $ 0 * ?d1 x"
  let ?D = "\<lambda>x. Du x $ 1 * ?d0 x"
  let ?P = "\<lambda>x. ?h x * ?d0 x"
  let ?Q = "\<lambda>x. ?h x * ?d1 x"
  let ?R = "\<lambda>x. Dprojected x $ 0 * phi x"
  let ?S = "\<lambda>x. Dprojected x $ 1 * phi x"
  let ?energy = "\<lambda>x. \<Sum>i\<in>UNIV.
    Du x $ i * slp_classical_gradient phi x $ i"
  let ?source = "\<lambda>x. ?q x * phi x"

  have d0_test: "slp_test_function_on U ?d0"
    by (rule slp_test_function_on_partial_derivative[OF phi_test])
  have d1_test: "slp_test_function_on U ?d1"
    by (rule slp_test_function_on_partial_derivative[OF phi_test])
  have u_data:
      "\<And>psi i. slp_test_function_on U psi \<Longrightarrow>
        set_integrable lborel U
          (\<lambda>x. u x * slp_complex_partial_derivative psi i x) \<and>
        set_integrable lborel U (\<lambda>x. Du x $ i * psi x) \<and>
        set_lebesgue_integral lborel U
            (\<lambda>x. u x * slp_complex_partial_derivative psi i x) =
          - set_lebesgue_integral lborel U
            (\<lambda>x. Du x $ i * psi x)"
    using u_weak unfolding slp_weak_gradient_on_def by blast
  have h_data:
      "\<And>psi i. slp_test_function_on U psi \<Longrightarrow>
        set_integrable lborel U
          (\<lambda>x. ?h x * slp_complex_partial_derivative psi i x) \<and>
        set_integrable lborel U
          (\<lambda>x. Dprojected x $ i * psi x) \<and>
        set_lebesgue_integral lborel U
            (\<lambda>x. ?h x * slp_complex_partial_derivative psi i x) =
          - set_lebesgue_integral lborel U
            (\<lambda>x. Dprojected x $ i * psi x)"
    using projected_weak unfolding slp_weak_gradient_on_def by blast

  note u00 = u_data[OF d0_test, of 0]
  note u11 = u_data[OF d1_test, of 1]
  note u01 = u_data[OF d1_test, of 0]
  note u10 = u_data[OF d0_test, of 1]
  note h0 = h_data[OF phi_test, of 0]
  note h1 = h_data[OF phi_test, of 1]
  have A_integrable: "set_integrable lborel U ?A"
    using u00 by blast
  have B_integrable: "set_integrable lborel U ?B"
    using u11 by blast
  have C_integrable: "set_integrable lborel U ?C"
    using u01 by blast
  have D_integrable: "set_integrable lborel U ?D"
    using u10 by blast
  have P_integrable: "set_integrable lborel U ?P"
    using h0 by blast
  have Q_integrable: "set_integrable lborel U ?Q"
    using h1 by blast
  have R_integrable: "set_integrable lborel U ?R"
    using h0 by blast
  have S_integrable: "set_integrable lborel U ?S"
    using h1 by blast
  have iD_integrable: "set_integrable lborel U (\<lambda>x. \<i> * ?D x)"
    using D_integrable by simp
  have iB_integrable: "set_integrable lborel U (\<lambda>x. \<i> * ?B x)"
    using B_integrable by simp
  have iS_integrable: "set_integrable lborel U (\<lambda>x. \<i> * ?S x)"
    using S_integrable by simp

  have mixed_function:
      "(\<lambda>x. u x * slp_complex_partial_derivative ?d1 0 x) =
        (\<lambda>x. u x * slp_complex_partial_derivative ?d0 1 x)"
  proof (rule ext)
    fix x
    note mixed = slp_test_mixed_partial_commute[OF phi_test, of x]
    show "u x * slp_complex_partial_derivative ?d1 0 x =
        u x * slp_complex_partial_derivative ?d0 1 x"
      by (simp only: mixed)
  qed
  have cross_integral:
      "set_lebesgue_integral lborel U ?C =
        set_lebesgue_integral lborel U ?D"
  proof -
    have negative_cross:
        "- set_lebesgue_integral lborel U ?C =
          - set_lebesgue_integral lborel U ?D"
      using u01 u10 mixed_function by simp
    show ?thesis
      using negative_cross by simp
  qed

  have distribute_difference:
      "\<And>a b d :: complex.
        ((a - b) / 2) * d = (a * d - b * d) / 2"
    apply (simp only: divide_inverse right_diff_distrib)
    by (simp only: left_diff_distrib right_diff_distrib mult_ac)
  have distribute_sum:
      "\<And>a b d :: complex.
        ((a + b) / 2) * d = (a * d + b * d) / 2"
    apply (simp only: divide_inverse distrib_right)
    by (simp only: distrib_left distrib_right mult_ac)

  have P_function:
      "?P = (\<lambda>x. (?A x + \<i> * ?D x) / 2)"
  proof (rule ext)
    fix x
    show "?P x = (?A x + \<i> * ?D x) / 2"
      unfolding slp_gradient_wirtinger_dbar_def
      by (simp only: distribute_sum mult.assoc)
  qed
  have Q_function:
      "?Q = (\<lambda>x. (?C x + \<i> * ?B x) / 2)"
  proof (rule ext)
    fix x
    show "?Q x = (?C x + \<i> * ?B x) / 2"
      unfolding slp_gradient_wirtinger_dbar_def
      by (simp only: distribute_sum mult.assoc)
  qed
  have P_integral:
      "set_lebesgue_integral lborel U ?P =
        (set_lebesgue_integral lborel U ?A +
          \<i> * set_lebesgue_integral lborel U ?D) / 2"
  proof -
    have sum_integral:
        "set_lebesgue_integral lborel U
            (\<lambda>x. ?A x + \<i> * ?D x) =
          set_lebesgue_integral lborel U ?A +
            set_lebesgue_integral lborel U (\<lambda>x. \<i> * ?D x)"
      by (rule set_integral_add(2)[OF A_integrable iD_integrable])
    show ?thesis
      by (simp only: P_function set_integral_divide_zero sum_integral
            set_integral_mult_right)
  qed
  have Q_integral:
      "set_lebesgue_integral lborel U ?Q =
        (set_lebesgue_integral lborel U ?C +
          \<i> * set_lebesgue_integral lborel U ?B) / 2"
  proof -
    have sum_integral:
        "set_lebesgue_integral lborel U
            (\<lambda>x. ?C x + \<i> * ?B x) =
          set_lebesgue_integral lborel U ?C +
            set_lebesgue_integral lborel U (\<lambda>x. \<i> * ?B x)"
      by (rule set_integral_add(2)[OF C_integrable iB_integrable])
    show ?thesis
      by (simp only: Q_function set_integral_divide_zero sum_integral
            set_integral_mult_right)
  qed
  have h0_integral:
      "set_lebesgue_integral lborel U ?P =
        - set_lebesgue_integral lborel U ?R"
    using h0 by blast
  have h1_integral:
      "set_lebesgue_integral lborel U ?Q =
        - set_lebesgue_integral lborel U ?S"
    using h1 by blast

  have two_is_zero: "(2 :: 2) = 0"
    by simp
  have energy_function: "?energy = (\<lambda>x. ?A x + ?B x)"
  proof (rule ext)
    fix x
    show "?energy x = ?A x + ?B x"
      unfolding slp_classical_gradient_def
      by (simp only: sum_2 two_is_zero vec_lambda_beta add.commute)
  qed
  have energy_integrable: "set_integrable lborel U ?energy"
    using set_integral_add(1)[OF A_integrable B_integrable]
    by (simp only: energy_function)
  have energy_integral:
      "set_lebesgue_integral lborel U ?energy =
        set_lebesgue_integral lborel U ?A +
          set_lebesgue_integral lborel U ?B"
    by (simp only: energy_function
          set_integral_add(2)[OF A_integrable B_integrable])

  have source_function:
      "?source = (\<lambda>x. (?R x - \<i> * ?S x) / 2)"
  proof (rule ext)
    fix x
    show "?source x = (?R x - \<i> * ?S x) / 2"
      unfolding slp_gradient_wirtinger_partial_def
      by (simp only: distribute_difference mult.assoc)
  qed
  have source_difference_integrable:
      "set_integrable lborel U (\<lambda>x. (?R x - \<i> * ?S x) / 2)"
    by (rule set_integrable_divide,
        rule set_integral_diff(1)[OF R_integrable iS_integrable])
  have source_integrable: "set_integrable lborel U ?source"
    using source_difference_integrable by (simp only: source_function)
  have source_integral:
      "set_lebesgue_integral lborel U ?source =
        (set_lebesgue_integral lborel U ?R -
          \<i> * set_lebesgue_integral lborel U ?S) / 2"
  proof -
    have difference_integral:
        "set_lebesgue_integral lborel U
            (\<lambda>x. ?R x - \<i> * ?S x) =
          set_lebesgue_integral lborel U ?R -
            set_lebesgue_integral lborel U (\<lambda>x. \<i> * ?S x)"
      by (rule set_integral_diff(2)[OF R_integrable iS_integrable])
    show ?thesis
      by (simp only: source_function set_integral_divide_zero
            difference_integral set_integral_mult_right)
  qed

  have P_scaled:
      "2 * set_lebesgue_integral lborel U ?P =
        set_lebesgue_integral lborel U ?A +
          \<i> * set_lebesgue_integral lborel U ?D"
    using P_integral by (simp add: mult.commute)
  have Q_scaled:
      "2 * set_lebesgue_integral lborel U ?Q =
        set_lebesgue_integral lborel U ?C +
          \<i> * set_lebesgue_integral lborel U ?B"
    using Q_integral by (simp add: mult.commute)
  have energy_mixed:
      "set_lebesgue_integral lborel U ?A +
          set_lebesgue_integral lborel U ?B =
        (set_lebesgue_integral lborel U ?A +
          \<i> * set_lebesgue_integral lborel U ?D) -
        \<i> * (set_lebesgue_integral lborel U ?C +
          \<i> * set_lebesgue_integral lborel U ?B)"
    using cross_integral by (simp add: algebra_simps)
  have energy_scaled:
      "(set_lebesgue_integral lborel U ?A +
          \<i> * set_lebesgue_integral lborel U ?D) -
        \<i> * (set_lebesgue_integral lborel U ?C +
          \<i> * set_lebesgue_integral lborel U ?B) =
        2 * set_lebesgue_integral lborel U ?P -
          \<i> * (2 * set_lebesgue_integral lborel U ?Q)"
    by (simp only: P_scaled Q_scaled)
  have energy_factored:
      "2 * set_lebesgue_integral lborel U ?P -
          \<i> * (2 * set_lebesgue_integral lborel U ?Q) =
        2 * (set_lebesgue_integral lborel U ?P -
          \<i> * set_lebesgue_integral lborel U ?Q)"
    by (simp only: right_diff_distrib mult_ac)
  have energy_via_h:
      "set_lebesgue_integral lborel U ?A +
          set_lebesgue_integral lborel U ?B =
        2 * (set_lebesgue_integral lborel U ?P -
          \<i> * set_lebesgue_integral lborel U ?Q)"
    by (simp only: energy_mixed energy_scaled energy_factored)
  have weak_substitution:
      "2 * (set_lebesgue_integral lborel U ?P -
          \<i> * set_lebesgue_integral lborel U ?Q) =
        2 * (- set_lebesgue_integral lborel U ?R -
          \<i> * (- set_lebesgue_integral lborel U ?S))"
    by (simp only: h0_integral h1_integral)
  have signed_half:
      "2 * (- set_lebesgue_integral lborel U ?R -
          \<i> * (- set_lebesgue_integral lborel U ?S)) =
        - 4 * ((set_lebesgue_integral lborel U ?R -
          \<i> * set_lebesgue_integral lborel U ?S) / 2)"
    by (simp add: algebra_simps)
  have final_integral:
      "set_lebesgue_integral lborel U ?energy =
        - 4 * set_lebesgue_integral lborel U ?source"
    by (simp only: energy_integral energy_via_h weak_substitution signed_half
          source_integral)
  show ?thesis
    using energy_integrable source_integrable final_integral by blast
qed

end
