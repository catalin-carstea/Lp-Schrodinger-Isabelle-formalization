theory Inverse_Schrodinger_Lp_Cauchy_Weak_Derivative_Conjugate
  imports Inverse_Schrodinger_Lp_Cauchy_Weak_Derivative
begin

section \<open>Conjugation of whole-plane weak gradients\<close>

lemma slp_smooth_on_cnj:
  assumes phi_smooth: "smooth_on UNIV phi"
  shows "smooth_on UNIV (\<lambda>x. cnj (phi x))"
proof -
  have cnj_smooth: "smooth_on UNIV cnj"
    by (rule bounded_linear.smooth_on[OF bounded_linear_cnj])
  have "smooth_on UNIV (cnj \<circ> phi)"
    by (rule smooth_on_compose[OF cnj_smooth phi_smooth]) auto
  then show ?thesis
    by (simp add: o_def)
qed

lemma slp_test_function_on_cnj_iff [simp]:
  "slp_test_function_on U (\<lambda>x. cnj (phi x)) \<longleftrightarrow>
    slp_test_function_on U phi"
proof
  assume conjugated: "slp_test_function_on U (\<lambda>x. cnj (phi x))"
  have conjugated_smooth:
    "smooth_on UNIV (\<lambda>x. cnj (phi x))"
    using conjugated
    unfolding slp_test_function_on_def by blast
  have phi_smooth: "smooth_on UNIV phi"
    using slp_smooth_on_cnj[OF conjugated_smooth]
    by simp
  show "slp_test_function_on U phi"
    using conjugated phi_smooth
    unfolding slp_test_function_on_def by simp
next
  assume original: "slp_test_function_on U phi"
  have phi_smooth: "smooth_on UNIV phi"
    using original
    unfolding slp_test_function_on_def by blast
  show "slp_test_function_on U (\<lambda>x. cnj (phi x))"
    using original slp_smooth_on_cnj[OF phi_smooth]
    unfolding slp_test_function_on_def by simp
qed

lemma slp_complex_partial_derivative_cnj:
  assumes phi_smooth: "smooth_on UNIV phi"
  shows "slp_complex_partial_derivative (\<lambda>x. cnj (phi x)) i x =
    cnj (slp_complex_partial_derivative phi i x)"
proof -
  have phi_differentiable_on: "phi differentiable_on UNIV"
    by (rule smooth_on_imp_differentiable_on[OF phi_smooth]) simp
  have phi_differentiable: "phi differentiable at x"
    using phi_differentiable_on
    by (simp add: differentiable_on_def)
  have cnj_has_derivative:
    "(cnj has_derivative cnj) (at (phi x))"
    using bounded_linear.has_derivative[OF bounded_linear_cnj
        has_derivative_ident]
    by simp
  have cnj_differentiable: "cnj differentiable at (phi x)"
    by (rule differentiableI[OF cnj_has_derivative])
  have cnj_frechet:
    "frechet_derivative cnj (at (phi x)) = cnj"
    by (rule sym, rule frechet_derivative_at[OF cnj_has_derivative])
  have chain:
    "frechet_derivative (cnj \<circ> phi) (at x) =
      frechet_derivative cnj (at (phi x)) \<circ>
        frechet_derivative phi (at x)"
    by (rule frechet_derivative_compose[OF
          phi_differentiable cnj_differentiable])
  show ?thesis
    unfolding slp_complex_partial_derivative_def
    using chain cnj_frechet
    by (simp add: o_def)
qed

definition slp_conjugate_gradient ::
  "slp_gradient_field \<Rightarrow> slp_gradient_field"
where
  "slp_conjugate_gradient Du x = (\<chi> i. cnj (Du x $ i))"

lemma slp_weak_gradient_on_UNIV_cnj:
  assumes weak: "slp_weak_gradient_on UNIV u Du"
  shows "slp_weak_gradient_on UNIV
    (\<lambda>x. cnj (u x)) (slp_conjugate_gradient Du)"
proof (unfold slp_weak_gradient_on_def, intro allI impI)
  fix phi
  assume phi_test: "slp_test_function_on UNIV phi"
  fix i
  let ?psi = "\<lambda>x. cnj (phi x)"
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have psi_test: "slp_test_function_on UNIV ?psi"
    using phi_test by simp
  have source:
    "set_integrable lborel UNIV
        (\<lambda>x. u x * slp_complex_partial_derivative ?psi i x) \<and>
      set_integrable lborel UNIV (\<lambda>x. Du x $ i * ?psi x) \<and>
      set_lebesgue_integral lborel UNIV
          (\<lambda>x. u x * slp_complex_partial_derivative ?psi i x) =
        - set_lebesgue_integral lborel UNIV
          (\<lambda>x. Du x $ i * ?psi x)"
    using weak psi_test
    unfolding slp_weak_gradient_on_def by blast
  have first_integrand:
    "(\<lambda>x. cnj (u x) * slp_complex_partial_derivative phi i x) =
      (\<lambda>x. cnj
        (u x * slp_complex_partial_derivative ?psi i x))"
  proof (rule ext)
    fix y
    have derivative_conj:
      "slp_complex_partial_derivative (\<lambda>x. cnj (phi x)) i y =
        cnj (slp_complex_partial_derivative phi i y)"
      by (rule slp_complex_partial_derivative_cnj[OF phi_smooth])
    show "cnj (u y) * slp_complex_partial_derivative phi i y =
      cnj (u y * slp_complex_partial_derivative ?psi i y)"
      using derivative_conj by simp
  qed
  have second_integrand:
    "(\<lambda>x. slp_conjugate_gradient Du x $ i * phi x) =
      (\<lambda>x. cnj (Du x $ i * ?psi x))"
    by (rule ext) (simp add: slp_conjugate_gradient_def)
  have first_integrable:
    "set_integrable lborel UNIV
      (\<lambda>x. cnj (u x) * slp_complex_partial_derivative phi i x)"
  proof -
    have source_first:
      "complex_integrable lborel
        (\<lambda>x. u x * slp_complex_partial_derivative ?psi i x)"
      using source unfolding set_integrable_def by simp
    have conjugated_first:
      "complex_integrable lborel
        (\<lambda>x. cnj
          (u x * slp_complex_partial_derivative ?psi i x))"
      by (rule integrable_cnj[OF source_first])
    show ?thesis
      unfolding set_integrable_def
      using conjugated_first first_integrand by simp
  qed
  have second_integrable:
    "set_integrable lborel UNIV
      (\<lambda>x. slp_conjugate_gradient Du x $ i * phi x)"
  proof -
    have source_second:
      "complex_integrable lborel (\<lambda>x. Du x $ i * ?psi x)"
      using source unfolding set_integrable_def by simp
    have conjugated_second:
      "complex_integrable lborel
        (\<lambda>x. cnj (Du x $ i * ?psi x))"
      by (rule integrable_cnj[OF source_second])
    show ?thesis
      unfolding set_integrable_def
      using conjugated_second second_integrand by simp
  qed
  have integral_identity:
    "set_lebesgue_integral lborel UNIV
        (\<lambda>x. cnj (u x) * slp_complex_partial_derivative phi i x) =
      - set_lebesgue_integral lborel UNIV
        (\<lambda>x. slp_conjugate_gradient Du x $ i * phi x)"
  proof -
    have source_identity:
      "set_lebesgue_integral lborel UNIV
          (\<lambda>x. u x * slp_complex_partial_derivative ?psi i x) =
        - set_lebesgue_integral lborel UNIV
          (\<lambda>x. Du x $ i * ?psi x)"
      using source by blast
    have conjugated_identity:
      "set_lebesgue_integral lborel UNIV
          (\<lambda>x. cnj
            (u x * slp_complex_partial_derivative ?psi i x)) =
        - set_lebesgue_integral lborel UNIV
          (\<lambda>x. cnj (Du x $ i * ?psi x))"
    proof -
      have source_identity_integral:
        "lebesgue_integral lborel
            (\<lambda>x. u x * slp_complex_partial_derivative ?psi i x) =
          - lebesgue_integral lborel (\<lambda>x. Du x $ i * ?psi x)"
        using source_identity
        unfolding set_lebesgue_integral_def by simp
      have conjugated_identity_integral:
        "lebesgue_integral lborel
            (\<lambda>x. cnj
              (u x * slp_complex_partial_derivative ?psi i x)) =
          - lebesgue_integral lborel
            (\<lambda>x. cnj (Du x $ i * ?psi x))"
      proof -
        have left_cnj:
          "lebesgue_integral lborel
              (\<lambda>x. cnj
                (u x * slp_complex_partial_derivative ?psi i x)) =
            cnj (lebesgue_integral lborel
              (\<lambda>x. u x * slp_complex_partial_derivative ?psi i x))"
          by (rule Bochner_Integration.integral_cnj)
        have right_cnj:
          "lebesgue_integral lborel
              (\<lambda>x. cnj (Du x $ i * ?psi x)) =
            cnj (lebesgue_integral lborel
              (\<lambda>x. Du x $ i * ?psi x))"
          by (rule Bochner_Integration.integral_cnj)
        have cnj_neg:
          "\<And>z::complex. cnj (- z) = - cnj z"
          by simp
        show ?thesis
          by (simp only: left_cnj right_cnj source_identity_integral
              cnj_neg)
      qed
      show ?thesis
        using conjugated_identity_integral
        unfolding set_lebesgue_integral_def by simp
    qed
    show ?thesis
      using conjugated_identity
      by (simp only: first_integrand second_integrand)
  qed
  show "set_integrable lborel UNIV
        (\<lambda>x. cnj (u x) * slp_complex_partial_derivative phi i x) \<and>
      set_integrable lborel UNIV
        (\<lambda>x. slp_conjugate_gradient Du x $ i * phi x) \<and>
      set_lebesgue_integral lborel UNIV
          (\<lambda>x. cnj (u x) * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel UNIV
          (\<lambda>x. slp_conjugate_gradient Du x $ i * phi x)"
    by (rule conjI[OF first_integrable conjI[OF second_integrable
          integral_identity]])
qed

section \<open>Opposite Cauchy orientation\<close>

definition slp_partial_inverse_gradient ::
  "aim_planar_field \<Rightarrow> slp_gradient_field"
where
  "slp_partial_inverse_gradient f x =
    (\<chi> i. if i = 0 then
      f x + slp_opposite_beurling_transform f x
    else
      \<i> * (f x - slp_opposite_beurling_transform f x))"

lemma slp_partial_inverse_gradient_component_0 [simp]:
  "slp_partial_inverse_gradient f x $ 0 =
    f x + slp_opposite_beurling_transform f x"
  by (simp add: slp_partial_inverse_gradient_def)

lemma slp_partial_inverse_gradient_component_1 [simp]:
  "slp_partial_inverse_gradient f x $ 1 =
    \<i> * (f x - slp_opposite_beurling_transform f x)"
  by (simp add: slp_partial_inverse_gradient_def)

lemma slp_conjugate_dbar_gradient:
  "slp_conjugate_gradient
      (slp_dbar_inverse_gradient (\<lambda>x. cnj (f x))) =
    slp_partial_inverse_gradient f"
  by (simp add: fun_eq_iff vec_eq_iff slp_conjugate_gradient_def
      slp_dbar_inverse_gradient_def slp_partial_inverse_gradient_def
      slp_opposite_beurling_transform_def algebra_simps)

context aim_planar_cauchy_beurling_derivatives
begin

theorem slp_partial_inverse_weak_gradient:
  assumes p_lower: "1 < (p::real)"
    and f_lp: "aim_complex_lp_on_plane p f"
    and f_support: "bounded {x. f x \<noteq> 0}"
  shows "slp_weak_gradient_on UNIV
    (slp_partial_inverse f)
    (slp_partial_inverse_gradient f)"
proof -
  have conjugated_lp:
    "aim_complex_lp_on_plane p (\<lambda>x. cnj (f x))"
    using f_lp by simp
  have conjugated_support:
    "bounded {x. cnj (f x) \<noteq> 0}"
    using f_support by simp
  have source:
    "slp_weak_gradient_on UNIV
      (slp_dbar_inverse (\<lambda>x. cnj (f x)))
      (slp_dbar_inverse_gradient (\<lambda>x. cnj (f x)))"
    by (rule slp_dbar_inverse_weak_gradient[OF p_lower
          conjugated_lp conjugated_support])
  have conjugated_source:
    "slp_weak_gradient_on UNIV
      (\<lambda>z. cnj (slp_dbar_inverse (\<lambda>x. cnj (f x)) z))
      (slp_conjugate_gradient
        (slp_dbar_inverse_gradient (\<lambda>x. cnj (f x))))"
    by (rule slp_weak_gradient_on_UNIV_cnj[OF source])
  show ?thesis
    using conjugated_source
    by (simp only: slp_partial_inverse_via_dbar_conjugate
        slp_conjugate_dbar_gradient)
qed

end

end
