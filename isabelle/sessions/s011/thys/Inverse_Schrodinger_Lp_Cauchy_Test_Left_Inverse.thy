theory Inverse_Schrodinger_Lp_Cauchy_Test_Left_Inverse
  imports
    Inverse_Schrodinger_Lp_Weak_Product_Wirtinger
    Inverse_Schrodinger_Lp_Cauchy_Weak_Derivative_Conjugate
    "Paper_ISLP_AIM_Planar_Cauchy_Test_Left_Inverse.AIM_Planar_Cauchy_Test_Left_Inverse_Interface"
begin

section \<open>Compact-smooth Cauchy left inverses\<close>

lemma aim_planar_classical_dbar_cnj:
  assumes phi_smooth: "smooth_on UNIV phi"
  shows "aim_planar_classical_dbar (\<lambda>x. cnj (phi x)) =
    (\<lambda>x. cnj (slp_classical_wirtinger_partial phi x))"
  unfolding aim_planar_classical_dbar_def
    slp_classical_wirtinger_partial_def
  by (rule ext)
    (simp add: slp_complex_partial_derivative_cnj[OF phi_smooth])

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_dbar_inverse_classical_dbar_left_inverse:
  assumes phi_test: "slp_test_function_on UNIV phi"
  shows "slp_dbar_inverse (aim_planar_classical_dbar phi) = phi"
proof -
  have source:
    "aim_planar_cauchy_transform (aim_planar_classical_dbar phi) = phi"
    using aim_planar_cauchy_test_left_inverse phi_test
    unfolding aim_planar_cauchy_test_left_inverse_claim_def by blast
  show ?thesis
    using source by (simp only: slp_dbar_inverse_eq_aim)
qed

theorem slp_partial_inverse_classical_partial_left_inverse:
  assumes phi_test: "slp_test_function_on UNIV phi"
  shows "slp_partial_inverse (slp_classical_wirtinger_partial phi) = phi"
proof -
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have conjugated_test:
    "slp_test_function_on UNIV (\<lambda>x. cnj (phi x))"
    using phi_test by simp
  have conjugated_derivative:
    "(\<lambda>x. cnj (slp_classical_wirtinger_partial phi x)) =
      aim_planar_classical_dbar (\<lambda>x. cnj (phi x))"
    using aim_planar_classical_dbar_cnj[OF phi_smooth] by simp
  have source:
    "slp_dbar_inverse
        (aim_planar_classical_dbar (\<lambda>x. cnj (phi x))) =
      (\<lambda>x. cnj (phi x))"
    by (rule slp_dbar_inverse_classical_dbar_left_inverse[OF
          conjugated_test])
  have conjugated_source:
    "slp_dbar_inverse
        (\<lambda>x. cnj (slp_classical_wirtinger_partial phi x)) =
      (\<lambda>x. cnj (phi x))"
    using source conjugated_derivative by simp
  show ?thesis
    using conjugated_source
    by (simp only: slp_partial_inverse_via_dbar_conjugate
        complex_cnj_cnj)
qed

end

end
