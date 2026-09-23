theory Inverse_Schrodinger_Lp_Center_Average_Smooth_Convergence
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Test_Fourier_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Leading_Functional"
begin

section \<open>Smooth center-average convergence and the leading term\<close>

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_center_average_smooth_uniform_limit:
  fixes phi :: slp_scalar_field
  assumes phi_test: "slp_test_function_on UNIV phi"
  shows "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi at_top"
proof -
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_l2: "aim_complex_lp_on_plane 2 phi"
    by (rule slp_test_function_aim_complex_lp_on_plane[OF _ phi_test]) simp
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have phi_continuous: "continuous_on UNIV phi"
    by (rule smooth_on_imp_continuous_on[OF phi_smooth])
  show ?thesis
    by (rule slp_center_average_uniform_limit_fourier_l1[OF
        phi_integrable phi_l2 slp_test_fourier_integrable[OF phi_test] phi_continuous])
qed

theorem slp_center_average_smooth_pairing_limit:
  fixes F phi :: slp_scalar_field
  assumes F_integrable: "integrable lborel F"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "((\<lambda>tau. integral\<^sup>L lborel
      (\<lambda>c. F c * slp_center_average tau phi c))
    \<longlongrightarrow> integral\<^sup>L lborel (\<lambda>c. F c * phi c)) at_top"
  by (rule slp_center_average_pairing_convergence[OF F_integrable
      slp_test_function_integrable_bounded(1)[OF phi_test]
      slp_test_function_integrable_bounded(2)[OF phi_test]
      slp_center_average_smooth_uniform_limit[OF phi_test]])

theorem slp_leading_functional_smooth_limit:
  fixes Q phi :: slp_scalar_field
  assumes Q_integrable: "integrable lborel Q"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "((\<lambda>tau. slp_leading_functional tau phi Q)
    \<longlongrightarrow> integral\<^sup>L lborel (\<lambda>z. Q z * phi z)) at_top"
proof -
  have identity: "slp_leading_functional tau phi Q =
      integral\<^sup>L lborel (\<lambda>z. Q z * slp_center_average tau phi z)" for tau
    by (rule slp_leading_functional_transpose[OF
        slp_test_function_integrable_bounded(1)[OF phi_test] Q_integrable])
  show ?thesis
    unfolding identity
    by (rule slp_center_average_smooth_pairing_limit[OF Q_integrable phi_test])
qed

end

end
