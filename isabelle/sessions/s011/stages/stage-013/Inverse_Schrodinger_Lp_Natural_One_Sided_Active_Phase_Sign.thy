theory Inverse_Schrodinger_Lp_Natural_One_Sided_Active_Phase_Sign
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Active_Phase"
begin

section \<open>Sign reversal for the active one-sided quadratic phase\<close>

theorem slp_left_branch_residual_first_negative_decay_measure_sign:
  fixes M :: "'c measure"
    and pairs :: "'c \<Rightarrow> (slp_point \<times> slp_point) list"
    and lam terminal :: "'c \<Rightarrow> slp_point"
    and F :: "'c \<Rightarrow> slp_point \<Rightarrow> complex"
  assumes stationary: "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and M_sigma: "sigma_finite_measure M"
    and lam_measurable: "lam \<in> borel_measurable M"
    and output_measurable:
      "(\<lambda>c. slp_left_branch_output (pairs c) (terminal c))
        \<in> borel_measurable M"
    and residual_measurable:
      "(\<lambda>c. slp_left_branch_residual (pairs c) (terminal c))
        \<in> borel_measurable M"
    and F_integrable: "integrable (M \<Otimes>\<^sub>M lborel) (case_prod F)"
  shows "((\<lambda>omega::real. integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
    (\<lambda>(c,eta). exp (\<i> * of_real ((- omega) *
      slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) * F c eta))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?G = "\<lambda>c eta. cnj (F c eta)"
  have G_integrable:
      "integrable (M \<Otimes>\<^sub>M lborel) (case_prod ?G)"
  proof -
    have conjugate_integrable:
        "integrable (M \<Otimes>\<^sub>M lborel)
          (\<lambda>z. cnj (case_prod F z))"
      by (rule integrable_cnj[OF F_integrable])
    show ?thesis
      using conjugate_integrable by (simp only: split_beta')
  qed
  have positive_decay:
      "((\<lambda>omega::real. integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
        (\<lambda>(c,eta). exp (\<i> * of_real (omega *
          slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) *
          ?G c eta)) \<longlongrightarrow> 0) at_top"
    by (rule slp_left_branch_residual_first_negative_decay_measure[
      OF stationary density M_sigma lam_measurable output_measurable
        residual_measurable G_integrable])
  let ?positive = "\<lambda>omega::real. integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
    (\<lambda>(c,eta). exp (\<i> * of_real (omega *
      slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) *
      ?G c eta)"
  let ?negative = "\<lambda>omega::real. integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
    (\<lambda>(c,eta). exp (\<i> * of_real ((- omega) *
      slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) * F c eta)"
  have integral_conjugate: "?negative omega = cnj (?positive omega)" for omega
  proof -
    have pointwise:
        "exp (\<i> * of_real ((- omega) *
            slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) *
            F c eta =
          cnj (exp (\<i> * of_real (omega *
            slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) *
            ?G c eta)" for c eta
      by (simp add: exp_cnj algebra_simps)
    have integrand_eq:
        "(\<lambda>(c,eta). exp (\<i> * of_real ((- omega) *
            slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) *
            F c eta) =
          (\<lambda>z. cnj ((case z of (c,eta) \<Rightarrow>
            exp (\<i> * of_real (omega *
              slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) *
            ?G c eta)))"
      by (rule ext) (simp only: pointwise split_beta')
    have negative_eq:
        "?negative omega = integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
          (\<lambda>z. cnj ((case z of (c,eta) \<Rightarrow>
            exp (\<i> * of_real (omega *
              slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) *
            ?G c eta)))"
      by (simp only: integrand_eq)
    have move_conjugate:
        "integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
          (\<lambda>z. cnj ((case z of (c,eta) \<Rightarrow>
            exp (\<i> * of_real (omega *
              slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) *
            ?G c eta))) = cnj (?positive omega)"
      by (rule Bochner_Integration.integral_cnj)
    show ?thesis using negative_eq move_conjugate by simp
  qed
  have conjugate_decay:
      "((\<lambda>omega. cnj (?positive omega)) \<longlongrightarrow> cnj 0) at_top"
    by (rule tendsto_cnj[OF positive_decay])
  show ?thesis
    using conjugate_decay
    by (simp only: integral_conjugate; simp)
qed

end
