theory Inverse_Schrodinger_Lp_Right_Recursive_Branch
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Recursive_Branch"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Conjugation"
begin

section \<open>The exact recursive analytic right Born branch\<close>

primrec slp_right_recursive_branch ::
    "nat \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_right_recursive_branch 0 tau center cutoff potential terminal_value =
    slp_dbar_psi_inverse (- tau) center
      (\<lambda>terminal. cutoff terminal * terminal_value terminal)"
| "slp_right_recursive_branch (Suc n) tau center cutoff potential
      terminal_value =
    slp_dbar_psi_inverse (- tau) center
      (\<lambda>pos. cutoff pos *
        slp_partial_psi_inverse (- tau) center
          (\<lambda>neg. potential neg *
            slp_right_recursive_branch n tau center cutoff potential
              terminal_value neg)
          pos)"

lemma slp_right_recursive_branch_zero_integral:
  "slp_right_recursive_branch 0 tau center cutoff potential terminal_value
      origin =
    inverse (of_real pi) *
      integral\<^sup>L lborel
        (\<lambda>terminal.
          (slp_center_kernel tau center terminal *
            (cutoff terminal * terminal_value terminal)) *
          slp_cauchy_kernel SLP_Dbar_Inverse origin terminal)"
  unfolding slp_right_recursive_branch.simps
    slp_dbar_psi_inverse_def slp_cauchy_transform_def
    slp_cauchy_integrand_def slp_oscillatory_modulation_def
  by simp

lemma slp_right_recursive_branch_Suc_integral:
  "slp_right_recursive_branch (Suc n) tau center cutoff potential
      terminal_value origin =
    inverse (of_real pi) *
      integral\<^sup>L lborel
        (\<lambda>pos.
          (slp_center_kernel tau center pos *
            (cutoff pos *
              (inverse (of_real pi) *
                integral\<^sup>L lborel
                  (\<lambda>neg.
                    (slp_center_kernel (- tau) center neg *
                      (potential neg *
                        slp_right_recursive_branch n tau center cutoff
                          potential terminal_value neg)) *
                    slp_cauchy_kernel SLP_Partial_Inverse pos neg)))) *
          slp_cauchy_kernel SLP_Dbar_Inverse origin pos)"
  unfolding slp_right_recursive_branch.simps
    slp_partial_psi_inverse_def slp_dbar_psi_inverse_def
    slp_cauchy_transform_def slp_cauchy_integrand_def
    slp_oscillatory_modulation_def
  by simp

theorem slp_left_recursive_branch_conjugate_eq_right:
  "cnj (slp_left_recursive_branch n (- tau) center
      (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
      (\<lambda>x. cnj (terminal_value x)) origin) =
    slp_right_recursive_branch n tau center cutoff potential terminal_value
      origin"
proof (induction n arbitrary: origin)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

end
