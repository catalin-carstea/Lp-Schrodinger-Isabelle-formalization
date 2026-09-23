theory Inverse_Schrodinger_Lp_Positive_Kernel_List_Functional_Suc
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Kernel_List_Functional_Zero"
begin

section \<open>Successor decomposition of the positive list integrand\<close>

theorem slp_left_branch_positive_kernel_list_Suc_integrand:
  "slp_left_branch_positive_kernel_list R cutoff potential terminal_value
        (pair # pairs) origin terminal *
      ennreal (norm (output_factor
        (slp_left_branch_output (pair # pairs) terminal))) =
    ennreal (inverse (pi ^ 2)) *
      slp_positive_branch_block_weight R cutoff potential origin
        (fst pair) (snd pair) *
      (slp_left_branch_positive_kernel_list R cutoff potential terminal_value
          pairs (snd pair) terminal *
        ennreal (norm (output_factor
          (slp_left_branch_output pairs terminal + fst pair - snd pair))))"
  by (simp only: slp_left_branch_positive_kernel_list.simps
      slp_left_branch_output_Cons slp_branch_increment_def;
      simp add: algebra_simps)

end
