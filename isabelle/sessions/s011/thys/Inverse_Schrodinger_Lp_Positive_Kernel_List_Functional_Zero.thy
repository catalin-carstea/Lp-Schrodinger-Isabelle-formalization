theory Inverse_Schrodinger_Lp_Positive_Kernel_List_Functional_Zero
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_List"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Branch_Functional"
begin

section \<open>Empty positive kernel list as the zero-order branch functional\<close>

theorem slp_left_branch_positive_kernel_list_zero_functional:
  "(\<integral>\<^sup>+ terminal.
      slp_left_branch_positive_kernel_list R cutoff potential terminal_value []
          origin terminal *
        ennreal (norm (output_factor
          (slp_left_branch_output [] terminal)))
      \<partial>lborel) =
    slp_positive_branch_functional R cutoff potential
      (\<lambda>x. ennreal (norm (terminal_value x))) 0 origin
      (\<lambda>x. ennreal (norm (output_factor x)))"
  by (simp only: slp_left_branch_positive_kernel_list.simps
      slp_left_branch_output_Nil slp_positive_branch_functional.simps;
      simp add: ac_simps)

end
