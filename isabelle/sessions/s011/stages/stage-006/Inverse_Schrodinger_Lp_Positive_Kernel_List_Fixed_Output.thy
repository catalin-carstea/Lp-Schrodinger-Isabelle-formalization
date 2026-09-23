theory Inverse_Schrodinger_Lp_Positive_Kernel_List_Fixed_Output
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_List"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Output_Density"
begin

section \<open>Positive list kernels at a prescribed branch output\<close>

definition slp_left_branch_positive_kernel_list_fixed_output ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
      terminal_value pairs origin output =
    slp_left_branch_positive_kernel_list R cutoff potential terminal_value
      pairs origin (output - slp_left_branch_output pairs 0)"

lemma slp_left_branch_positive_kernel_list_fixed_output_Nil:
  "slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
      terminal_value [] origin output =
    slp_positive_output_density R cutoff potential
      (\<lambda>x. ennreal (norm (terminal_value x))) 0 origin output"
  unfolding slp_left_branch_positive_kernel_list_fixed_output_def
  by simp

theorem slp_left_branch_positive_kernel_list_fixed_output_Cons:
  "slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
        terminal_value (pair # pairs) origin output =
    ennreal (inverse (pi ^ 2)) *
      slp_positive_branch_block_weight R cutoff potential origin
        (fst pair) (snd pair) *
      slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
        terminal_value pairs (snd pair) (output - fst pair + snd pair)"
  unfolding slp_left_branch_positive_kernel_list_fixed_output_def
    slp_left_branch_output_Cons slp_branch_increment_def
  by (simp add: algebra_simps)

end
