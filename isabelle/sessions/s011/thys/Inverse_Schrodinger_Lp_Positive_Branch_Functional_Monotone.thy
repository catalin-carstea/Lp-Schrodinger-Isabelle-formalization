theory Inverse_Schrodinger_Lp_Positive_Branch_Functional_Monotone
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Branch_Functional"
begin

section \<open>Monotonicity of the positive branch functional\<close>

theorem slp_positive_branch_functional_mono:
  assumes terminal_weight_le:
      "\<And>x. terminal_weight x \<le> terminal_majorant x"
    and test_le: "\<And>x. test x \<le> test_majorant x"
  shows
    "slp_positive_branch_functional R cutoff potential terminal_weight n
        origin test \<le>
      slp_positive_branch_functional R cutoff potential terminal_majorant n
        origin test_majorant"
  using test_le
  by (induction n arbitrary: origin test test_majorant)
    (auto intro!: nn_integral_mono mult_mono mult_left_mono
      terminal_weight_le simp: slp_positive_branch_functional.simps)

end
