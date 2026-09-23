theory Inverse_Schrodinger_Lp_Left_Recursive_Branch_Zero_Graph
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Recursive_Branch"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_List"
begin

section \<open>The order-zero analytic branch as its exact graph integral\<close>

definition slp_left_branch_zero_graph_integral ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_point \<Rightarrow> complex"
where
  "slp_left_branch_zero_graph_integral tau center cutoff potential
      terminal_value origin =
    integral\<^sup>L lborel
      (\<lambda>terminal.
        slp_center_kernel tau center terminal *
          slp_left_branch_complex_kernel_list cutoff potential terminal_value
            [] origin terminal)"

theorem slp_left_recursive_branch_zero_eq_graph_integral:
  "slp_left_recursive_branch 0 tau center cutoff potential terminal_value
      origin =
    slp_left_branch_zero_graph_integral tau center cutoff potential
      terminal_value origin"
proof -
  have rearranged_integrand:
      "(\<lambda>terminal.
          slp_center_kernel tau center terminal *
            (inverse (of_real pi) *
              slp_cauchy_kernel SLP_Partial_Inverse origin terminal *
              cutoff terminal * terminal_value terminal)) =
        (\<lambda>terminal.
          inverse (of_real pi) *
            ((slp_center_kernel tau center terminal *
                (cutoff terminal * terminal_value terminal)) *
              slp_cauchy_kernel SLP_Partial_Inverse origin terminal))"
    by (rule ext)
      (simp only: mult.assoc mult.commute mult.left_commute)
  show ?thesis
    unfolding slp_left_recursive_branch_zero_integral
      slp_left_branch_zero_graph_integral_def
      slp_left_branch_complex_kernel_list.simps
      slp_left_branch_complex_terminal_def
      rearranged_integrand
    by (simp only: Bochner_Integration.integral_mult_right_zero)
qed

end
