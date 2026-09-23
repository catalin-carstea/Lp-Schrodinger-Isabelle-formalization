theory Inverse_Schrodinger_Lp_Left_Graph_Index_List_Terminal_Recursion
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Index_List_Insert_Integral"
begin

section \<open>Terminal-integral recursion for a nonempty index list\<close>

theorem slp_integral_graph_indices_Cons_terminal:
  fixes positive negative :: "'i \<Rightarrow> slp_point"
  shows
    "integral\<^sup>L (lborel :: slp_point measure)
        (\<lambda>terminal.
          slp_left_branch_oscillatory_graph_kernel_indices (i # indices) tau
            center cutoff potential terminal_value origin
            ((positive, negative), terminal)) =
      (inverse (of_real (pi ^ 2)) *
        slp_center_kernel tau center (positive i) *
        slp_center_kernel (- tau) center (negative i) *
        slp_left_branch_complex_block cutoff potential origin (positive i)
          (negative i)) *
      integral\<^sup>L (lborel :: slp_point measure)
        (\<lambda>terminal.
          slp_left_branch_oscillatory_graph_kernel_indices indices tau center
            cutoff potential terminal_value (negative i)
            ((positive, negative), terminal))"
proof -
  let ?head =
    "inverse (of_real (pi ^ 2)) *
      slp_center_kernel tau center (positive i) *
      slp_center_kernel (- tau) center (negative i) *
      slp_left_branch_complex_block cutoff potential origin (positive i)
        (negative i)"
  have integrand:
      "(\<lambda>terminal.
          slp_left_branch_oscillatory_graph_kernel_indices (i # indices) tau
            center cutoff potential terminal_value origin
            ((positive, negative), terminal)) =
        (\<lambda>terminal. ?head *
          slp_left_branch_oscillatory_graph_kernel_indices indices tau center
            cutoff potential terminal_value (negative i)
            ((positive, negative), terminal))"
    by (rule ext)
      (simp only: slp_left_branch_oscillatory_graph_kernel_indices_Cons)
  show ?thesis
    unfolding integrand
    by (simp only: Bochner_Integration.integral_mult_right_zero)
qed

end
