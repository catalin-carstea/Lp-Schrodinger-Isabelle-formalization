theory Inverse_Schrodinger_Lp_Left_Graph_Index_List_Kernel
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Pair_Insert_Integral"
begin

section \<open>Arbitrary index-list presentation of the left graph kernel\<close>

definition slp_left_branch_oscillatory_graph_kernel_indices ::
    "'i list \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow>
      ((('i \<Rightarrow> slp_point) \<times> ('i \<Rightarrow> slp_point)) \<times>
        slp_point) \<Rightarrow> complex"
where
  "slp_left_branch_oscillatory_graph_kernel_indices indices tau center cutoff
      potential terminal_value origin coordinates =
    slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
      terminal_value
      (map (\<lambda>i. (fst (fst coordinates) i, snd (fst coordinates) i))
        indices)
      origin (snd coordinates)"

theorem slp_left_branch_oscillatory_graph_kernel_indices_Cons:
  fixes positive negative :: "'i \<Rightarrow> slp_point"
    and terminal :: slp_point
  shows
    "slp_left_branch_oscillatory_graph_kernel_indices (i # indices) tau center
      cutoff potential terminal_value origin ((positive, negative), terminal) =
    inverse (of_real (pi ^ 2)) *
      slp_center_kernel tau center (positive i) *
      slp_center_kernel (- tau) center (negative i) *
      slp_left_branch_complex_block cutoff potential origin (positive i)
        (negative i) *
      slp_left_branch_oscillatory_graph_kernel_indices indices tau center
        cutoff potential terminal_value (negative i)
        ((positive, negative), terminal)"
  unfolding slp_left_branch_oscillatory_graph_kernel_indices_def
  by (simp only: list.map slp_left_branch_oscillatory_graph_kernel_Cons
      prod.sel)

end
