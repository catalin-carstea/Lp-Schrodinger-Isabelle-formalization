theory Inverse_Schrodinger_Lp_Left_Graph_Index_List_Update_Invariant
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Index_List_Head_Recursion"
begin

section \<open>Tail-list invariance under an irrelevant coordinate update\<close>

theorem slp_left_branch_oscillatory_graph_kernel_indices_update_irrelevant:
  fixes positive negative :: "'i \<Rightarrow> slp_point"
  assumes i_notin: "i \<notin> set indices"
  shows
    "slp_left_branch_oscillatory_graph_kernel_indices indices tau center cutoff
        potential terminal_value origin
        ((positive(i := pos_head), negative(i := neg_head)), terminal) =
      slp_left_branch_oscillatory_graph_kernel_indices indices tau center cutoff
        potential terminal_value origin ((positive, negative), terminal)"
proof -
  have pair_map:
      "map (\<lambda>j. ((positive(i := pos_head)) j,
          (negative(i := neg_head)) j)) indices =
        map (\<lambda>j. (positive j, negative j)) indices"
  proof (rule map_cong)
    show "indices = indices"
      by (rule refl)
  next
    fix j
    assume "j \<in> set indices"
    with i_notin have "j \<noteq> i"
      by blast
    then show
      "((positive(i := pos_head)) j, (negative(i := neg_head)) j) =
        (positive j, negative j)"
      by simp
  qed
  show ?thesis
    unfolding slp_left_branch_oscillatory_graph_kernel_indices_def
    by (simp only: fst_conv snd_conv pair_map)
qed

end
