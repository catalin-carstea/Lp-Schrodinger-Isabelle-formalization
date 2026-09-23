theory Inverse_Schrodinger_Lp_Left_Graph_Index_List_Fresh_Tail_Recursion
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Index_List_Update_Invariant"
begin

section \<open>Head recursion with unmodified tail families\<close>

theorem slp_integral_graph_indices_insert_head_factored_fresh_tail:
  fixes M :: "'i \<Rightarrow> slp_point measure"
  assumes M_sigma: "product_sigma_finite M"
    and finite_I: "finite I"
    and i_notin: "i \<notin> I"
    and i_notin_indices: "i \<notin> set indices"
    and graph_integrable:
      "integrable
        (((PiM (insert i I) M) \<Otimes>\<^sub>M (PiM (insert i I) M))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_indices (i # indices) tau
          center cutoff potential terminal_value origin)"
  shows
    "integral\<^sup>L
        (((PiM (insert i I) M) \<Otimes>\<^sub>M (PiM (insert i I) M))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_indices (i # indices) tau
          center cutoff potential terminal_value origin) =
      integral\<^sup>L
        ((M i \<Otimes>\<^sub>M M i) \<Otimes>\<^sub>M
          ((PiM I M) \<Otimes>\<^sub>M (PiM I M)))
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          (inverse (of_real (pi ^ 2)) *
            slp_center_kernel tau center pos_head *
            slp_center_kernel (- tau) center neg_head *
            slp_left_branch_complex_block cutoff potential origin pos_head
              neg_head) *
          integral\<^sup>L (lborel :: slp_point measure)
            (\<lambda>terminal.
              slp_left_branch_oscillatory_graph_kernel_indices indices tau
                center cutoff potential terminal_value neg_head
                ((pos_tail, neg_tail), terminal)))"
proof -
  note factored = slp_integral_graph_indices_insert_head_factored[OF
    M_sigma finite_I i_notin graph_integrable]
  have integrands:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          (inverse (of_real (pi ^ 2)) *
            slp_center_kernel tau center pos_head *
            slp_center_kernel (- tau) center neg_head *
            slp_left_branch_complex_block cutoff potential origin pos_head
              neg_head) *
          integral\<^sup>L (lborel :: slp_point measure)
            (\<lambda>terminal.
              slp_left_branch_oscillatory_graph_kernel_indices indices tau
                center cutoff potential terminal_value neg_head
                ((pos_tail(i := pos_head), neg_tail(i := neg_head)),
                  terminal))) =
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          (inverse (of_real (pi ^ 2)) *
            slp_center_kernel tau center pos_head *
            slp_center_kernel (- tau) center neg_head *
            slp_left_branch_complex_block cutoff potential origin pos_head
              neg_head) *
          integral\<^sup>L (lborel :: slp_point measure)
            (\<lambda>terminal.
              slp_left_branch_oscillatory_graph_kernel_indices indices tau
                center cutoff potential terminal_value neg_head
                ((pos_tail, neg_tail), terminal)))"
    by (rule ext)
      (simp only:
        slp_left_branch_oscillatory_graph_kernel_indices_update_irrelevant[OF
          i_notin_indices])
  show ?thesis
    using factored unfolding integrands .
qed

end
