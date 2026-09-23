theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Successor_Shifted_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Index_List_Recursive_Fubini"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Coordinate_Integrable"
begin

section \<open>Natural successor recursion with an explicit shifted tail\<close>

theorem slp_left_branch_oscillatory_graph_kernel_natural_Suc_fubini_shifted:
  assumes graph_integrable:
    "integrable
      (((PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure)))
          \<Otimes>\<^sub>M
        (PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_left_branch_oscillatory_graph_kernel_natural (Suc n) tau center
        cutoff potential terminal_value origin)"
  shows
    "integral\<^sup>L
        (((PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
          (PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))))
            \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_natural (Suc n) tau center
          cutoff potential terminal_value origin) =
      (\<integral>pos_head. \<integral>neg_head.
        (inverse (of_real (pi ^ 2)) *
          slp_center_kernel tau center pos_head *
          slp_center_kernel (- tau) center neg_head *
          slp_left_branch_complex_block cutoff potential origin pos_head
            neg_head) *
        integral\<^sup>L
          ((PiM {1..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
           (PiM {1..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))))
          (\<lambda>(pos_tail, neg_tail).
            integral\<^sup>L (lborel :: slp_point measure)
              (\<lambda>terminal.
                slp_left_branch_oscillatory_graph_kernel_indices
                  [1..<Suc n] tau center cutoff potential terminal_value
                  neg_head ((pos_tail, neg_tail), terminal)))
        \<partial>(lborel :: slp_point measure)
        \<partial>(lborel :: slp_point measure))"
proof -
  let ?M = "\<lambda>_::nat. (lborel :: slp_point measure)"
  have interval_insert: "insert 0 {1..<Suc n} = {..<Suc n}"
    by auto
  have interval_list: "0 # [1..<Suc n] = [0..<Suc n]"
    by (induction n) simp_all
  have natural_pair_map:
      "\<And>positive negative.
        map (\<lambda>k.
          (slp_left_branch_natural_value (Suc n) positive k,
           slp_left_branch_natural_value (Suc n) negative k))
          [0..<Suc n] =
        map (\<lambda>k. (positive k, negative k)) [0..<Suc n]"
    by (simp add: slp_left_branch_natural_value_def)
  have kernel_eq:
      "slp_left_branch_oscillatory_graph_kernel_indices [0..<Suc n] tau
          center cutoff potential terminal_value origin =
        slp_left_branch_oscillatory_graph_kernel_natural (Suc n) tau center
          cutoff potential terminal_value origin"
    unfolding slp_left_branch_oscillatory_graph_kernel_indices_def
      slp_left_branch_oscillatory_graph_kernel_natural_def
    by (rule ext) (simp only: natural_pair_map)
  have indices_integrable:
      "integrable
        (((PiM (insert 0 {1..<Suc n}) ?M) \<Otimes>\<^sub>M
          (PiM (insert 0 {1..<Suc n}) ?M)) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_indices
          (0 # [1..<Suc n]) tau center cutoff potential terminal_value origin)"
    using graph_integrable
    unfolding interval_insert interval_list kernel_eq .
  have M_sigma: "product_sigma_finite ?M"
    by standard
  have finite_tail: "finite {1..<Suc n}"
    by simp
  have zero_not_tail: "0 \<notin> {1..<Suc n}"
    by simp
  have zero_not_indices: "0 \<notin> set [1..<Suc n]"
    by simp
  note raw = slp_integral_graph_indices_insert_head_recursive_fubini[
    where M = ?M and I = "{1..<Suc n}" and i = 0
      and indices = "[1..<Suc n]" and tau = tau and center = center
      and cutoff = cutoff and potential = potential
      and terminal_value = terminal_value and origin = origin,
    OF M_sigma finite_tail zero_not_tail zero_not_indices indices_integrable]
  show ?thesis
    using raw
    unfolding interval_insert interval_list kernel_eq
    by simp
qed

end
