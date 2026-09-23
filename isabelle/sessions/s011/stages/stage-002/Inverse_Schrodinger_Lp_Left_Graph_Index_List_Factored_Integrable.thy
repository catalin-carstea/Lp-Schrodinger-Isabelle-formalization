theory Inverse_Schrodinger_Lp_Left_Graph_Index_List_Factored_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Index_List_Recursive_Fubini"
begin

section \<open>Factored integrability of the fresh-tail graph recursion\<close>

theorem slp_integrable_graph_indices_insert_head_factored_fresh_tail:
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
    "integrable
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
  let ?T = "PiM I M"
  let ?F = "PiM (insert i I) M"
  let ?MF = "?F \<Otimes>\<^sub>M ?F"
  let ?MAll = "?MF \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?Heads = "M i \<Otimes>\<^sub>M M i"
  let ?Tails = "?T \<Otimes>\<^sub>M ?T"
  let ?Interleaved = "?Heads \<Otimes>\<^sub>M ?Tails"
  let ?kernel =
    "slp_left_branch_oscillatory_graph_kernel_indices (i # indices) tau
      center cutoff potential terminal_value origin"
  let ?coefficient = "\<lambda>pos_head neg_head.
    inverse (of_real (pi ^ 2)) *
      slp_center_kernel tau center pos_head *
      slp_center_kernel (- tau) center neg_head *
      slp_left_branch_complex_block cutoff potential origin pos_head neg_head"
  let ?tail_terminal = "\<lambda>neg_head pos_tail neg_tail.
    integral\<^sup>L (lborel :: slp_point measure)
      (\<lambda>terminal.
        slp_left_branch_oscillatory_graph_kernel_indices indices tau center
          cutoff potential terminal_value neg_head
          ((pos_tail, neg_tail), terminal))"
  let ?factored =
    "\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
      ?coefficient pos_head neg_head *
        ?tail_terminal neg_head pos_tail neg_tail"
  interpret product: product_sigma_finite M
    by (rule M_sigma)
  have F_sigma: "sigma_finite_measure ?F"
    by (rule product.sigma_finite) (use finite_I in simp)
  interpret F: sigma_finite_measure ?F
    by (rule F_sigma)
  interpret family_pair: pair_sigma_finite ?F ?F ..
  have MF_sigma: "sigma_finite_measure ?MF"
    by standard
  interpret MF: sigma_finite_measure ?MF
    by (rule MF_sigma)
  interpret all_coordinates:
    pair_sigma_finite ?MF "(lborel :: slp_point measure)" ..
  have terminal_integrable:
      "integrable ?MF
        (\<lambda>families. integral\<^sup>L (lborel :: slp_point measure)
          (\<lambda>terminal. ?kernel (families, terminal)))"
    using all_coordinates.integrable_fst'[OF graph_integrable]
    by simp
  have transported_integrable:
      "integrable ?Interleaved
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          integral\<^sup>L (lborel :: slp_point measure)
            (\<lambda>terminal.
              ?kernel
                ((pos_tail(i := pos_head), neg_tail(i := neg_head)),
                  terminal)))"
    by (rule product.slp_integrable_inserted_pair_heads_tails[OF
          finite_I i_notin terminal_integrable])
  have transported_eq_factored:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          integral\<^sup>L (lborel :: slp_point measure)
            (\<lambda>terminal.
              ?kernel
                ((pos_tail(i := pos_head), neg_tail(i := neg_head)),
                  terminal))) =
        ?factored"
    by (rule ext)
      (simp only: slp_integral_graph_indices_Cons_terminal fun_upd_same
        slp_left_branch_oscillatory_graph_kernel_indices_update_irrelevant[OF
          i_notin_indices])
  show ?thesis
    using transported_integrable unfolding transported_eq_factored .
qed

end
