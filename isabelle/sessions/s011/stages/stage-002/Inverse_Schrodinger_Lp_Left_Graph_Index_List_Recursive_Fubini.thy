theory Inverse_Schrodinger_Lp_Left_Graph_Index_List_Recursive_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Index_List_Fresh_Tail_Recursion"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Pair_Insert_Integrable"
begin

section \<open>Outer complex Fubini for the fresh-tail graph recursion\<close>

theorem slp_integral_graph_indices_insert_head_recursive_fubini:
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
      (\<integral>pos_head. \<integral>neg_head.
        (inverse (of_real (pi ^ 2)) *
          slp_center_kernel tau center pos_head *
          slp_center_kernel (- tau) center neg_head *
          slp_left_branch_complex_block cutoff potential origin pos_head
            neg_head) *
        integral\<^sup>L ((PiM I M) \<Otimes>\<^sub>M (PiM I M))
          (\<lambda>(pos_tail, neg_tail).
            integral\<^sup>L (lborel :: slp_point measure)
              (\<lambda>terminal.
                slp_left_branch_oscillatory_graph_kernel_indices indices tau
                  center cutoff potential terminal_value neg_head
                  ((pos_tail, neg_tail), terminal)))
        \<partial>M i \<partial>M i)"
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
  have T_sigma: "sigma_finite_measure ?T"
    by (rule product.sigma_finite[OF finite_I])
  interpret F: sigma_finite_measure ?F
    by (rule F_sigma)
  interpret family_pair: pair_sigma_finite ?F ?F ..
  have MF_sigma: "sigma_finite_measure ?MF"
    by standard
  interpret MF: sigma_finite_measure ?MF
    by (rule MF_sigma)
  interpret all_coordinates:
    pair_sigma_finite ?MF "(lborel :: slp_point measure)" ..
  interpret head_pair: pair_sigma_finite "M i" "M i" ..
  interpret T: sigma_finite_measure ?T
    by (rule T_sigma)
  interpret tail_pair: pair_sigma_finite ?T ?T ..
  have Heads_sigma: "sigma_finite_measure ?Heads"
    by standard
  have Tails_sigma: "sigma_finite_measure ?Tails"
    by standard
  interpret Heads: sigma_finite_measure ?Heads
    by (rule Heads_sigma)
  interpret Tails: sigma_finite_measure ?Tails
    by (rule Tails_sigma)
  interpret head_tail: pair_sigma_finite ?Heads ?Tails ..
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
  have factored_integrable: "integrable ?Interleaved ?factored"
    using transported_integrable unfolding transported_eq_factored .
  have source_to_factored:
      "integral\<^sup>L ?MAll ?kernel =
        integral\<^sup>L ?Interleaved ?factored"
    by (rule slp_integral_graph_indices_insert_head_factored_fresh_tail[OF
          M_sigma finite_I i_notin i_notin_indices graph_integrable])
  have head_tail_split:
      "integral\<^sup>L ?Interleaved ?factored =
        integral\<^sup>L ?Heads
          (\<lambda>heads. integral\<^sup>L ?Tails
            (\<lambda>tails. ?factored (heads, tails)))"
    using head_tail.integral_fst'[OF factored_integrable]
    by simp
  have head_integrable:
      "integrable ?Heads
        (\<lambda>heads. integral\<^sup>L ?Tails
          (\<lambda>tails. ?factored (heads, tails)))"
    by (rule head_tail.integrable_fst'[OF factored_integrable])
  let ?head_value =
    "\<lambda>(pos_head, neg_head).
      ?coefficient pos_head neg_head *
        integral\<^sup>L ?Tails
          (\<lambda>(pos_tail, neg_tail).
            ?tail_terminal neg_head pos_tail neg_tail)"
  have head_values:
      "(\<lambda>heads. integral\<^sup>L ?Tails
          (\<lambda>tails. ?factored (heads, tails))) =
        ?head_value"
    by (rule ext)
      (simp only: split_beta' fst_conv snd_conv prod.collapse
        Bochner_Integration.integral_mult_right_zero)
  have head_value_integrable: "integrable ?Heads ?head_value"
    using head_integrable unfolding head_values .
  have head_split:
      "integral\<^sup>L ?Heads ?head_value =
        (\<integral>pos_head. \<integral>neg_head.
          ?head_value (pos_head, neg_head) \<partial>M i \<partial>M i)"
    using head_pair.integral_fst'[OF head_value_integrable]
    by simp
  show ?thesis
    using source_to_factored head_tail_split head_split
    unfolding head_values by simp
qed

end
