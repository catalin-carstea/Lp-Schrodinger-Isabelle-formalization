theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Successor_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Successor_Shifted_Fubini"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Shifted_Reindex"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Index_List_Factored_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Bijective_Reindex_Leading_Pair_Integral"
begin

section \<open>Zero-based natural successor recursion\<close>

theorem slp_left_branch_oscillatory_graph_kernel_natural_Suc_fubini:
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
          ((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
           (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
          (\<lambda>(pos_tail, neg_tail).
            integral\<^sup>L (lborel :: slp_point measure)
              (\<lambda>terminal.
                slp_left_branch_oscillatory_graph_kernel_indices
                  [0..<n] tau center cutoff potential terminal_value
                  neg_head ((pos_tail, neg_tail), terminal)))
        \<partial>(lborel :: slp_point measure)
        \<partial>(lborel :: slp_point measure))"
proof -
  let ?M = "\<lambda>_::nat. (lborel :: slp_point measure)"
  let ?Heads =
    "(lborel :: slp_point measure) \<Otimes>\<^sub>M
      (lborel :: slp_point measure)"
  let ?ShiftedOne = "PiM {1..<Suc n} ?M"
  let ?ZeroOne = "PiM {..<n} ?M"
  let ?Shifted = "?ShiftedOne \<Otimes>\<^sub>M ?ShiftedOne"
  let ?Zero = "?ZeroOne \<Otimes>\<^sub>M ?ZeroOne"
  let ?coefficient = "\<lambda>pos_head neg_head.
    inverse (of_real (pi ^ 2)) *
      slp_center_kernel tau center pos_head *
      slp_center_kernel (- tau) center neg_head *
      slp_left_branch_complex_block cutoff potential origin pos_head neg_head"
  let ?shifted_terminal = "\<lambda>neg_head pos_tail neg_tail.
    integral\<^sup>L (lborel :: slp_point measure)
      (\<lambda>terminal.
        slp_left_branch_oscillatory_graph_kernel_indices [1..<Suc n] tau
          center cutoff potential terminal_value neg_head
          ((pos_tail, neg_tail), terminal))"
  let ?zero_terminal = "\<lambda>neg_head pos_tail neg_tail.
    integral\<^sup>L (lborel :: slp_point measure)
      (\<lambda>terminal.
        slp_left_branch_oscillatory_graph_kernel_indices [0..<n] tau center
          cutoff potential terminal_value neg_head
          ((pos_tail, neg_tail), terminal))"
  let ?shifted_factored =
    "\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
      ?coefficient pos_head neg_head *
        ?shifted_terminal neg_head pos_tail neg_tail"
  let ?zero_factored =
    "\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
      ?coefficient pos_head neg_head * ?zero_terminal neg_head pos_tail neg_tail"
  let ?shifted_head =
    "\<lambda>(pos_head, neg_head).
      ?coefficient pos_head neg_head *
        integral\<^sup>L ?Shifted
          (\<lambda>(pos_tail, neg_tail).
            ?shifted_terminal neg_head pos_tail neg_tail)"
  let ?zero_head =
    "\<lambda>(pos_head, neg_head).
      ?coefficient pos_head neg_head *
        integral\<^sup>L ?Zero
          (\<lambda>(pos_tail, neg_tail).
            ?zero_terminal neg_head pos_tail neg_tail)"
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
  interpret planar: product_sigma_finite ?M
    by (rule M_sigma)
  have finite_shifted: "finite {1..<Suc n}"
    by simp
  have finite_zero: "finite {..<n}"
    by simp
  have shifted_integrable:
      "integrable (?Heads \<Otimes>\<^sub>M ?Shifted) ?shifted_factored"
    by (rule slp_integrable_graph_indices_insert_head_factored_fresh_tail[
          OF M_sigma finite_shifted _ _ indices_integrable]; simp)
  have shifted_measurable:
      "?shifted_factored \<in> borel_measurable
        (?Heads \<Otimes>\<^sub>M ?Shifted)"
    by (rule borel_measurable_integrable[OF shifted_integrable])
  have mapped_factored:
      "(\<lambda>(leading, (positive, negative)).
          ?shifted_factored
            (leading,
              ((\<lambda>i\<in>{1..<Suc n}. positive (i - 1)),
               (\<lambda>i\<in>{1..<Suc n}. negative (i - 1))))) =
        ?zero_factored"
    by (rule ext)
      (simp only: split_beta' prod.collapse fst_conv snd_conv
        slp_left_graph_indices_shifted_predecessor)
  note integrable_reindex =
    planar.slp_integrable_leading_PiM_pair_reindex_bij_betw_iff[
      where L = ?Heads and I = "{1..<Suc n}" and K = "{..<n}"
        and t = "\<lambda>i::nat. i - 1" and f = ?shifted_factored,
      OF finite_shifted finite_zero slp_predecessor_bij_betw_shifted
        shifted_measurable]
  have zero_integrable:
      "integrable (?Heads \<Otimes>\<^sub>M ?Zero) ?zero_factored"
    using integrable_reindex shifted_integrable
    unfolding mapped_factored by simp
  note integral_reindex =
    planar.slp_integral_leading_PiM_pair_reindex_bij_betw[
      where L = ?Heads and I = "{1..<Suc n}" and K = "{..<n}"
        and t = "\<lambda>i::nat. i - 1" and f = ?shifted_factored,
      OF finite_shifted finite_zero slp_predecessor_bij_betw_shifted
        shifted_measurable]
  have global_reindex:
      "integral\<^sup>L (?Heads \<Otimes>\<^sub>M ?Shifted) ?shifted_factored =
        integral\<^sup>L (?Heads \<Otimes>\<^sub>M ?Zero) ?zero_factored"
    using integral_reindex unfolding mapped_factored by simp
  have shifted_one_sigma: "sigma_finite_measure ?ShiftedOne"
    by (rule planar.sigma_finite[OF finite_shifted])
  have zero_one_sigma: "sigma_finite_measure ?ZeroOne"
    by (rule planar.sigma_finite[OF finite_zero])
  interpret shifted_one: sigma_finite_measure ?ShiftedOne
    by (rule shifted_one_sigma)
  interpret zero_one: sigma_finite_measure ?ZeroOne
    by (rule zero_one_sigma)
  interpret shifted_pair: pair_sigma_finite ?ShiftedOne ?ShiftedOne ..
  interpret zero_pair: pair_sigma_finite ?ZeroOne ?ZeroOne ..
  have shifted_sigma: "sigma_finite_measure ?Shifted"
    by standard
  have zero_sigma: "sigma_finite_measure ?Zero"
    by standard
  interpret shifted: sigma_finite_measure ?Shifted
    by (rule shifted_sigma)
  interpret zero: sigma_finite_measure ?Zero
    by (rule zero_sigma)
  interpret head_shifted: pair_sigma_finite ?Heads ?Shifted ..
  interpret head_zero: pair_sigma_finite ?Heads ?Zero ..
  have shifted_split:
      "integral\<^sup>L (?Heads \<Otimes>\<^sub>M ?Shifted) ?shifted_factored =
        integral\<^sup>L ?Heads
          (\<lambda>heads. integral\<^sup>L ?Shifted
            (\<lambda>tails. ?shifted_factored (heads, tails)))"
    using head_shifted.integral_fst'[OF shifted_integrable]
    by simp
  have zero_split:
      "integral\<^sup>L (?Heads \<Otimes>\<^sub>M ?Zero) ?zero_factored =
        integral\<^sup>L ?Heads
          (\<lambda>heads. integral\<^sup>L ?Zero
            (\<lambda>tails. ?zero_factored (heads, tails)))"
    using head_zero.integral_fst'[OF zero_integrable]
    by simp
  have shifted_head_values:
      "(\<lambda>heads. integral\<^sup>L ?Shifted
          (\<lambda>tails. ?shifted_factored (heads, tails))) = ?shifted_head"
    by (rule ext)
      (simp only: split_beta' fst_conv snd_conv prod.collapse
        Bochner_Integration.integral_mult_right_zero)
  have zero_head_values:
      "(\<lambda>heads. integral\<^sup>L ?Zero
          (\<lambda>tails. ?zero_factored (heads, tails))) = ?zero_head"
    by (rule ext)
      (simp only: split_beta' fst_conv snd_conv prod.collapse
        Bochner_Integration.integral_mult_right_zero)
  have shifted_head_integrable: "integrable ?Heads ?shifted_head"
    using head_shifted.integrable_fst'[OF shifted_integrable]
    unfolding shifted_head_values .
  have zero_head_integrable: "integrable ?Heads ?zero_head"
    using head_zero.integrable_fst'[OF zero_integrable]
    unfolding zero_head_values .
  have shifted_head_split:
      "integral\<^sup>L ?Heads ?shifted_head =
        (\<integral>pos_head. \<integral>neg_head.
          ?shifted_head (pos_head, neg_head)
          \<partial>(lborel :: slp_point measure)
          \<partial>(lborel :: slp_point measure))"
    using lborel_pair.integral_fst'[OF shifted_head_integrable]
    by simp
  have zero_head_split:
      "integral\<^sup>L ?Heads ?zero_head =
        (\<integral>pos_head. \<integral>neg_head.
          ?zero_head (pos_head, neg_head)
          \<partial>(lborel :: slp_point measure)
          \<partial>(lborel :: slp_point measure))"
    using lborel_pair.integral_fst'[OF zero_head_integrable]
    by simp
  have nested_reindex:
      "(\<integral>pos_head. \<integral>neg_head.
          ?shifted_head (pos_head, neg_head)
          \<partial>(lborel :: slp_point measure)
          \<partial>(lborel :: slp_point measure)) =
        (\<integral>pos_head. \<integral>neg_head.
          ?zero_head (pos_head, neg_head)
          \<partial>(lborel :: slp_point measure)
          \<partial>(lborel :: slp_point measure))"
    using global_reindex shifted_split zero_split shifted_head_split
      zero_head_split
    unfolding shifted_head_values zero_head_values by simp
  note shifted_formula =
    slp_left_branch_oscillatory_graph_kernel_natural_Suc_fubini_shifted[
      OF graph_integrable]
  show ?thesis
    using shifted_formula nested_reindex by simp
qed

end
