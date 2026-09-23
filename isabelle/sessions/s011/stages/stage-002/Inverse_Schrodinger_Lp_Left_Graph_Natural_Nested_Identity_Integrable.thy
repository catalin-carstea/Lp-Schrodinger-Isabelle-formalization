theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Nested_Identity_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Recursive_Branch_Identity"
begin

section \<open>Terminal-generic nested-to-flat identity\<close>

theorem slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_nested_integrable:
  fixes B tau :: real
    and center origin :: slp_point
    and cutoff potential terminal_value :: "slp_point \<Rightarrow> complex"
  assumes origin_bound: "norm origin \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and graph_integrable:
      "\<And>m root. norm root \<le> B \<Longrightarrow>
        integrable
          (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))
              \<Otimes>\<^sub>M
            (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))))
              \<Otimes>\<^sub>M (lborel :: slp_point measure))
          (slp_left_branch_oscillatory_graph_kernel_natural m tau center
            cutoff potential terminal_value root)"
  shows
    "integral\<^sup>L
        (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
          (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
            \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential terminal_value origin) =
      slp_left_branch_nested_graph_functional n tau center cutoff potential
        terminal_value origin"
using origin_bound
proof (induction n arbitrary: origin)
  case 0
  show ?case
    apply (rule slp_left_branch_oscillatory_graph_kernel_natural_zero_integral)
    apply (rule graph_integrable)
    by (fact "0.prems")
next
  case (Suc n)
  let ?M = "\<lambda>_::nat. (lborel :: slp_point measure)"
  let ?MP = "PiM {..<n} ?M"
  let ?MF = "?MP \<Otimes>\<^sub>M ?MP"
  let ?Tail = "\<lambda>neg.
    integral\<^sup>L
      (?MF \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential terminal_value neg)"
  let ?Split = "\<lambda>neg.
    integral\<^sup>L ?MF (\<lambda>(pos_tail, neg_tail).
      integral\<^sup>L (lborel :: slp_point measure) (\<lambda>terminal.
        slp_left_branch_oscillatory_graph_kernel_indices [0..<n] tau center
          cutoff potential terminal_value neg
          ((pos_tail, neg_tail), terminal)))"
  let ?Nested = "\<lambda>neg.
    slp_left_branch_nested_graph_functional n tau center cutoff potential
      terminal_value neg"
  let ?block = "\<lambda>pos neg.
    slp_left_branch_complex_block cutoff potential origin pos neg"
  let ?raw = "\<lambda>pos neg.
    slp_center_kernel tau center pos *
      slp_center_kernel (- tau) center neg *
      ?block pos neg * ?Nested neg"
  have current_integrable:
      "integrable
        (((PiM {..<Suc n} ?M) \<Otimes>\<^sub>M (PiM {..<Suc n} ?M))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_natural (Suc n) tau center
          cutoff potential terminal_value origin)"
    apply (rule graph_integrable)
    by (fact Suc.prems)
  interpret product: product_sigma_finite ?M
    by standard
  have MP_sigma: "sigma_finite_measure ?MP"
    by (rule product.sigma_finite) simp
  interpret MP: sigma_finite_measure ?MP
    by (rule MP_sigma)
  interpret family_pair: pair_sigma_finite ?MP ?MP ..
  have MF_sigma: "sigma_finite_measure ?MF"
    by standard
  interpret MF: sigma_finite_measure ?MF
    by (rule MF_sigma)
  interpret all_coordinates:
    pair_sigma_finite ?MF "(lborel :: slp_point measure)" ..
  have split_nested_product:
      "?block pos neg * ?Split neg = ?block pos neg * ?Nested neg"
    for pos neg
  proof (cases "norm neg \<le> B")
    case True
    have coordinate_map:
        "map (\<lambda>k.
            (slp_left_branch_natural_value n pos_tail k,
             slp_left_branch_natural_value n neg_tail k)) [0..<n] =
          map (\<lambda>k. (pos_tail k, neg_tail k)) [0..<n]"
      for pos_tail neg_tail
      apply (rule map_cong)
       apply (rule refl)
      unfolding slp_left_branch_natural_value_def
      by simp
    have natural_indices:
        "slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
            potential terminal_value neg ((pos_tail, neg_tail), terminal) =
          slp_left_branch_oscillatory_graph_kernel_indices [0..<n] tau center
            cutoff potential terminal_value neg
            ((pos_tail, neg_tail), terminal)"
      for pos_tail neg_tail terminal
      unfolding slp_left_branch_oscillatory_graph_kernel_natural_def
        slp_left_branch_oscillatory_graph_kernel_indices_def
      by (simp only: prod.sel coordinate_map)
    have natural_indices_pair:
        "slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
            potential terminal_value neg (families, terminal) =
          slp_left_branch_oscillatory_graph_kernel_indices [0..<n] tau center
            cutoff potential terminal_value neg
            ((fst families, snd families), terminal)"
      for families terminal
      using natural_indices[of "fst families" "snd families" terminal]
      by simp
    have tail_integrable:
        "integrable
          (?MF \<Otimes>\<^sub>M (lborel :: slp_point measure))
          (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
            potential terminal_value neg)"
      by (rule graph_integrable[OF True])
    have terminal_split:
        "integral\<^sup>L ?MF (\<lambda>families.
            integral\<^sup>L (lborel :: slp_point measure) (\<lambda>terminal.
              slp_left_branch_oscillatory_graph_kernel_natural n tau center
                cutoff potential terminal_value neg (families, terminal))) =
          ?Tail neg"
      using all_coordinates.integral_fst'[OF tail_integrable]
      by simp
    have fubini: "?Tail neg = ?Split neg"
      using terminal_split[symmetric]
      by (simp only: natural_indices_pair split_beta')
    show ?thesis
      using fubini Suc.IH[OF True] by simp
  next
    case False
    have potential_zero: "potential neg = 0"
    proof (rule ccontr)
      assume "potential neg \<noteq> 0"
      then have "norm neg \<le> B"
        by (rule potential_support)
      with False show False
        by simp
    qed
    show ?thesis
      unfolding slp_left_branch_complex_block_def
      by (simp add: potential_zero)
  qed
  have scalarized:
      "(\<integral>pos. \<integral>neg.
          (inverse (of_real (pi ^ 2)) *
            slp_center_kernel tau center pos *
            slp_center_kernel (- tau) center neg * ?block pos neg) *
          ?Split neg
          \<partial>(lborel :: slp_point measure)
          \<partial>(lborel :: slp_point measure)) =
        inverse (of_real (pi ^ 2)) *
          integral\<^sup>L (lborel :: slp_point measure) (\<lambda>pos.
            integral\<^sup>L (lborel :: slp_point measure) (\<lambda>neg.
              ?raw pos neg))"
    by (simp only: mult.assoc split_nested_product
        Bochner_Integration.integral_mult_right_zero)
  note recurrence =
    slp_left_branch_oscillatory_graph_kernel_natural_Suc_fubini[
      OF current_integrable]
  show ?case
    apply (subst recurrence)
    unfolding slp_left_branch_nested_graph_functional.simps
    using scalarized
    by simp
qed

end
