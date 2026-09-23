theory Inverse_Schrodinger_Lp_Born_Left_Positive_Kernel_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Amplitude_Transport"
begin

section \<open>Measurability of parameterized positive branch kernels\<close>

lemma slp_left_branch_positive_kernel_list_param_measurable:
  fixes M :: "'a measure"
    and pair_functions :: "('a \<Rightarrow> slp_point \<times> slp_point) list"
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and origin_measurable[measurable]:
      "origin \<in> measurable M lborel"
    and terminal_measurable[measurable]:
      "terminal \<in> measurable M lborel"
    and pair_first_measurable:
      "\<And>pair. pair \<in> set pair_functions \<Longrightarrow>
        (\<lambda>x. fst (pair x)) \<in> measurable M lborel"
    and pair_second_measurable:
      "\<And>pair. pair \<in> set pair_functions \<Longrightarrow>
        (\<lambda>x. snd (pair x)) \<in> measurable M lborel"
  shows
    "(\<lambda>x. slp_left_branch_positive_kernel_list R cutoff potential
        terminal_value (map (\<lambda>pair. pair x) pair_functions)
        (origin x) (terminal x)) \<in> borel_measurable M"
  using origin_measurable pair_first_measurable pair_second_measurable
proof (induction pair_functions arbitrary: origin)
  case Nil
  have origin_borel[measurable]: "origin \<in> borel_measurable M"
    using Nil.prems(1) by (simp only: measurable_lborel1)
  have terminal_borel[measurable]: "terminal \<in> borel_measurable M"
    using terminal_measurable by (simp only: measurable_lborel1)
  have difference_measurable:
      "(\<lambda>x. origin x - terminal x) \<in> measurable M lborel"
    by measurable
  have kernel_measurable[measurable]:
      "(\<lambda>x. slp_localized_cauchy_kernel R
          (origin x - terminal x)) \<in> borel_measurable M"
    using measurable_comp[OF difference_measurable
      slp_localized_cauchy_kernel_borel_measurable]
    by (simp only: comp_def)
  have cutoff_terminal_measurable[measurable]:
      "(\<lambda>x. cutoff (terminal x)) \<in> borel_measurable M"
    using measurable_comp[OF terminal_measurable cutoff_measurable]
    by (simp only: comp_def)
  have terminal_value_terminal_measurable[measurable]:
      "(\<lambda>x. terminal_value (terminal x)) \<in> borel_measurable M"
    using measurable_comp[OF terminal_measurable terminal_value_measurable]
    by (simp only: comp_def)
  show ?case
    unfolding list.map slp_left_branch_positive_kernel_list.simps
    by measurable
next
  case (Cons pair pair_functions)
  have pair_first[measurable]:
      "(\<lambda>x. fst (pair x)) \<in> measurable M lborel"
    by (rule Cons.prems(2)[of pair]) simp
  have pair_second[measurable]:
      "(\<lambda>x. snd (pair x)) \<in> measurable M lborel"
    by (rule Cons.prems(3)[of pair]) simp
  have origin_borel[measurable]: "origin \<in> borel_measurable M"
    using Cons.prems(1) by (simp only: measurable_lborel1)
  have pair_first_borel[measurable]:
      "(\<lambda>x. fst (pair x)) \<in> borel_measurable M"
    using pair_first by (simp only: measurable_lborel1)
  have pair_second_borel[measurable]:
      "(\<lambda>x. snd (pair x)) \<in> borel_measurable M"
    using pair_second by (simp only: measurable_lborel1)
  have origin_pos_difference:
      "(\<lambda>x. origin x - fst (pair x)) \<in> measurable M lborel"
    by measurable
  have pos_neg_difference:
      "(\<lambda>x. fst (pair x) - snd (pair x))
        \<in> measurable M lborel"
    by measurable
  have origin_pos_kernel[measurable]:
      "(\<lambda>x. slp_localized_cauchy_kernel R
          (origin x - fst (pair x))) \<in> borel_measurable M"
    using measurable_comp[OF origin_pos_difference
      slp_localized_cauchy_kernel_borel_measurable]
    by (simp only: comp_def)
  have pos_neg_kernel[measurable]:
      "(\<lambda>x. slp_localized_cauchy_kernel R
          (fst (pair x) - snd (pair x))) \<in> borel_measurable M"
    using measurable_comp[OF pos_neg_difference
      slp_localized_cauchy_kernel_borel_measurable]
    by (simp only: comp_def)
  have cutoff_pos[measurable]:
      "(\<lambda>x. cutoff (fst (pair x))) \<in> borel_measurable M"
    using measurable_comp[OF pair_first cutoff_measurable]
    by (simp only: comp_def)
  have potential_neg[measurable]:
      "(\<lambda>x. potential (snd (pair x))) \<in> borel_measurable M"
    using measurable_comp[OF pair_second potential_measurable]
    by (simp only: comp_def)
  have tail_first:
      "\<And>tail_pair. tail_pair \<in> set pair_functions \<Longrightarrow>
        (\<lambda>x. fst (tail_pair x)) \<in> measurable M lborel"
    using Cons.prems(2) by simp
  have tail_second:
      "\<And>tail_pair. tail_pair \<in> set pair_functions \<Longrightarrow>
        (\<lambda>x. snd (tail_pair x)) \<in> measurable M lborel"
    using Cons.prems(3) by simp
  have tail_measurable[measurable]:
      "(\<lambda>x. slp_left_branch_positive_kernel_list R cutoff potential
          terminal_value (map (\<lambda>tail_pair. tail_pair x) pair_functions)
          (snd (pair x)) (terminal x)) \<in> borel_measurable M"
    by (rule Cons.IH[OF pair_second tail_first tail_second])
  show ?case
    unfolding list.map slp_left_branch_positive_kernel_list.simps
      slp_positive_branch_block_weight_def
    by measurable
qed

end
