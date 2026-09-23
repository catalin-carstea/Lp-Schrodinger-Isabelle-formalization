theory Inverse_Schrodinger_Lp_Positive_Kernel_List_Fixed_Output_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Positive_Kernel_List_Fixed_Output"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Positive_Kernel_Measurable"
begin

section \<open>Parameter measurability of fixed-output positive list kernels\<close>

theorem slp_left_branch_positive_kernel_list_fixed_output_param_measurable:
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
    and output_measurable[measurable]:
      "output \<in> measurable M lborel"
    and pair_first_measurable:
      "\<And>pair. pair \<in> set pair_functions \<Longrightarrow>
        (\<lambda>x. fst (pair x)) \<in> measurable M lborel"
    and pair_second_measurable:
      "\<And>pair. pair \<in> set pair_functions \<Longrightarrow>
        (\<lambda>x. snd (pair x)) \<in> measurable M lborel"
  shows
    "(\<lambda>x. slp_left_branch_positive_kernel_list_fixed_output R cutoff
        potential terminal_value (map (\<lambda>pair. pair x) pair_functions)
        (origin x) (output x)) \<in> borel_measurable M"
proof -
  have branch_output_measurable:
      "(\<lambda>x. slp_left_branch_output
          (map (\<lambda>pair. pair x) pair_functions) 0)
        \<in> measurable M lborel"
    using pair_first_measurable pair_second_measurable
  proof (induction pair_functions)
    case Nil
    show ?case
      by simp
  next
    case (Cons pair pair_functions)
    have pair_first[measurable]:
        "(\<lambda>x. fst (pair x)) \<in> measurable M lborel"
      by (rule Cons.prems(1)[of pair]) simp
    have pair_second[measurable]:
        "(\<lambda>x. snd (pair x)) \<in> measurable M lborel"
      by (rule Cons.prems(2)[of pair]) simp
    have pair_first_borel[measurable]:
        "(\<lambda>x. fst (pair x)) \<in> borel_measurable M"
      using pair_first by (simp only: measurable_lborel1)
    have pair_second_borel[measurable]:
        "(\<lambda>x. snd (pair x)) \<in> borel_measurable M"
      using pair_second by (simp only: measurable_lborel1)
    have tail_first:
        "\<And>tail_pair. tail_pair \<in> set pair_functions \<Longrightarrow>
          (\<lambda>x. fst (tail_pair x)) \<in> measurable M lborel"
      using Cons.prems(1) by simp
    have tail_second:
        "\<And>tail_pair. tail_pair \<in> set pair_functions \<Longrightarrow>
          (\<lambda>x. snd (tail_pair x)) \<in> measurable M lborel"
      using Cons.prems(2) by simp
    have tail_output[measurable]:
        "(\<lambda>x. slp_left_branch_output
            (map (\<lambda>tail_pair. tail_pair x) pair_functions) 0)
          \<in> measurable M lborel"
      by (rule Cons.IH[OF tail_first tail_second])
    have tail_output_borel[measurable]:
        "(\<lambda>x. slp_left_branch_output
            (map (\<lambda>tail_pair. tail_pair x) pair_functions) 0)
          \<in> borel_measurable M"
      using tail_output by (simp only: measurable_lborel1)
    show ?case
      by (simp only: list.map slp_left_branch_output_Cons
          slp_branch_increment_def; measurable)
  qed
  have output_borel[measurable]:
      "output \<in> borel_measurable M"
    using output_measurable by (simp only: measurable_lborel1)
  have branch_output_borel[measurable]:
      "(\<lambda>x. slp_left_branch_output
          (map (\<lambda>pair. pair x) pair_functions) 0)
        \<in> borel_measurable M"
    using branch_output_measurable by (simp only: measurable_lborel1)
  have terminal_measurable:
      "(\<lambda>x. output x - slp_left_branch_output
          (map (\<lambda>pair. pair x) pair_functions) 0)
        \<in> measurable M lborel"
    by measurable
  show ?thesis
    unfolding slp_left_branch_positive_kernel_list_fixed_output_def
    by (rule slp_left_branch_positive_kernel_list_param_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable
          origin_measurable terminal_measurable pair_first_measurable
          pair_second_measurable])
qed

end
