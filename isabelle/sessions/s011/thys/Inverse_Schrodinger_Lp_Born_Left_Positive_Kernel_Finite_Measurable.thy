theory Inverse_Schrodinger_Lp_Born_Left_Positive_Kernel_Finite_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Positive_Kernel_Measurable"
begin

section \<open>Positive-kernel measurability on finite branch coordinates\<close>

theorem slp_left_branch_positive_kernel_joint_measurable:
  fixes branch_dummy :: "'i::finite itself"
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "(slp_left_branch_positive_kernel_joint R cutoff potential terminal_value ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
      \<in> borel_measurable lborel"
proof -
  let ?pair_functions =
    "map (\<lambda>k (coordinates :: 'i slp_left_branch_finite_coordinates).
      (fst (fst (snd coordinates)) $ from_nat_into UNIV k,
       snd (fst (snd coordinates)) $ from_nat_into UNIV k))
      [0..<CARD('i)]"
  have origin_measurable:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        fst coordinates) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have pos_measurable:
      "\<And>i. (\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        fst (fst (snd coordinates)) $ i) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have neg_measurable:
      "\<And>i. (\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        snd (fst (snd coordinates)) $ i) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have terminal_measurable:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        snd (snd coordinates)) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have pair_first:
      "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
        (\<lambda>coordinates. fst (pair coordinates))
          \<in> measurable lborel lborel"
  proof -
    fix pair
    assume pair_mem: "pair \<in> set ?pair_functions"
    from pair_mem have pair_image:
        "pair \<in>
          (\<lambda>k (coordinates :: 'i slp_left_branch_finite_coordinates).
            (fst (fst (snd coordinates)) $ from_nat_into UNIV k,
             snd (fst (snd coordinates)) $ from_nat_into UNIV k)) `
            set [0..<CARD('i)]"
      by (simp only: set_map)
    then obtain k where pair:
        "pair =
          (\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
            (fst (fst (snd coordinates)) $ from_nat_into UNIV k,
             snd (fst (snd coordinates)) $ from_nat_into UNIV k))"
      by (rule imageE)
    show "(\<lambda>coordinates. fst (pair coordinates))
        \<in> measurable lborel lborel"
      using pos_measurable[of "from_nat_into UNIV k"]
      by (simp only: pair fst_conv)
  qed
  have pair_second:
      "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
        (\<lambda>coordinates. snd (pair coordinates))
          \<in> measurable lborel lborel"
  proof -
    fix pair
    assume pair_mem: "pair \<in> set ?pair_functions"
    from pair_mem have pair_image:
        "pair \<in>
          (\<lambda>k (coordinates :: 'i slp_left_branch_finite_coordinates).
            (fst (fst (snd coordinates)) $ from_nat_into UNIV k,
             snd (fst (snd coordinates)) $ from_nat_into UNIV k)) `
            set [0..<CARD('i)]"
      by (simp only: set_map)
    then obtain k where pair:
        "pair =
          (\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
            (fst (fst (snd coordinates)) $ from_nat_into UNIV k,
             snd (fst (snd coordinates)) $ from_nat_into UNIV k))"
      by (rule imageE)
    show "(\<lambda>coordinates. snd (pair coordinates))
        \<in> measurable lborel lborel"
      using neg_measurable[of "from_nat_into UNIV k"]
      by (simp only: pair snd_conv)
  qed
  have parameterized:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
          (map (\<lambda>pair. pair coordinates) ?pair_functions)
          (fst coordinates) (snd (snd coordinates)))
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_list_param_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable
          origin_measurable terminal_measurable pair_first pair_second])
  show ?thesis
    using parameterized
    unfolding slp_left_branch_positive_kernel_joint_def
      slp_left_branch_positive_kernel_finite_def
      slp_finite_branch_pair_list_def
    by (simp only: map_map comp_def)
qed

end
