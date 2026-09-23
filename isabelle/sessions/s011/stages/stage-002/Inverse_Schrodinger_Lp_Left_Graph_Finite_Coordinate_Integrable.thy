theory Inverse_Schrodinger_Lp_Left_Graph_Finite_Coordinate_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Terminal_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_Measurable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Positive_Kernel_Finite_Measurable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Inner_Mass"
begin

section \<open>Fixed-root integrability on the finite branch carrier\<close>

definition slp_left_branch_oscillatory_graph_kernel_fixed_root_finite ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow>
      (((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point)
        \<Rightarrow> complex"
where
  "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
      cutoff potential terminal_value origin branch_coordinates =
    slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
      terminal_value
      (slp_finite_branch_pair_list
        (\<lambda>i. fst (fst branch_coordinates) $ i)
        (\<lambda>i. snd (fst branch_coordinates) $ i))
      origin (snd branch_coordinates)"

lemma slp_left_branch_phase_param_measurable:
  fixes M :: "'a measure"
    and pair_functions :: "('a \<Rightarrow> slp_point \<times> slp_point) list"
  assumes terminal_measurable[measurable]:
      "terminal \<in> borel_measurable M"
    and pair_first_measurable:
      "\<And>pair. pair \<in> set pair_functions \<Longrightarrow>
        (\<lambda>x. fst (pair x)) \<in> borel_measurable M"
    and pair_second_measurable:
      "\<And>pair. pair \<in> set pair_functions \<Longrightarrow>
        (\<lambda>x. snd (pair x)) \<in> borel_measurable M"
  shows
    "(\<lambda>x. slp_left_branch_phase center
        (map (\<lambda>pair. pair x) pair_functions) (terminal x))
      \<in> borel_measurable M"
  using pair_first_measurable pair_second_measurable
proof (induction pair_functions)
  case Nil
  have center_phase_measurable:
      "slp_center_phase center \<in> borel_measurable borel"
    using slp_center_phase_measurable[of center]
    by (simp only: measurable_lborel2)
  have terminal_phase[measurable]:
      "(\<lambda>x. slp_center_phase center (terminal x))
        \<in> borel_measurable M"
    using measurable_compose[OF terminal_measurable
        center_phase_measurable]
    by (simp only: comp_def)
  show ?case
    unfolding list.map slp_left_branch_phase_def slp_branch_phase_def
    by measurable
next
  case (Cons pair pair_functions)
  have first_measurable[measurable]:
      "(\<lambda>x. fst (pair x)) \<in> borel_measurable M"
    by (rule Cons.prems(1)[of pair]) simp
  have second_measurable[measurable]:
      "(\<lambda>x. snd (pair x)) \<in> borel_measurable M"
    by (rule Cons.prems(2)[of pair]) simp
  have center_phase_measurable:
      "slp_center_phase center \<in> borel_measurable borel"
    using slp_center_phase_measurable[of center]
    by (simp only: measurable_lborel2)
  have first_phase[measurable]:
      "(\<lambda>x. slp_center_phase center (fst (pair x)))
        \<in> borel_measurable M"
    using measurable_compose[OF first_measurable
        center_phase_measurable]
    by (simp only: comp_def)
  have second_phase[measurable]:
      "(\<lambda>x. slp_center_phase center (snd (pair x)))
        \<in> borel_measurable M"
    using measurable_compose[OF second_measurable
        center_phase_measurable]
    by (simp only: comp_def)
  have tail_first:
      "\<And>tail_pair. tail_pair \<in> set pair_functions \<Longrightarrow>
        (\<lambda>x. fst (tail_pair x)) \<in> borel_measurable M"
    using Cons.prems(1) by simp
  have tail_second:
      "\<And>tail_pair. tail_pair \<in> set pair_functions \<Longrightarrow>
        (\<lambda>x. snd (tail_pair x)) \<in> borel_measurable M"
    using Cons.prems(2) by simp
  have tail_phase[measurable]:
      "(\<lambda>x. slp_left_branch_phase center
          (map (\<lambda>tail_pair. tail_pair x) pair_functions) (terminal x))
        \<in> borel_measurable M"
    by (rule Cons.IH[OF tail_first tail_second])
  have phase_step:
      "(\<lambda>x. slp_left_branch_phase center
          (map (\<lambda>entry. entry x) (pair # pair_functions))
          (terminal x)) =
        (\<lambda>x. slp_center_phase center (fst (pair x)) -
          slp_center_phase center (snd (pair x)) +
          slp_left_branch_phase center
            (map (\<lambda>tail_pair. tail_pair x) pair_functions)
            (terminal x))"
    by (rule ext)
      (simp only: list.map slp_left_branch_phase_def slp_branch_phase_def
        sum_list.Cons add.assoc)
  show ?case
    apply (subst phase_step)
    by measurable
qed

lemma slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "(slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
      cutoff potential terminal_value origin ::
        (((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point)
          \<Rightarrow> complex) \<in> borel_measurable lborel"
proof -
  let ?pair_functions =
    "map (\<lambda>k (branch_coordinates ::
        ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point).
      (fst (fst branch_coordinates) $ from_nat_into UNIV k,
       snd (fst branch_coordinates) $ from_nat_into UNIV k))
      [0..<CARD('i)]"
  have first_measurable:
      "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
        (\<lambda>x. fst (pair x)) \<in> borel_measurable lborel"
  proof -
    fix pair
    assume "pair \<in> set ?pair_functions"
    then obtain k where pair:
        "pair = (\<lambda>branch_coordinates.
          (fst (fst branch_coordinates) $ from_nat_into UNIV k,
           snd (fst branch_coordinates) $ from_nat_into UNIV k))"
      by (auto simp only: set_map image_iff)
    show "(\<lambda>x. fst (pair x)) \<in> borel_measurable lborel"
      unfolding pair
      apply (simp only: fst_conv measurable_lborel1 measurable_lborel2)
      by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  qed
  have second_measurable:
      "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
        (\<lambda>x. snd (pair x)) \<in> borel_measurable lborel"
  proof -
    fix pair
    assume "pair \<in> set ?pair_functions"
    then obtain k where pair:
        "pair = (\<lambda>branch_coordinates.
          (fst (fst branch_coordinates) $ from_nat_into UNIV k,
           snd (fst branch_coordinates) $ from_nat_into UNIV k))"
      by (auto simp only: set_map image_iff)
    show "(\<lambda>x. snd (pair x)) \<in> borel_measurable lborel"
      unfolding pair
      apply (simp only: snd_conv measurable_lborel1 measurable_lborel2)
      by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  qed
  have terminal_measurable:
      "(\<lambda>branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        snd branch_coordinates) \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have phase_measurable[measurable]:
      "(\<lambda>branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        slp_left_branch_phase center
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst branch_coordinates) $ i)
            (\<lambda>i. snd (fst branch_coordinates) $ i))
          (snd branch_coordinates)) \<in> borel_measurable lborel"
  proof -
    have parameterized:
        "(\<lambda>branch_coordinates.
          slp_left_branch_phase center
            (map (\<lambda>pair. pair branch_coordinates) ?pair_functions)
            (snd branch_coordinates)) \<in> borel_measurable lborel"
      by (rule slp_left_branch_phase_param_measurable[OF terminal_measurable
            first_measurable second_measurable])
    show ?thesis
      using parameterized
      unfolding slp_finite_branch_pair_list_def
      by (simp only: map_map comp_def)
  qed
  have origin_measurable:
      "(\<lambda>_ :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        origin) \<in> borel_measurable lborel"
    by measurable
  have pos_measurable:
      "\<And>i. (\<lambda>branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        fst (fst branch_coordinates) $ i) \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have neg_measurable:
      "\<And>i. (\<lambda>branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        snd (fst branch_coordinates) $ i) \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have raw_measurable[measurable]:
      "(\<lambda>branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        slp_left_branch_complex_kernel_list cutoff potential terminal_value
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst branch_coordinates) $ i)
            (\<lambda>i. snd (fst branch_coordinates) $ i))
          origin (snd branch_coordinates)) \<in> borel_measurable lborel"
    unfolding slp_finite_branch_pair_list_def
    by (rule slp_left_branch_complex_kernel_list_compose_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable
          origin_measurable pos_measurable neg_measurable
          terminal_measurable])
  show ?thesis
    unfolding slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_def
      slp_left_branch_oscillatory_graph_kernel_def
      slp_left_branch_complex_kernel_joint_def
      slp_left_branch_complex_kernel_finite_def
    by measurable
qed

lemma slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_norm:
  "norm (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
      cutoff potential terminal_value origin branch_coordinates) =
    norm (slp_left_branch_complex_kernel_joint cutoff potential terminal_value
      (origin, branch_coordinates))"
  unfolding slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_def
    slp_left_branch_complex_kernel_joint_def
    slp_left_branch_complex_kernel_finite_def
  apply (simp only: fst_conv snd_conv)
  by (rule slp_left_branch_oscillatory_graph_kernel_norm)

lemma slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_le_positive:
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "ennreal (norm
      (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential terminal_value origin branch_coordinates)) \<le>
      slp_left_branch_positive_kernel_joint (2 * B) cutoff potential
        terminal_value (origin, branch_coordinates)"
proof (cases
    "slp_left_branch_complex_kernel_joint cutoff potential terminal_value
      (origin, branch_coordinates) = 0")
  case True
  then show ?thesis
    by (simp only:
        slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_norm
        norm_zero ennreal_0 zero_le)
next
  assume raw_nonzero:
      "slp_left_branch_complex_kernel_joint cutoff potential terminal_value
        (origin, branch_coordinates) \<noteq> 0"
  have raw_eq:
      "slp_left_branch_complex_kernel_joint cutoff potential terminal_value
          (origin, branch_coordinates) =
        slp_left_branch_complex_kernel_finite cutoff potential terminal_value
          (\<lambda>i. fst (fst branch_coordinates) $ i)
          (\<lambda>i. snd (fst branch_coordinates) $ i)
          origin (snd branch_coordinates)"
    unfolding slp_left_branch_complex_kernel_joint_def
    by (simp only: fst_conv snd_conv)
  have finite_nonzero:
      "slp_left_branch_complex_kernel_finite cutoff potential terminal_value
        (\<lambda>i. fst (fst branch_coordinates) $ i)
        (\<lambda>i. snd (fst branch_coordinates) $ i)
        origin (snd branch_coordinates) \<noteq> 0"
  proof
    assume finite_zero:
        "slp_left_branch_complex_kernel_finite cutoff potential terminal_value
          (\<lambda>i. fst (fst branch_coordinates) $ i)
          (\<lambda>i. snd (fst branch_coordinates) $ i)
          origin (snd branch_coordinates) = 0"
    have joint_zero:
        "slp_left_branch_complex_kernel_joint cutoff potential terminal_value
          (origin, branch_coordinates) = 0"
      using raw_eq finite_zero by (rule HOL.trans)
    show False
      using raw_nonzero joint_zero by contradiction
  qed
  have finite_chain:
      "slp_left_branch_radius_chain_finite (2 * B)
        (\<lambda>i. fst (fst branch_coordinates) $ i)
        (\<lambda>i. snd (fst branch_coordinates) $ i)
        origin (snd branch_coordinates)"
    by (rule slp_left_branch_complex_kernel_finite_support_chain[OF
          B_nonnegative origin_bound cutoff_support potential_support
          finite_nonzero])
  have joint_chain:
      "slp_left_branch_radius_chain_joint (2 * B)
        (origin, branch_coordinates)"
    using finite_chain
    unfolding slp_left_branch_radius_chain_joint_def by simp
  have exact:
      "ennreal (norm
        (slp_left_branch_complex_kernel_joint cutoff potential terminal_value
          (origin, branch_coordinates))) =
        slp_left_branch_positive_kernel_joint (2 * B) cutoff potential
          terminal_value (origin, branch_coordinates)"
    by (rule slp_left_branch_complex_kernel_joint_positive_weight[OF
          joint_chain])
  show ?thesis
    by (simp only:
        slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_norm exact
        order_refl)
qed

theorem slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_integrable:
  fixes branch_dummy :: "'i::finite itself"
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and positive_inner_mass_finite:
      "slp_left_branch_positive_inner_mass_finite TYPE('i) (2 * B) cutoff
        potential terminal_value (\<lambda>_. 1) origin < \<infinity>"
  shows
    "integrable lborel
      (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential terminal_value origin ::
          (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point)
            \<Rightarrow> complex)"
proof (unfold integrable_iff_bounded, intro conjI)
  show
    "(slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
      cutoff potential terminal_value origin ::
        (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point)
          \<Rightarrow> complex) \<in> borel_measurable lborel"
    by (rule
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_measurable[OF
        cutoff_measurable potential_measurable terminal_value_measurable])
  have pointwise:
      "\<And>branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        ennreal (norm
          (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential terminal_value origin branch_coordinates))
        \<le> slp_left_branch_positive_kernel_joint (2 * B) cutoff potential
          terminal_value (origin, branch_coordinates)"
    by (rule
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_le_positive[OF
        B_nonnegative origin_bound cutoff_support potential_support])
  have mass_bound:
      "(\<integral>\<^sup>+ (branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point).
        ennreal (norm
          (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential terminal_value origin branch_coordinates))
        \<partial>lborel) \<le>
       (\<integral>\<^sup>+ (branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point).
        slp_left_branch_positive_kernel_joint (2 * B) cutoff potential
          terminal_value (origin, branch_coordinates) \<partial>lborel)"
  proof (rule nn_integral_mono_AE)
    show
      "AE (branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) in lborel.
        ennreal (norm
          (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential terminal_value origin branch_coordinates))
        \<le> slp_left_branch_positive_kernel_joint (2 * B) cutoff potential
          terminal_value (origin, branch_coordinates)"
      by (rule always_eventually) (rule allI, rule pointwise)
  qed
  have positive_mass:
      "(\<integral>\<^sup>+ (branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point).
        slp_left_branch_positive_kernel_joint (2 * B) cutoff potential
          terminal_value (origin, branch_coordinates) \<partial>lborel) <
        \<infinity>"
    using positive_inner_mass_finite
    unfolding slp_left_branch_positive_inner_mass_finite_def
    by (simp only: norm_one ennreal_1 mult_1_right)
  show
    "(\<integral>\<^sup>+ (branch_coordinates ::
        ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point).
      ennreal (norm
        (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
          cutoff potential terminal_value origin branch_coordinates))
      \<partial>lborel) < \<infinity>"
    by (rule le_less_trans[OF mass_bound positive_mass])
qed

end
