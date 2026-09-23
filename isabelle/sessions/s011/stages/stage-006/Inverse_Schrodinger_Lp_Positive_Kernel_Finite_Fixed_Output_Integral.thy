theory Inverse_Schrodinger_Lp_Positive_Kernel_Finite_Fixed_Output_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Positive_Kernel_List_Fixed_Output_Natural_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Two_Finite_Vectors_Natural_NN_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Natural_Branch_Pair_List"
begin

section \<open>Finite Cartesian fixed-output positive-kernel integrals\<close>

theorem slp_left_branch_positive_kernel_finite_fixed_output_integral:
  fixes branch_dummy :: "'i::finite itself"
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "nn_integral
        (lborel :: ((slp_point^'i) \<times> (slp_point^'i)) measure)
        (\<lambda>(pos, neg).
          slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
            terminal_value
            (slp_finite_branch_pair_list (($) pos) (($) neg)) origin target) =
      slp_positive_output_density R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) CARD('i) origin target"
proof -
  let ?V = "(lborel :: ((slp_point^'i) \<times> (slp_point^'i)) measure)"
  let ?N = "PiM {..<CARD('i)}
    (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?U = "?N \<Otimes>\<^sub>M ?N"
  let ?F = "\<lambda>coordinates::(slp_point^'i) \<times> (slp_point^'i).
    slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
      terminal_value
      (slp_finite_branch_pair_list (($) (fst coordinates))
        (($) (snd coordinates)))
      origin target"
  let ?H = "\<lambda>(pos, neg).
    slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
      terminal_value (map (\<lambda>k. (pos k, neg k)) [0..<CARD('i)])
      origin target"
  let ?cartesian_pair_functions =
    "map (\<lambda>k (coordinates :: (slp_point^'i) \<times> (slp_point^'i)).
      (fst coordinates $ from_nat_into UNIV k,
       snd coordinates $ from_nat_into UNIV k)) [0..<CARD('i)]"
  have cartesian_pos_measurable:
      "\<And>i. (\<lambda>coordinates :: (slp_point^'i) \<times> (slp_point^'i).
        fst coordinates $ i) \<in> measurable ?V lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have cartesian_neg_measurable:
      "\<And>i. (\<lambda>coordinates :: (slp_point^'i) \<times> (slp_point^'i).
        snd coordinates $ i) \<in> measurable ?V lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have cartesian_pair_first:
      "\<And>pair. pair \<in> set ?cartesian_pair_functions \<Longrightarrow>
        (\<lambda>x. fst (pair x)) \<in> measurable ?V lborel"
  proof -
    fix pair
    assume "pair \<in> set ?cartesian_pair_functions"
    then obtain k where pair:
        "pair = (\<lambda>coordinates :: (slp_point^'i) \<times> (slp_point^'i).
          (fst coordinates $ from_nat_into UNIV k,
           snd coordinates $ from_nat_into UNIV k))"
      by auto
    show "(\<lambda>x. fst (pair x)) \<in> measurable ?V lborel"
      unfolding pair
      using cartesian_pos_measurable[of "from_nat_into UNIV k"]
      by (simp only: fst_conv)
  qed
  have cartesian_pair_second:
      "\<And>pair. pair \<in> set ?cartesian_pair_functions \<Longrightarrow>
        (\<lambda>x. snd (pair x)) \<in> measurable ?V lborel"
  proof -
    fix pair
    assume "pair \<in> set ?cartesian_pair_functions"
    then obtain k where pair:
        "pair = (\<lambda>coordinates :: (slp_point^'i) \<times> (slp_point^'i).
          (fst coordinates $ from_nat_into UNIV k,
           snd coordinates $ from_nat_into UNIV k))"
      by auto
    show "(\<lambda>x. snd (pair x)) \<in> measurable ?V lborel"
      unfolding pair
      using cartesian_neg_measurable[of "from_nat_into UNIV k"]
      by (simp only: snd_conv)
  qed
  have cartesian_origin:
      "(\<lambda>_::(slp_point^'i) \<times> (slp_point^'i). origin)
        \<in> measurable ?V lborel"
    by measurable
  have cartesian_target:
      "(\<lambda>_::(slp_point^'i) \<times> (slp_point^'i). target)
        \<in> measurable ?V lborel"
    by measurable
  have F_measurable: "?F \<in> borel_measurable ?V"
  proof -
    note raw =
      slp_left_branch_positive_kernel_list_fixed_output_param_measurable[
        where M = ?V and pair_functions = ?cartesian_pair_functions,
        OF cutoff_measurable potential_measurable terminal_value_measurable
          cartesian_origin cartesian_target cartesian_pair_first
          cartesian_pair_second]
    show ?thesis
      using raw
      unfolding slp_finite_branch_pair_list_def
      by (simp only: map_map comp_def split_beta')
  qed
  have transported:
      "nn_integral ?V ?F =
        (\<integral>\<^sup>+ pos_natural. \<integral>\<^sup>+ neg_natural.
          ?F ((\<chi> i. pos_natural (to_nat_on UNIV i)),
            (\<chi> i. neg_natural (to_nat_on UNIV i)))
          \<partial>?N \<partial>?N)"
    by (rule slp_nn_integral_two_finite_vectors_natural_coordinates[OF
          F_measurable])
  have natural_pairs:
      "slp_finite_branch_pair_list
          (($) (\<chi> i::'i. pos_natural (to_nat_on UNIV i)))
          (($) (\<chi> i::'i. neg_natural (to_nat_on UNIV i))) =
        map (\<lambda>k. (pos_natural k, neg_natural k)) [0..<CARD('i)]"
    for pos_natural neg_natural
  proof -
    have pos_function:
        "($) (\<chi> i::'i. pos_natural (to_nat_on UNIV i)) =
          (\<lambda>i. pos_natural (to_nat_on UNIV i))"
      by (rule ext) (simp only: vec_lambda_beta)
    have neg_function:
        "($) (\<chi> i::'i. neg_natural (to_nat_on UNIV i)) =
          (\<lambda>i. neg_natural (to_nat_on UNIV i))"
      by (rule ext) (simp only: vec_lambda_beta)
    show
      "slp_finite_branch_pair_list
          (($) (\<chi> i::'i. pos_natural (to_nat_on UNIV i)))
          (($) (\<chi> i::'i. neg_natural (to_nat_on UNIV i))) =
        map (\<lambda>k. (pos_natural k, neg_natural k)) [0..<CARD('i)]"
      unfolding pos_function neg_function
      by (rule slp_finite_branch_pair_list_natural_coordinates)
  qed
  have transported_normalized:
      "nn_integral ?V ?F =
        (\<integral>\<^sup>+ pos_natural. \<integral>\<^sup>+ neg_natural.
          ?H (pos_natural, neg_natural) \<partial>?N \<partial>?N)"
    using transported
    by (simp only: split_beta' fst_conv snd_conv natural_pairs)
  have natural_pos_projection: "fst \<in> measurable ?U ?N"
    by (rule measurable_fst)
  have natural_neg_projection: "snd \<in> measurable ?U ?N"
    by (rule measurable_snd)
  have natural_pos_coordinate:
      "\<And>k. k \<in> {..<CARD('i)} \<Longrightarrow>
        (\<lambda>(pos, neg). pos k) \<in> measurable ?U lborel"
  proof -
    fix k
    assume k: "k \<in> {..<CARD('i)}"
    have component: "(\<lambda>pos. pos k) \<in> measurable ?N lborel"
      by (rule measurable_component_singleton[OF k])
    show "(\<lambda>(pos, neg). pos k) \<in> measurable ?U lborel"
      using measurable_compose[OF natural_pos_projection component]
      by (simp only: comp_def split_beta')
  qed
  have natural_neg_coordinate:
      "\<And>k. k \<in> {..<CARD('i)} \<Longrightarrow>
        (\<lambda>(pos, neg). neg k) \<in> measurable ?U lborel"
  proof -
    fix k
    assume k: "k \<in> {..<CARD('i)}"
    have component: "(\<lambda>neg. neg k) \<in> measurable ?N lborel"
      by (rule measurable_component_singleton[OF k])
    show "(\<lambda>(pos, neg). neg k) \<in> measurable ?U lborel"
      using measurable_compose[OF natural_neg_projection component]
      by (simp only: comp_def split_beta')
  qed
  let ?natural_pair_functions =
    "(map (\<lambda>k. \<lambda>(pos, neg). (pos k, neg k)) [0..<CARD('i)] ::
      (((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<Rightarrow>
        slp_point \<times> slp_point) list)"
  have natural_pair_first:
      "\<And>pair. pair \<in> set ?natural_pair_functions \<Longrightarrow>
        (\<lambda>x. fst (pair x)) \<in> measurable ?U lborel"
  proof -
    fix pair
    assume "pair \<in> set ?natural_pair_functions"
    then obtain k where k: "k \<in> {..<CARD('i)}"
      and pair: "pair = (\<lambda>(pos, neg). (pos k, neg k))"
      by auto
    show "(\<lambda>x. fst (pair x)) \<in> measurable ?U lborel"
      unfolding pair
      using natural_pos_coordinate[OF k]
      by (simp only: split_beta' fst_conv)
  qed
  have natural_pair_second:
      "\<And>pair. pair \<in> set ?natural_pair_functions \<Longrightarrow>
        (\<lambda>x. snd (pair x)) \<in> measurable ?U lborel"
  proof -
    fix pair
    assume "pair \<in> set ?natural_pair_functions"
    then obtain k where k: "k \<in> {..<CARD('i)}"
      and pair: "pair = (\<lambda>(pos, neg). (pos k, neg k))"
      by auto
    show "(\<lambda>x. snd (pair x)) \<in> measurable ?U lborel"
      unfolding pair
      using natural_neg_coordinate[OF k]
      by (simp only: split_beta' snd_conv)
  qed
  have natural_origin:
      "(\<lambda>_::(nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point).
        origin) \<in> measurable ?U lborel"
    by measurable
  have natural_target:
      "(\<lambda>_::(nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point).
        target) \<in> measurable ?U lborel"
    by measurable
  have H_measurable: "?H \<in> borel_measurable ?U"
  proof -
    note raw =
      slp_left_branch_positive_kernel_list_fixed_output_param_measurable[
        where M = ?U and pair_functions = ?natural_pair_functions,
        OF cutoff_measurable potential_measurable terminal_value_measurable
          natural_origin natural_target natural_pair_first natural_pair_second]
    show ?thesis
      using raw by (simp only: map_map comp_def split_beta')
  qed
  interpret product:
    product_sigma_finite
      "\<lambda>_::nat. (lborel :: slp_point measure)"
    by standard
  interpret natural: sigma_finite_measure ?N
    by (rule product.sigma_finite) simp
  have split:
      "nn_integral ?U ?H =
        (\<integral>\<^sup>+ pos. \<integral>\<^sup>+ neg. ?H (pos, neg)
          \<partial>?N \<partial>?N)"
  proof -
    note raw = natural.nn_integral_fst[OF H_measurable]
    show ?thesis
      using raw[symmetric] by (simp only: split_beta')
  qed
  have density:
      "nn_integral ?U ?H =
        slp_positive_output_density R cutoff potential
          (\<lambda>x. ennreal (norm (terminal_value x))) CARD('i) origin target"
    by (rule slp_left_branch_positive_kernel_list_fixed_output_integral_natural[
          OF cutoff_measurable potential_measurable terminal_value_measurable])
  have composed:
      "nn_integral ?V ?F =
        slp_positive_output_density R cutoff potential
          (\<lambda>x. ennreal (norm (terminal_value x))) CARD('i) origin target"
    using transported_normalized split density
    by simp
  show ?thesis
    using composed by (simp only: split_beta' fst_conv snd_conv)
qed

end
