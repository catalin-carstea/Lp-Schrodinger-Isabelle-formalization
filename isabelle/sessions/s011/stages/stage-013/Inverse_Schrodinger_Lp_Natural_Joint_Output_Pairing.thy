theory Inverse_Schrodinger_Lp_Natural_Joint_Output_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Output_Density_Pairing"
begin

section \<open>Natural branch outputs on joint array and terminal measures\<close>

lemma slp_natural_branch_output_param_measurable:
  fixes M :: "'a measure"
    and pos neg :: "'a \<Rightarrow> nat \<Rightarrow> slp_point"
    and terminal :: "'a \<Rightarrow> slp_point"
  assumes pos_measurable:
      "pos \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and neg_measurable:
      "neg \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and terminal_measurable: "terminal \<in> measurable M lborel"
  shows "(\<lambda>x. slp_left_branch_output
      (map (\<lambda>k. (pos x k, neg x k)) [0..<n]) (terminal x))
    \<in> measurable M lborel"
proof -
  let ?MP = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  have pos_component: "(\<lambda>x. pos x k) \<in> borel_measurable M"
    if k_in: "k \<in> {..<n}" for k
  proof -
    have component: "(\<lambda>family::nat \<Rightarrow> slp_point. family k)
      \<in> measurable ?MP lborel"
      by (rule measurable_component_singleton[OF k_in])
    show ?thesis using measurable_compose[OF pos_measurable component]
      by (simp only: measurable_lborel1)
  qed
  have neg_component: "(\<lambda>x. neg x k) \<in> borel_measurable M"
    if k_in: "k \<in> {..<n}" for k
  proof -
    have component: "(\<lambda>family::nat \<Rightarrow> slp_point. family k)
      \<in> measurable ?MP lborel"
      by (rule measurable_component_singleton[OF k_in])
    show ?thesis using measurable_compose[OF neg_measurable component]
      by (simp only: measurable_lborel1)
  qed
  have sum_measurable[measurable]:
    "(\<lambda>x. \<Sum>k\<in>{..<n}. pos x k - neg x k) \<in> borel_measurable M"
  proof (rule borel_measurable_sum)
    fix k assume k_in: "k \<in> {..<n}"
    show "(\<lambda>x. pos x k - neg x k) \<in> borel_measurable M"
      using pos_component[OF k_in] neg_component[OF k_in] by measurable
  qed
  have terminal_borel[measurable]: "terminal \<in> borel_measurable M"
    using terminal_measurable by (simp only: measurable_lborel1)
  have output_eq:
    "slp_left_branch_output (map (\<lambda>k. (pos x k, neg x k)) [0..<n])
      (terminal x) = terminal x + (\<Sum>k\<in>{..<n}. pos x k - neg x k)"
    for x
    by (simp add: slp_left_branch_output_def slp_branch_increment_def
        map_map comp_def sum_list_distinct_conv_sum_set atLeast0LessThan)
  show ?thesis
    by (simp only: output_eq measurable_lborel1; measurable)
qed

lemma slp_natural_weighted_positive_kernel_param_measurable:
  fixes M :: "'a measure"
    and pos neg :: "'a \<Rightarrow> nat \<Rightarrow> slp_point"
    and origin terminal :: "'a \<Rightarrow> slp_point"
    and output_test :: "slp_point \<Rightarrow> ennreal"
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_value_measurable: "terminal_value \<in> borel_measurable lborel"
    and output_test_measurable: "output_test \<in> borel_measurable lborel"
    and pos_measurable:
      "pos \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and neg_measurable:
      "neg \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and origin_measurable: "origin \<in> measurable M lborel"
    and terminal_measurable: "terminal \<in> measurable M lborel"
  shows "(\<lambda>x. slp_left_branch_positive_kernel_list R cutoff potential
      terminal_value (map (\<lambda>k. (pos x k, neg x k)) [0..<n])
        (origin x) (terminal x) *
    output_test (slp_left_branch_output
      (map (\<lambda>k. (pos x k, neg x k)) [0..<n]) (terminal x)))
    \<in> borel_measurable M"
proof -
  let ?pairs = "\<lambda>x. map (\<lambda>k. (pos x k, neg x k)) [0..<n]"
  let ?out = "\<lambda>x. slp_left_branch_output (?pairs x) (terminal x)"
  have out_measurable: "?out \<in> measurable M lborel"
    by (rule slp_natural_branch_output_param_measurable[
          OF pos_measurable neg_measurable terminal_measurable])
  have fixed_measurable:
    "(\<lambda>x. slp_left_branch_positive_kernel_list_fixed_output R cutoff
      potential terminal_value (?pairs x) (origin x) (?out x))
      \<in> borel_measurable M"
    by (rule slp_natural_fixed_output_param_measurable[
          OF cutoff_measurable potential_measurable terminal_value_measurable
            pos_measurable neg_measurable origin_measurable out_measurable])
  have kernel_measurable[measurable]:
    "(\<lambda>x. slp_left_branch_positive_kernel_list R cutoff potential
      terminal_value (?pairs x) (origin x) (terminal x)) \<in> borel_measurable M"
    using fixed_measurable
    by (simp add: slp_left_branch_positive_kernel_list_fixed_output_def
        slp_left_branch_output_def)
  have weight_measurable[measurable]:
    "(\<lambda>x. output_test (?out x)) \<in> borel_measurable M"
    by (rule measurable_compose[OF out_measurable output_test_measurable])
  show ?thesis by measurable
qed

theorem slp_left_branch_positive_kernel_natural_joint_output_density_pairing:
  fixes n :: nat and root :: slp_point
    and output_test :: "slp_point \<Rightarrow> ennreal"
  assumes cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]: "potential \<in> borel_measurable lborel"
    and terminal_measurable[measurable]: "terminal_value \<in> borel_measurable lborel"
    and output_test_measurable[measurable]: "output_test \<in> borel_measurable lborel"
  shows "nn_integral
    (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
    (\<lambda>z. slp_left_branch_positive_kernel_list R cutoff potential terminal_value
      (map (\<lambda>k. (fst (fst z) k, snd (fst z) k)) [0..<n]) root (snd z) *
      output_test (slp_left_branch_output
        (map (\<lambda>k. (fst (fst z) k, snd (fst z) k)) [0..<n]) (snd z))) =
    nn_integral lborel (\<lambda>target.
      output_test target * slp_positive_output_density R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) n root target)"
proof -
  let ?MP = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MA = "?MP \<Otimes>\<^sub>M ?MP"
  let ?MJ = "?MA \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?pairs = "\<lambda>families::(nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point).
    map (\<lambda>k. (fst families k, snd families k)) [0..<n]"
  let ?weighted = "\<lambda>families terminal.
    slp_left_branch_positive_kernel_list R cutoff potential terminal_value
      (?pairs families) root terminal *
    output_test (slp_left_branch_output (?pairs families) terminal)"
  have joint_measurable:
    "(\<lambda>z. ?weighted (fst z) (snd z)) \<in> borel_measurable ?MJ"
    by (rule slp_natural_weighted_positive_kernel_param_measurable[
          OF cutoff_measurable potential_measurable terminal_measurable
            output_test_measurable]; measurable)
  have joint_to_nested:
    "nn_integral ?MJ (\<lambda>z. ?weighted (fst z) (snd z)) =
      nn_integral ?MA (\<lambda>families. nn_integral lborel (?weighted families))"
    using lborel.nn_integral_fst[OF joint_measurable] by simp
  note nested_pairing =
    slp_left_branch_positive_kernel_natural_output_density_pairing[
      where n = n and root = root and R = R and cutoff = cutoff
        and potential = potential and terminal_value = terminal_value
        and output_test = output_test,
      OF cutoff_measurable potential_measurable terminal_measurable
        output_test_measurable]
  show ?thesis by (rule trans[OF joint_to_nested nested_pairing])
qed

end
