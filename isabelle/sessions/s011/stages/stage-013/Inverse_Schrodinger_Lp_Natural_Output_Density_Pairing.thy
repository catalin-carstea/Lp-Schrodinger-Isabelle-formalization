theory Inverse_Schrodinger_Lp_Natural_Output_Density_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Positive_Kernel_List_Fixed_Output_Natural_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Affine_Output_Transport"
begin

section \<open>Natural-order positive branch kernels and their output density\<close>

lemma slp_natural_fixed_output_param_measurable:
  fixes M :: "'a measure"
    and pos neg :: "'a \<Rightarrow> nat \<Rightarrow> slp_point"
    and origin target_position :: "'a \<Rightarrow> slp_point"
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_measurable: "terminal_value \<in> borel_measurable lborel"
    and pos_measurable:
      "pos \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and neg_measurable:
      "neg \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and origin_measurable: "origin \<in> measurable M lborel"
    and output_measurable: "target_position \<in> measurable M lborel"
  shows "(\<lambda>x. slp_left_branch_positive_kernel_list_fixed_output R cutoff
    potential terminal_value (map (\<lambda>k. (pos x k, neg x k)) [0..<n])
      (origin x) (target_position x)) \<in> borel_measurable M"
proof -
  let ?MP = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?pairs = "map (\<lambda>k x. (pos x k, neg x k)) [0..<n]"
  have pos_component: "(\<lambda>x. pos x k) \<in> measurable M lborel"
    if k_bound: "k < n" for k
  proof -
    have k_in: "k \<in> {..<n}" using k_bound by simp
    have component: "(\<lambda>family::nat \<Rightarrow> slp_point. family k)
      \<in> measurable ?MP lborel"
      by (rule measurable_component_singleton[OF k_in])
    show ?thesis by (rule measurable_compose[OF pos_measurable component])
  qed
  have neg_component: "(\<lambda>x. neg x k) \<in> measurable M lborel"
    if k_bound: "k < n" for k
  proof -
    have k_in: "k \<in> {..<n}" using k_bound by simp
    have component: "(\<lambda>family::nat \<Rightarrow> slp_point. family k)
      \<in> measurable ?MP lborel"
      by (rule measurable_component_singleton[OF k_in])
    show ?thesis by (rule measurable_compose[OF neg_measurable component])
  qed
  have first_measurable:
    "(\<lambda>x. fst (pair x)) \<in> measurable M lborel"
    if pair_in: "pair \<in> set ?pairs" for pair
  proof -
    obtain k where k_bound: "k < n"
      and pair_eq: "pair = (\<lambda>x. (pos x k, neg x k))"
      using pair_in by auto
    show ?thesis using pos_component[OF k_bound] by (simp only: pair_eq fst_conv)
  qed
  have second_measurable:
    "(\<lambda>x. snd (pair x)) \<in> measurable M lborel"
    if pair_in: "pair \<in> set ?pairs" for pair
  proof -
    obtain k where k_bound: "k < n"
      and pair_eq: "pair = (\<lambda>x. (pos x k, neg x k))"
      using pair_in by auto
    show ?thesis using neg_component[OF k_bound] by (simp only: pair_eq snd_conv)
  qed
  note result = slp_left_branch_positive_kernel_list_fixed_output_param_measurable[
    where M = M and pair_functions = ?pairs and R = R and cutoff = cutoff
      and potential = potential and terminal_value = terminal_value
      and origin = origin,
    OF cutoff_measurable potential_measurable terminal_measurable
      origin_measurable output_measurable first_measurable second_measurable]
  show ?thesis using result by (simp only: map_map comp_def)
qed

theorem slp_left_branch_positive_kernel_natural_output_density_pairing:
  fixes n :: nat and root :: slp_point
    and output_test :: "slp_point \<Rightarrow> ennreal"
  assumes cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]: "potential \<in> borel_measurable lborel"
    and terminal_measurable[measurable]: "terminal_value \<in> borel_measurable lborel"
    and output_test_measurable[measurable]: "output_test \<in> borel_measurable lborel"
  shows "nn_integral
    ((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
    (\<lambda>families. nn_integral lborel (\<lambda>terminal.
      slp_left_branch_positive_kernel_list R cutoff potential terminal_value
        (map (\<lambda>k. (fst families k, snd families k)) [0..<n]) root terminal *
      output_test (slp_left_branch_output
        (map (\<lambda>k. (fst families k, snd families k)) [0..<n]) terminal))) =
    nn_integral lborel (\<lambda>target.
      output_test target * slp_positive_output_density R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) n root target)"
proof -
  let ?MP = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MA = "?MP \<Otimes>\<^sub>M ?MP"
  let ?MJ = "?MA \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?pairs = "\<lambda>families::(nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point).
    map (\<lambda>k. (fst families k, snd families k)) [0..<n]"
  let ?fixed = "\<lambda>families target.
    slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
      terminal_value (?pairs families) root target"
  let ?weighted = "\<lambda>families target. ?fixed families target * output_test target"
  have fixed_raw[measurable]:
    "(\<lambda>z. ?fixed (fst z) (snd z)) \<in> borel_measurable ?MJ"
    by (rule slp_natural_fixed_output_param_measurable[
        OF cutoff_measurable potential_measurable terminal_measurable]; measurable)
  have fixed_joint: "case_prod ?fixed \<in> borel_measurable ?MJ"
    using fixed_raw by (simp only: case_prod_unfold)
  have weighted_raw:
    "(\<lambda>z. ?weighted (fst z) (snd z)) \<in> borel_measurable ?MJ"
    using fixed_raw output_test_measurable by measurable
  have weighted_joint: "case_prod ?weighted \<in> borel_measurable ?MJ"
    using weighted_raw by (simp only: case_prod_unfold)
  interpret natural_product: product_sigma_finite
    "\<lambda>_::nat. (lborel :: slp_point measure)" by standard
  interpret family_measure: sigma_finite_measure ?MP
    by (rule natural_product.sigma_finite) simp
  interpret family_pair: pair_sigma_finite ?MP ?MP ..
  interpret array_measure: sigma_finite_measure ?MA by standard
  interpret all_coordinates: pair_sigma_finite ?MA "lborel :: slp_point measure" ..
  have translate_terminal:
    "nn_integral lborel (\<lambda>terminal.
      slp_left_branch_positive_kernel_list R cutoff potential terminal_value
        (?pairs families) root terminal *
      output_test (slp_left_branch_output (?pairs families) terminal)) =
      nn_integral lborel (?weighted families)"
    if families_in: "families \<in> space ?MA" for families
  proof -
    have fixed_slice: "?fixed families \<in> borel_measurable lborel"
      using measurable_compose_Pair1[OF families_in fixed_joint]
      by (simp only: case_prod_conv)
    have weighted_slice: "?weighted families \<in> borel_measurable lborel"
      using fixed_slice output_test_measurable by measurable
    note shifted = slp_nn_integral_translate[OF weighted_slice,
      where shift = "slp_left_branch_output (?pairs families) 0"]
    show ?thesis using shifted
      by (simp add: slp_left_branch_positive_kernel_list_fixed_output_def
          slp_left_branch_output_def algebra_simps)
  qed
  have translate_all:
    "nn_integral ?MA (\<lambda>families. nn_integral lborel (\<lambda>terminal.
      slp_left_branch_positive_kernel_list R cutoff potential terminal_value
        (?pairs families) root terminal *
      output_test (slp_left_branch_output (?pairs families) terminal))) =
      nn_integral ?MA (\<lambda>families. nn_integral lborel (?weighted families))"
  proof (rule nn_integral_cong)
    fix families assume families_in: "families \<in> space ?MA"
    show "nn_integral lborel (\<lambda>terminal.
      slp_left_branch_positive_kernel_list R cutoff potential terminal_value
        (?pairs families) root terminal *
      output_test (slp_left_branch_output (?pairs families) terminal)) =
      nn_integral lborel (?weighted families)"
      by (rule translate_terminal[OF families_in])
  qed
  have swap:
    "nn_integral ?MA (\<lambda>families. nn_integral lborel (?weighted families)) =
      nn_integral lborel (\<lambda>target. nn_integral ?MA
        (\<lambda>families. ?weighted families target))"
    using all_coordinates.Fubini'[OF weighted_joint] by simp
  have array_slice:
    "(\<lambda>families. ?fixed families target) \<in> borel_measurable ?MA"
    for target :: slp_point
  proof -
    have insert_target: "(\<lambda>families. (families, target)) \<in> measurable ?MA ?MJ"
      by (rule measurable_Pair2') simp
    show ?thesis using measurable_compose[OF insert_target fixed_joint]
      by (simp only: case_prod_conv)
  qed
  have density_value:
    "nn_integral ?MA (\<lambda>families. ?fixed families target) =
      slp_positive_output_density R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) n root target"
    for target :: slp_point
    using slp_left_branch_positive_kernel_list_fixed_output_integral_natural[
      where n = n and R = R and cutoff = cutoff and potential = potential
        and terminal_value = terminal_value and origin = root and target = target,
      OF cutoff_measurable potential_measurable terminal_measurable]
    by (simp only: case_prod_unfold)
  have collapse_target:
    "nn_integral ?MA (\<lambda>families. ?weighted families target) =
      output_test target * slp_positive_output_density R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) n root target"
    for target :: slp_point
    using nn_integral_multc[OF array_slice[of target], where c = "output_test target"]
      density_value[of target]
    by (simp add: mult.commute)
  note combined = trans[OF translate_all swap]
  show ?thesis using combined by (simp only: collapse_target)
qed

end
