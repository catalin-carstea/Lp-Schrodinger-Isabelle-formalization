theory Inverse_Schrodinger_Lp_Natural_One_Sided_Density_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Joint_Output_Pairing"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Packed_Unit_Terminal_Output_Pairing"
begin

section \<open>Root-paired natural one-sided density transport\<close>

lemma slp_natural_one_sided_positive_param_measurable:
  fixes M :: "'a measure"
    and pos neg :: "'a \<Rightarrow> nat \<Rightarrow> slp_point"
    and origin terminal :: "'a \<Rightarrow> slp_point"
    and cutoff q T Q :: slp_scalar_field
    and h :: "slp_point \<Rightarrow> ennreal"
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and T_measurable: "T \<in> borel_measurable lborel"
    and Q_measurable: "Q \<in> borel_measurable lborel"
    and h_measurable: "h \<in> borel_measurable lborel"
    and pos_measurable:
      "pos \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and neg_measurable:
      "neg \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and origin_measurable: "origin \<in> measurable M lborel"
    and terminal_measurable: "terminal \<in> measurable M lborel"
  shows "(\<lambda>z. ennreal (norm (Q (origin z))) *
      slp_left_branch_positive_kernel_list R cutoff q T
        (map (\<lambda>k. (pos z k, neg z k)) [0..<n]) (origin z) (terminal z) *
      h (slp_left_branch_output
        (map (\<lambda>k. (pos z k, neg z k)) [0..<n]) (terminal z)))
    \<in> borel_measurable M"
proof -
  have weighted[measurable]:
    "(\<lambda>z. slp_left_branch_positive_kernel_list R cutoff q T
      (map (\<lambda>k. (pos z k, neg z k)) [0..<n]) (origin z) (terminal z) *
      h (slp_left_branch_output
        (map (\<lambda>k. (pos z k, neg z k)) [0..<n]) (terminal z)))
      \<in> borel_measurable M"
    by (rule slp_natural_weighted_positive_kernel_param_measurable[
      OF cutoff_measurable q_measurable T_measurable h_measurable
        pos_measurable neg_measurable origin_measurable terminal_measurable])
  have root_value[measurable]:
    "(\<lambda>z. Q (origin z)) \<in> borel_measurable M"
    by (rule measurable_compose[OF origin_measurable Q_measurable])
  show ?thesis by (simp only: mult.assoc; measurable)
qed

theorem slp_natural_one_sided_positive_density_pairing:
  fixes n :: nat and cutoff q T Q :: slp_scalar_field
    and h :: "slp_point \<Rightarrow> ennreal"
  assumes cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and h_measurable[measurable]: "h \<in> borel_measurable lborel"
  shows "nn_integral
    ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)
    (\<lambda>z. ennreal (norm (Q (snd z))) *
      slp_left_branch_positive_kernel_list R cutoff q T
        (map (\<lambda>k. (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n])
        (snd z) (snd (fst z)) *
      h (slp_left_branch_output
        (map (\<lambda>k. (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n])
        (snd (fst z)))) =
    nn_integral lborel (\<lambda>u. h u *
      slp_positive_root_output_density R cutoff q
        (\<lambda>s. ennreal (norm (T s))) n Q u)"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?M = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?pairs = "\<lambda>b::((nat \<Rightarrow> slp_point) \<times>
      (nat \<Rightarrow> slp_point)) \<times> slp_point.
    map (\<lambda>k. (fst (fst b) k, snd (fst b) k)) [0..<n]"
  let ?out = "\<lambda>b. slp_left_branch_output (?pairs b) (snd b)"
  let ?K = "\<lambda>x b. slp_left_branch_positive_kernel_list R cutoff q T
    (?pairs b) x (snd b)"
  let ?QN = "\<lambda>x. ennreal (norm (Q x))"
  let ?TW = "\<lambda>s. ennreal (norm (T s))"
  let ?F = "\<lambda>z. ?QN (snd z) * ?K (snd z) (fst z) * h (?out (fst z))"
  let ?L = "\<lambda>x. slp_positive_branch_functional R cutoff q ?TW n x h"
  have joint_measurable: "?F \<in> borel_measurable ?M"
    by (rule slp_natural_one_sided_positive_param_measurable[
      OF cutoff_measurable q_measurable T_measurable Q_measurable h_measurable];
      measurable)
  interpret natural_product: product_sigma_finite
    "\<lambda>_::nat. (lborel :: slp_point measure)" by standard
  interpret family: sigma_finite_measure ?P
    by (rule natural_product.sigma_finite) simp
  interpret arrays: pair_sigma_finite ?P ?P ..
  interpret array_measure: sigma_finite_measure "?P \<Otimes>\<^sub>M ?P" by standard
  interpret branches: pair_sigma_finite "?P \<Otimes>\<^sub>M ?P"
    "lborel :: slp_point measure" ..
  interpret branch_measure: sigma_finite_measure ?B by standard
  interpret full_measure: pair_sigma_finite ?B "lborel :: slp_point measure" ..
  have TW_measurable[measurable]: "?TW \<in> borel_measurable lborel" by measurable
  have weighted: "(\<lambda>b. ?K x b * h (?out b)) \<in> borel_measurable ?B" for x
    by (rule slp_natural_weighted_positive_kernel_param_measurable[
      OF cutoff_measurable q_measurable T_measurable h_measurable]; measurable)
  have branch_pairing:
    "nn_integral ?B (\<lambda>b. ?K x b * h (?out b)) = ?L x" for x
  proof -
    have "nn_integral ?B (\<lambda>b. ?K x b * h (?out b)) =
        nn_integral lborel (\<lambda>u. h u *
          slp_positive_output_density R cutoff q ?TW n x u)"
      by (rule slp_left_branch_positive_kernel_natural_joint_output_density_pairing[
        OF cutoff_measurable q_measurable T_measurable h_measurable])
    also have "\<dots> = ?L x"
      by (rule slp_positive_output_density_pushforward[
        OF cutoff_measurable q_measurable TW_measurable h_measurable])
    finally show ?thesis .
  qed
  have root_inner: "nn_integral ?B (\<lambda>b. ?F (b,x)) = ?QN x * ?L x" for x
  proof -
    have pull: "nn_integral ?B (\<lambda>b. ?F (b,x)) =
        ?QN x * nn_integral ?B (\<lambda>b. ?K x b * h (?out b))"
      using nn_integral_cmult[OF weighted[of x], where c="?QN x"]
      by (simp only: fst_conv snd_conv mult.assoc)
    show ?thesis using pull by (simp only: branch_pairing)
  qed
  have move_root: "nn_integral ?M ?F =
      nn_integral lborel (\<lambda>x. nn_integral ?B (\<lambda>b. ?F (b,x)))"
    using full_measure.nn_integral_snd[OF joint_measurable] by simp
  have raw_to_functional: "nn_integral ?M ?F =
      nn_integral lborel (\<lambda>x. ?QN x * ?L x)"
    using move_root by (simp only: root_inner)
  have density_to_functional:
    "nn_integral lborel (\<lambda>u. h u *
      slp_positive_root_output_density R cutoff q ?TW n Q u) =
     nn_integral lborel (\<lambda>x. ?QN x * ?L x)"
    by (rule slp_positive_root_output_density_pairing[
      OF cutoff_measurable q_measurable TW_measurable Q_measurable h_measurable])
  show ?thesis by (rule trans[OF raw_to_functional density_to_functional[symmetric]])
qed

end
