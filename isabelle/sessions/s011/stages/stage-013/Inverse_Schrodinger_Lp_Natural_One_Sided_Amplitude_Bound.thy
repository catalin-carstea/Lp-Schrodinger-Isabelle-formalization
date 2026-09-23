theory Inverse_Schrodinger_Lp_Natural_One_Sided_Amplitude_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Density_Pairing"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Amplitude_Integrable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Natural one-sided amplitudes and absolute integral bounds\<close>

definition slp_natural_one_sided_weighted_amplitude ::
  "nat \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    ((((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
      slp_point) \<times> slp_point) \<Rightarrow> complex"
where
  "slp_natural_one_sided_weighted_amplitude n Q cutoff q T H z =
    (let b = fst z; x = snd z;
         ps = map (\<lambda>k. (fst (fst b) k, snd (fst b) k)) [0..<n]
     in Q x * slp_left_branch_complex_kernel_list cutoff q T ps x (snd b) *
       H (slp_left_branch_output ps (snd b)))"

theorem slp_natural_one_sided_weighted_amplitude_measurable:
  assumes cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and H_measurable[measurable]: "H \<in> borel_measurable lborel"
  shows "slp_natural_one_sided_weighted_amplitude n Q cutoff q T H
    \<in> borel_measurable ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  have kernel_measurable:
    "(\<lambda>z. slp_left_branch_complex_kernel_list c v Z
      (map (\<lambda>j. (pos z j, neg z j)) [0..<k]) (origin z) (terminal z))
      \<in> borel_measurable ?MJ"
    if c_meas: "c \<in> borel_measurable lborel"
      and v_meas: "v \<in> borel_measurable lborel"
      and Z_meas: "Z \<in> borel_measurable lborel"
      and pos_meas: "pos \<in> measurable ?MJ (PiM {..<k} (\<lambda>_::nat. lborel))"
      and neg_meas: "neg \<in> measurable ?MJ (PiM {..<k} (\<lambda>_::nat. lborel))"
      and origin_meas: "origin \<in> measurable ?MJ lborel"
      and terminal_meas: "terminal \<in> measurable ?MJ lborel"
    for k c v Z pos neg origin terminal
  proof -
    let ?PK = "PiM {..<k} (\<lambda>_::nat. (lborel :: slp_point measure))"
    have coordinate:
      "(\<lambda>z. slp_left_branch_natural_value k (family z) j) \<in> borel_measurable ?MJ"
      if family_meas: "family \<in> measurable ?MJ ?PK" for family j
    proof (cases "j < k")
      case True
      have j_in: "j \<in> {..<k}" using True by simp
      have evaluation: "(\<lambda>f::nat \<Rightarrow> slp_point. f j) \<in> measurable ?PK lborel"
        by (rule measurable_component_singleton[OF j_in])
      have composed: "(\<lambda>z. family z j) \<in> measurable ?MJ lborel"
        by (rule measurable_compose[OF family_meas evaluation])
      show ?thesis using composed True
        by (simp add: slp_left_branch_natural_value_def measurable_lborel1)
    next
      case False
      show ?thesis by (simp add: slp_left_branch_natural_value_def False)
    qed
    have origin_borel: "origin \<in> borel_measurable ?MJ"
      using origin_meas by (simp only: measurable_lborel1)
    have terminal_borel: "terminal \<in> borel_measurable ?MJ"
      using terminal_meas by (simp only: measurable_lborel1)
    have guarded:
      "(\<lambda>z. slp_left_branch_complex_kernel_list c v Z
        (map (\<lambda>j. (slp_left_branch_natural_value k (pos z) j,
          slp_left_branch_natural_value k (neg z) j)) [0..<k])
        (origin z) (terminal z)) \<in> borel_measurable ?MJ"
      by (rule slp_left_branch_complex_kernel_list_compose_measurable[
            OF c_meas v_meas Z_meas origin_borel
              coordinate[OF pos_meas] coordinate[OF neg_meas] terminal_borel])
    have pairs_eq:
      "map (\<lambda>j. (slp_left_branch_natural_value k (pos z) j,
        slp_left_branch_natural_value k (neg z) j)) [0..<k] =
        map (\<lambda>j. (pos z j, neg z j)) [0..<k]" for z
      by (rule map_cong) (auto simp: slp_left_branch_natural_value_def)
    show ?thesis using guarded by (simp only: pairs_eq)
  qed
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  have kernel[measurable]:
    "(\<lambda>z. slp_left_branch_complex_kernel_list cutoff q T
      (?ps z) (snd z) (snd (fst z))) \<in> borel_measurable ?MJ"
    by (rule kernel_measurable[OF cutoff_measurable q_measurable T_measurable]; measurable)
  have output_map:
    "(\<lambda>z. slp_left_branch_output (?ps z) (snd (fst z)))
      \<in> measurable ?MJ lborel"
    by (rule slp_natural_branch_output_param_measurable; measurable)
  have output_factor[measurable]:
    "(\<lambda>z. H (slp_left_branch_output (?ps z) (snd (fst z))))
      \<in> borel_measurable ?MJ"
    by (rule measurable_compose[OF output_map H_measurable])
  show ?thesis
    unfolding slp_natural_one_sided_weighted_amplitude_def Let_def
    by measurable
qed


theorem slp_natural_one_sided_oscillatory_integral_bound:
  fixes n :: nat and Q cutoff q T H :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and H_measurable[measurable]: "H \<in> borel_measurable lborel"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phase_measurable[measurable]: "psi \<in> borel_measurable ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)"
    and density_mass: "nn_integral lborel (\<lambda>u. ennreal (norm (H u)) *
      slp_positive_root_output_density (2 * R) cutoff q
        (\<lambda>s. ennreal (norm (T s))) n Q u) < top_class.top"
  shows "integrable ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)
    (\<lambda>z. exp (\<i> * of_real (psi z)) *
      slp_natural_one_sided_weighted_amplitude n Q cutoff q T H z)"
    and "ennreal (norm (integral\<^sup>L ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi z)) *
        slp_natural_one_sided_weighted_amplitude n Q cutoff q T H z))) \<le>
      nn_integral lborel (\<lambda>u. ennreal (norm (H u)) *
        slp_positive_root_output_density (2 * R) cutoff q
          (\<lambda>s. ennreal (norm (T s))) n Q u)"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?A = "slp_natural_one_sided_weighted_amplitude n Q cutoff q T H"
  let ?f = "\<lambda>z. exp (\<i> * of_real (psi z)) * ?A z"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  let ?s = "\<lambda>z. snd (fst z)"
  let ?out = "\<lambda>z. slp_left_branch_output (?ps z) (?s z)"
  let ?K = "\<lambda>z. ennreal (norm (Q (snd z))) *
    slp_left_branch_positive_kernel_list (2 * R) cutoff q T
      (?ps z) (snd z) (?s z) * ennreal (norm (H (?out z)))"
  let ?mass = "nn_integral lborel (\<lambda>u. ennreal (norm (H u)) *
    slp_positive_root_output_density (2 * R) cutoff q
      (\<lambda>s. ennreal (norm (T s))) n Q u)"
  have amplitude_measurable[measurable]: "?A \<in> borel_measurable ?MJ"
    by (rule slp_natural_one_sided_weighted_amplitude_measurable[
      OF cutoff_measurable q_measurable T_measurable Q_measurable H_measurable])
  have majorant: "ennreal (norm (?A z)) \<le> ?K z" for z
  proof (cases "?A z = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have root_nonzero: "Q (snd z) \<noteq> 0"
      using False unfolding slp_natural_one_sided_weighted_amplitude_def Let_def by auto
    have kernel_nonzero:
      "slp_left_branch_complex_kernel_list cutoff q T (?ps z) (snd z) (?s z) \<noteq> 0"
      using False unfolding slp_natural_one_sided_weighted_amplitude_def Let_def by auto
    have root_bound: "norm (snd z) \<le> R" by (rule Q_support[OF root_nonzero])
    have chain: "slp_left_branch_radius_chain (2 * R) (snd z) (?ps z) (?s z)"
      by (rule slp_left_branch_complex_kernel_list_support_chain[
        OF R_nonnegative root_bound cutoff_support q_support kernel_nonzero])
    have weight:
      "ennreal (norm (slp_left_branch_complex_kernel_list cutoff q T
        (?ps z) (snd z) (?s z))) =
       slp_left_branch_positive_kernel_list (2 * R) cutoff q T (?ps z) (snd z) (?s z)"
      by (rule slp_left_branch_complex_kernel_list_positive_weight[OF chain])
    have exact: "ennreal (norm (?A z)) = ?K z"
      unfolding slp_natural_one_sided_weighted_amplitude_def Let_def
      by (simp add: norm_mult ennreal_mult weight)
    then show ?thesis by simp
  qed
  have test_measurable: "(\<lambda>u. ennreal (norm (H u))) \<in> borel_measurable lborel"
    by measurable
  have pairing: "nn_integral ?MJ ?K = ?mass"
    using slp_natural_one_sided_positive_density_pairing[
      where R="2 * R" and n=n, OF cutoff_measurable q_measurable
        T_measurable Q_measurable test_measurable]
    by (simp only: case_prod_unfold)
  have integral_bound:
    "nn_integral ?MJ (\<lambda>z. ennreal (norm (?A z))) \<le> nn_integral ?MJ ?K"
    by (rule nn_integral_mono) (rule majorant)
  have amplitude_bound: "nn_integral ?MJ (\<lambda>z. ennreal (norm (?A z))) \<le> ?mass"
    using integral_bound by (simp only: pairing)
  have f_measurable: "?f \<in> borel_measurable ?MJ" by measurable
  have norm_eq: "norm (?f z) = norm (?A z)" for z
    by (simp add: norm_mult norm_exp_i_times)
  have f_bound: "nn_integral ?MJ (\<lambda>z. ennreal (norm (?f z))) \<le> ?mass"
    using amplitude_bound by (simp only: norm_eq)
  have finite_norm: "nn_integral ?MJ (\<lambda>z. ennreal (norm (?f z))) < top_class.top"
    by (rule le_less_trans[OF f_bound density_mass])
  have f_integrable: "integrable ?MJ ?f"
    using f_measurable finite_norm by (simp add: integrable_iff_bounded)
  show "integrable ?MJ ?f" by (rule f_integrable)
  show "ennreal (norm (integral\<^sup>L ?MJ ?f)) \<le> ?mass"
    by (rule order_trans[OF
      Bochner_Integration.integral_norm_bound_ennreal[OF f_integrable] f_bound])
qed

end
