theory Inverse_Schrodinger_Lp_Natural_Mixed_Amplitude_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Density_Pairing"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Coordinate_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Support"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Natural mixed complex amplitudes controlled by center densities\<close>

definition slp_natural_mixed_weighted_amplitude ::
  "nat \<Rightarrow> nat \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    (((((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times> slp_point) \<times>
      (((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times> slp_point)) \<times>
      slp_point) \<Rightarrow> complex"
where
  "slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H z =
    (let l = fst (fst z); r = snd (fst z); x = snd z;
         lp = map (\<lambda>k. (fst (fst l) k, snd (fst l) k)) [0..<n];
         rp = map (\<lambda>k. (fst (fst r) k, snd (fst r) k)) [0..<m]
     in Q x * slp_left_branch_complex_kernel_list cutoff q T lp x (snd l) *
       cnj (slp_left_branch_complex_kernel_list
         (\<lambda>y. cnj (cutoff y)) (\<lambda>y. cnj (qt y)) (\<lambda>y. cnj (U y))
         rp x (snd r)) *
       H (slp_mixed_branch_center x lp (snd l) rp (snd r)))"

theorem slp_natural_mixed_weighted_amplitude_measurable:
  assumes cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and qt_measurable[measurable]: "qt \<in> borel_measurable lborel"
    and U_measurable[measurable]: "U \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and H_measurable[measurable]: "H \<in> borel_measurable lborel"
  shows "slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H
    \<in> borel_measurable
      (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M
        (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
        \<Otimes>\<^sub>M lborel)"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
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
  let ?l = "\<lambda>z. fst (fst z)"
  let ?r = "\<lambda>z. snd (fst z)"
  let ?lp = "\<lambda>z. map (\<lambda>k. (fst (fst (?l z)) k, snd (fst (?l z)) k)) [0..<n]"
  let ?rp = "\<lambda>z. map (\<lambda>k. (fst (fst (?r z)) k, snd (fst (?r z)) k)) [0..<m]"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z)
    (?lp z) (snd (?l z)) (?rp z) (snd (?r z))"
  have left_kernel[measurable]:
    "(\<lambda>z. slp_left_branch_complex_kernel_list cutoff q T
      (?lp z) (snd z) (snd (?l z))) \<in> borel_measurable ?MJ"
    by (rule kernel_measurable[OF cutoff_measurable q_measurable T_measurable]; measurable)
  have cnj_measurable: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          continuous_on_cnj[OF continuous_on_id]])
  have cutoff_cnj: "(\<lambda>y. cnj (cutoff y)) \<in> borel_measurable lborel"
    by (rule measurable_compose[OF cutoff_measurable cnj_measurable])
  have qt_cnj: "(\<lambda>y. cnj (qt y)) \<in> borel_measurable lborel"
    by (rule measurable_compose[OF qt_measurable cnj_measurable])
  have U_cnj: "(\<lambda>y. cnj (U y)) \<in> borel_measurable lborel"
    by (rule measurable_compose[OF U_measurable cnj_measurable])
  have right_inner[measurable]:
    "(\<lambda>z. slp_left_branch_complex_kernel_list
      (\<lambda>y. cnj (cutoff y)) (\<lambda>y. cnj (qt y)) (\<lambda>y. cnj (U y))
      (?rp z) (snd z) (snd (?r z))) \<in> borel_measurable ?MJ"
    by (rule kernel_measurable[OF cutoff_cnj qt_cnj U_cnj]; measurable)
  have right_kernel[measurable]:
    "(\<lambda>z. cnj (slp_left_branch_complex_kernel_list
      (\<lambda>y. cnj (cutoff y)) (\<lambda>y. cnj (qt y)) (\<lambda>y. cnj (U y))
      (?rp z) (snd z) (snd (?r z)))) \<in> borel_measurable ?MJ"
    by (rule measurable_compose[OF right_inner cnj_measurable])
  have left_out:
    "(\<lambda>z. slp_left_branch_output (?lp z) (snd (?l z))) \<in> measurable ?MJ lborel"
    by (rule slp_natural_branch_output_param_measurable; measurable)
  have right_out:
    "(\<lambda>z. slp_left_branch_output (?rp z) (snd (?r z))) \<in> measurable ?MJ lborel"
    by (rule slp_natural_branch_output_param_measurable; measurable)
  have left_out_borel[measurable]:
    "(\<lambda>z. slp_left_branch_output (?lp z) (snd (?l z))) \<in> borel_measurable ?MJ"
    using left_out by (simp only: measurable_lborel1)
  have right_out_borel[measurable]:
    "(\<lambda>z. slp_left_branch_output (?rp z) (snd (?r z))) \<in> borel_measurable ?MJ"
    using right_out by (simp only: measurable_lborel1)
  have center_borel: "?center \<in> borel_measurable ?MJ"
    by (simp only: slp_mixed_branch_center_def
          slp_left_branch_output_eq_right[symmetric]; measurable)
  have center_map: "?center \<in> measurable ?MJ lborel"
    using center_borel by (simp only: measurable_lborel1)
  have center_factor[measurable]: "(\<lambda>z. H (?center z)) \<in> borel_measurable ?MJ"
    by (rule measurable_compose[OF center_map H_measurable])
  show ?thesis
    unfolding slp_natural_mixed_weighted_amplitude_def Let_def
    by measurable
qed

theorem slp_natural_mixed_weighted_amplitude_integrable_from_density:
  fixes n m :: nat and Q cutoff q T qt U H :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and qt_measurable[measurable]: "qt \<in> borel_measurable lborel"
    and U_measurable[measurable]: "U \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and H_measurable[measurable]: "H \<in> borel_measurable lborel"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and density_mass:
      "nn_integral lborel (\<lambda>c. ennreal (norm (H c)) *
        slp_mixed_center_density (2 * R) cutoff q qt
          (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c) < top_class.top"
  shows "integrable
    (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M
      (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
      \<Otimes>\<^sub>M lborel)
    (slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H)"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?F = "slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H"
  let ?lp = "\<lambda>z. map (\<lambda>k. (fst (fst (fst (fst z))) k,
    snd (fst (fst (fst z))) k)) [0..<n]"
  let ?rp = "\<lambda>z. map (\<lambda>k. (fst (fst (snd (fst z))) k,
    snd (fst (snd (fst z))) k)) [0..<m]"
  let ?s = "\<lambda>z. snd (fst (fst z))"
  let ?t = "\<lambda>z. snd (snd (fst z))"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z) (?lp z) (?s z) (?rp z) (?t z)"
  let ?K = "\<lambda>z. ennreal (norm (Q (snd z))) *
    slp_left_branch_positive_kernel_list (2 * R) cutoff q T (?lp z) (snd z) (?s z) *
    slp_left_branch_positive_kernel_list (2 * R) cutoff qt U (?rp z) (snd z) (?t z) *
    ennreal (norm (H (?center z)))"
  have amplitude_measurable: "?F \<in> borel_measurable ?MJ"
    by (rule slp_natural_mixed_weighted_amplitude_measurable[
          OF cutoff_measurable q_measurable T_measurable qt_measurable
            U_measurable Q_measurable H_measurable])
  have positive_conjugate:
    "slp_left_branch_positive_kernel_list (2 * R)
      (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (qt x)) (\<lambda>x. cnj (U x))
      pairs origin terminal =
     slp_left_branch_positive_kernel_list (2 * R) cutoff qt U pairs origin terminal"
    for pairs origin terminal
  proof (induction pairs arbitrary: origin)
    case Nil
    then show ?case by simp
  next
    case (Cons pair pairs)
    then show ?case by (simp add: slp_positive_branch_block_weight_def)
  qed
  have majorant: "ennreal (norm (?F z)) \<le> ?K z" for z
  proof (cases "?F z = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have root_nonzero: "Q (snd z) \<noteq> 0"
      using False unfolding slp_natural_mixed_weighted_amplitude_def Let_def by auto
    have left_nonzero:
      "slp_left_branch_complex_kernel_list cutoff q T (?lp z) (snd z) (?s z) \<noteq> 0"
      using False unfolding slp_natural_mixed_weighted_amplitude_def Let_def by auto
    have right_nonzero:
      "slp_left_branch_complex_kernel_list
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (qt x)) (\<lambda>x. cnj (U x))
        (?rp z) (snd z) (?t z) \<noteq> 0"
      using False unfolding slp_natural_mixed_weighted_amplitude_def Let_def by auto
    have root_bound: "norm (snd z) \<le> R" by (rule Q_support[OF root_nonzero])
    have left_chain: "slp_left_branch_radius_chain (2 * R) (snd z) (?lp z) (?s z)"
      by (rule slp_left_branch_complex_kernel_list_support_chain[
            OF R_nonnegative root_bound cutoff_support q_support left_nonzero])
    have cutoff_conjugate_support: "\<And>x. cnj (cutoff x) \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      using cutoff_support by simp
    have qt_conjugate_support: "\<And>x. cnj (qt x) \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      using qt_support by simp
    have right_chain: "slp_left_branch_radius_chain (2 * R) (snd z) (?rp z) (?t z)"
      by (rule slp_left_branch_complex_kernel_list_support_chain[
            OF R_nonnegative root_bound cutoff_conjugate_support qt_conjugate_support right_nonzero])
    have left_weight:
      "ennreal (norm (slp_left_branch_complex_kernel_list cutoff q T
        (?lp z) (snd z) (?s z))) =
       slp_left_branch_positive_kernel_list (2 * R) cutoff q T (?lp z) (snd z) (?s z)"
      by (rule slp_left_branch_complex_kernel_list_positive_weight[OF left_chain])
    have right_weight:
      "ennreal (norm (slp_left_branch_complex_kernel_list
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (qt x)) (\<lambda>x. cnj (U x))
        (?rp z) (snd z) (?t z))) =
       slp_left_branch_positive_kernel_list (2 * R) cutoff qt U (?rp z) (snd z) (?t z)"
      using slp_left_branch_complex_kernel_list_positive_weight[
        OF right_chain, of "\<lambda>x. cnj (cutoff x)" "\<lambda>x. cnj (qt x)" "\<lambda>x. cnj (U x)"]
      by (simp only: positive_conjugate)
    have exact: "ennreal (norm (?F z)) = ?K z"
      unfolding slp_natural_mixed_weighted_amplitude_def Let_def
      by (simp add: norm_mult ennreal_mult left_weight right_weight)
    then show ?thesis by simp
  qed
  have test_measurable: "(\<lambda>c. ennreal (norm (H c))) \<in> borel_measurable lborel"
    by measurable
  have pairing:
    "nn_integral ?MJ ?K =
     nn_integral lborel (\<lambda>c. ennreal (norm (H c)) *
       slp_mixed_center_density (2 * R) cutoff q qt
         (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c)"
    using slp_natural_mixed_positive_density_pairing[
      OF cutoff_measurable q_measurable qt_measurable T_measurable
        U_measurable Q_measurable test_measurable, where R="2 * R" and n=n and m=m]
    by (simp only: case_prod_unfold)
  have integral_bound: "nn_integral ?MJ (\<lambda>z. ennreal (norm (?F z))) \<le> nn_integral ?MJ ?K"
    by (rule nn_integral_mono) (rule majorant)
  have finite_norm: "nn_integral ?MJ (\<lambda>z. ennreal (norm (?F z))) < top_class.top"
    using integral_bound pairing density_mass by auto
  show ?thesis using amplitude_measurable finite_norm
    by (simp add: integrable_iff_bounded)
qed

end
