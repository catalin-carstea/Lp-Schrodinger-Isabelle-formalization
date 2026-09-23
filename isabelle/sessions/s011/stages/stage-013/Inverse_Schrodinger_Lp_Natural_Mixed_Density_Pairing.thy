theory Inverse_Schrodinger_Lp_Natural_Mixed_Density_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Joint_Output_Pairing"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Pairing"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Natural mixed kernels paired through the center density\<close>

lemma slp_natural_mixed_positive_param_measurable:
  fixes M :: "'a measure"
    and left_pos left_neg right_pos right_neg :: "'a \<Rightarrow> nat \<Rightarrow> slp_point"
    and origin left_terminal right_terminal :: "'a \<Rightarrow> slp_point"
    and cutoff q qt T U Q :: slp_scalar_field
    and center_test :: "slp_point \<Rightarrow> ennreal"
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
    and T_measurable: "T \<in> borel_measurable lborel"
    and U_measurable: "U \<in> borel_measurable lborel"
    and Q_measurable: "Q \<in> borel_measurable lborel"
    and test_measurable: "center_test \<in> borel_measurable lborel"
    and left_pos_measurable:
      "left_pos \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and left_neg_measurable:
      "left_neg \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and right_pos_measurable:
      "right_pos \<in> measurable M (PiM {..<m} (\<lambda>_::nat. lborel))"
    and right_neg_measurable:
      "right_neg \<in> measurable M (PiM {..<m} (\<lambda>_::nat. lborel))"
    and origin_measurable: "origin \<in> measurable M lborel"
    and left_terminal_measurable: "left_terminal \<in> measurable M lborel"
    and right_terminal_measurable: "right_terminal \<in> measurable M lborel"
  shows "(\<lambda>z. ennreal (norm (Q (origin z))) *
      slp_left_branch_positive_kernel_list R cutoff q T
        (map (\<lambda>k. (left_pos z k, left_neg z k)) [0..<n])
        (origin z) (left_terminal z) *
      slp_left_branch_positive_kernel_list R cutoff qt U
        (map (\<lambda>k. (right_pos z k, right_neg z k)) [0..<m])
        (origin z) (right_terminal z) *
      center_test (slp_mixed_branch_center (origin z)
        (map (\<lambda>k. (left_pos z k, left_neg z k)) [0..<n]) (left_terminal z)
        (map (\<lambda>k. (right_pos z k, right_neg z k)) [0..<m]) (right_terminal z)))
    \<in> borel_measurable M"
proof -
  let ?left_pairs = "\<lambda>z. map (\<lambda>k. (left_pos z k, left_neg z k)) [0..<n]"
  let ?right_pairs = "\<lambda>z. map (\<lambda>k. (right_pos z k, right_neg z k)) [0..<m]"
  let ?left_out = "\<lambda>z. slp_left_branch_output (?left_pairs z) (left_terminal z)"
  let ?right_out = "\<lambda>z. slp_left_branch_output (?right_pairs z) (right_terminal z)"
  let ?center = "\<lambda>z. slp_mixed_branch_center (origin z)
    (?left_pairs z) (left_terminal z) (?right_pairs z) (right_terminal z)"
  have left_out_measurable: "?left_out \<in> measurable M lborel"
    by (rule slp_natural_branch_output_param_measurable[
          OF left_pos_measurable left_neg_measurable left_terminal_measurable])
  have right_out_measurable: "?right_out \<in> measurable M lborel"
    by (rule slp_natural_branch_output_param_measurable[
          OF right_pos_measurable right_neg_measurable right_terminal_measurable])
  have left_out_borel[measurable]: "?left_out \<in> borel_measurable M"
    using left_out_measurable by (simp only: measurable_lborel1)
  have right_out_borel[measurable]: "?right_out \<in> borel_measurable M"
    using right_out_measurable by (simp only: measurable_lborel1)
  have origin_borel[measurable]: "origin \<in> borel_measurable M"
    using origin_measurable by (simp only: measurable_lborel1)
  have center_borel: "?center \<in> borel_measurable M"
    by (simp only: slp_mixed_branch_center_def
          slp_left_branch_output_eq_right[symmetric]; measurable)
  have center_measurable: "?center \<in> measurable M lborel"
    using center_borel by (simp only: measurable_lborel1)
  have left_weighted:
    "(\<lambda>z. slp_left_branch_positive_kernel_list R cutoff q T
      (?left_pairs z) (origin z) (left_terminal z) * (1::ennreal))
      \<in> borel_measurable M"
    by (rule slp_natural_weighted_positive_kernel_param_measurable[
          where output_test = "\<lambda>_. 1",
          OF cutoff_measurable q_measurable T_measurable];
        (fact | measurable))
  have right_weighted:
    "(\<lambda>z. slp_left_branch_positive_kernel_list R cutoff qt U
      (?right_pairs z) (origin z) (right_terminal z) * (1::ennreal))
      \<in> borel_measurable M"
    by (rule slp_natural_weighted_positive_kernel_param_measurable[
          where output_test = "\<lambda>_. 1",
          OF cutoff_measurable qt_measurable U_measurable];
        (fact | measurable))
  have left_kernel_measurable[measurable]:
    "(\<lambda>z. slp_left_branch_positive_kernel_list R cutoff q T
      (?left_pairs z) (origin z) (left_terminal z)) \<in> borel_measurable M"
    using left_weighted by simp
  have right_kernel_measurable[measurable]:
    "(\<lambda>z. slp_left_branch_positive_kernel_list R cutoff qt U
      (?right_pairs z) (origin z) (right_terminal z)) \<in> borel_measurable M"
    using right_weighted by simp
  have root_value_measurable[measurable]:
    "(\<lambda>z. Q (origin z)) \<in> borel_measurable M"
    by (rule measurable_compose[OF origin_measurable Q_measurable])
  have weight_measurable[measurable]:
    "(\<lambda>z. center_test (?center z)) \<in> borel_measurable M"
    by (rule measurable_compose[OF center_measurable test_measurable])
  show ?thesis by measurable
qed

theorem slp_natural_mixed_positive_density_pairing:
  fixes n m :: nat and cutoff q qt T U Q :: slp_scalar_field
    and center_test :: "slp_point \<Rightarrow> ennreal"
  assumes cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and qt_measurable[measurable]: "qt \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and U_measurable[measurable]: "U \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and test_measurable[measurable]: "center_test \<in> borel_measurable lborel"
  shows "nn_integral
    (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M
      (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
      \<Otimes>\<^sub>M lborel)
    (\<lambda>((l,r),x). ennreal (norm (Q x)) *
      slp_left_branch_positive_kernel_list R cutoff q T
        (map (\<lambda>k. (fst (fst l) k, snd (fst l) k)) [0..<n]) x (snd l) *
      slp_left_branch_positive_kernel_list R cutoff qt U
        (map (\<lambda>k. (fst (fst r) k, snd (fst r) k)) [0..<m]) x (snd r) *
      center_test (slp_mixed_branch_center x
        (map (\<lambda>k. (fst (fst l) k, snd (fst l) k)) [0..<n]) (snd l)
        (map (\<lambda>k. (fst (fst r) k, snd (fst r) k)) [0..<m]) (snd r))) =
    nn_integral lborel (\<lambda>center. center_test center *
      slp_mixed_center_density R cutoff q qt
        (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q center)"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?N = "?BL \<Otimes>\<^sub>M ?BR"
  let ?MJ = "?N \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>l::((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times> slp_point.
    map (\<lambda>k. (fst (fst l) k, snd (fst l) k)) [0..<n]"
  let ?rp = "\<lambda>r::((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times> slp_point.
    map (\<lambda>k. (fst (fst r) k, snd (fst r) k)) [0..<m]"
  let ?OL = "\<lambda>l. slp_left_branch_output (?lp l) (snd l)"
  let ?OR = "\<lambda>r. slp_left_branch_output (?rp r) (snd r)"
  let ?KL = "\<lambda>x l. slp_left_branch_positive_kernel_list R cutoff q T (?lp l) x (snd l)"
  let ?KR = "\<lambda>x r. slp_left_branch_positive_kernel_list R cutoff qt U (?rp r) x (snd r)"
  let ?QN = "\<lambda>x. ennreal (norm (Q x))"
  let ?J = "\<lambda>z. ?QN (snd z) *
    ?KL (snd z) (fst (fst z)) * ?KR (snd z) (snd (fst z)) *
    center_test (slp_mixed_branch_center (snd z)
      (?lp (fst (fst z))) (snd (fst (fst z)))
      (?rp (snd (fst z))) (snd (snd (fst z))))"
  let ?DL = "slp_positive_output_density R cutoff q (\<lambda>s. ennreal (norm (T s))) n"
  let ?DR = "slp_positive_output_density R cutoff qt (\<lambda>t. ennreal (norm (U t))) m"
  let ?H = "\<lambda>x u. nn_integral lborel (\<lambda>v. center_test (-x + u + v) * ?DR x v)"
  have center_eq:
    "slp_mixed_branch_center x (?lp l) (snd l) (?rp r) (snd r) =
      -x + ?OL l + ?OR r" for x l r
    by (simp only: slp_mixed_branch_center_def slp_left_branch_output_eq_right[symmetric])
  have joint_measurable: "?J \<in> borel_measurable ?MJ"
    by (rule slp_natural_mixed_positive_param_measurable[
          OF cutoff_measurable q_measurable qt_measurable T_measurable
            U_measurable Q_measurable test_measurable]; measurable)
  interpret natural_product: product_sigma_finite
    "\<lambda>_::nat. (lborel :: slp_point measure)" by standard
  interpret left_family: sigma_finite_measure ?PL
    by (rule natural_product.sigma_finite) simp
  interpret right_family: sigma_finite_measure ?PR
    by (rule natural_product.sigma_finite) simp
  interpret left_arrays: pair_sigma_finite ?PL ?PL ..
  interpret right_arrays: pair_sigma_finite ?PR ?PR ..
  interpret left_array_measure: sigma_finite_measure "?PL \<Otimes>\<^sub>M ?PL" by standard
  interpret right_array_measure: sigma_finite_measure "?PR \<Otimes>\<^sub>M ?PR" by standard
  interpret left_coordinates: pair_sigma_finite
    "?PL \<Otimes>\<^sub>M ?PL" "lborel :: slp_point measure" ..
  interpret right_coordinates: pair_sigma_finite
    "?PR \<Otimes>\<^sub>M ?PR" "lborel :: slp_point measure" ..
  interpret left_measure: sigma_finite_measure ?BL by standard
  interpret right_measure: sigma_finite_measure ?BR by standard
  interpret branches: pair_sigma_finite ?BL ?BR ..
  interpret passive_measure: sigma_finite_measure ?N by standard
  interpret full_measure: pair_sigma_finite ?N "lborel :: slp_point measure" ..
  have T_weight[measurable]: "(\<lambda>s. ennreal (norm (T s))) \<in> borel_measurable lborel"
    by measurable
  have U_weight[measurable]: "(\<lambda>t. ennreal (norm (U t))) \<in> borel_measurable lborel"
    by measurable
  have left_density[measurable]: "case_prod ?DL \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable[
          OF cutoff_measurable q_measurable T_weight])
  have right_density[measurable]: "case_prod ?DR \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable[
          OF cutoff_measurable qt_measurable U_weight])
  have H_joint: "(\<lambda>z. ?H (fst z) (snd z)) \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have H_slice[measurable]: "?H x \<in> borel_measurable lborel" for x
    using measurable_Pair2[OF H_joint, where x = x] by simp
  have right_test[measurable]:
    "(\<lambda>v. center_test (-x + ?OL l + v)) \<in> borel_measurable lborel" for x l
    by measurable
  have right_weighted:
    "(\<lambda>r. ?KR x r * center_test (-x + ?OL l + ?OR r)) \<in> borel_measurable ?BR"
    for x l
    by (rule slp_natural_weighted_positive_kernel_param_measurable[
          where output_test = "\<lambda>v. center_test (-x + ?OL l + v)",
          OF cutoff_measurable qt_measurable U_measurable right_test]; measurable)
  have right_pairing:
    "nn_integral ?BR (\<lambda>r. ?KR x r * center_test (-x + ?OL l + ?OR r)) =
      ?H x (?OL l)" for x l
    by (rule slp_left_branch_positive_kernel_natural_joint_output_density_pairing[
          where output_test = "\<lambda>v. center_test (-x + ?OL l + v)",
          OF cutoff_measurable qt_measurable U_measurable right_test])
  have left_weighted:
    "(\<lambda>l. ?KL x l * ?H x (?OL l)) \<in> borel_measurable ?BL" for x
    by (rule slp_natural_weighted_positive_kernel_param_measurable[
          where output_test = "?H x",
          OF cutoff_measurable q_measurable T_measurable H_slice]; measurable)
  have left_pairing:
    "nn_integral ?BL (\<lambda>l. ?KL x l * ?H x (?OL l)) =
      nn_integral lborel (\<lambda>u. ?H x u * ?DL x u)" for x
    by (rule slp_left_branch_positive_kernel_natural_joint_output_density_pairing[
          where output_test = "?H x",
          OF cutoff_measurable q_measurable T_measurable H_slice])
  have density_weighted:
    "(\<lambda>u. ?H x u * ?DL x u) \<in> borel_measurable lborel" for x
    by measurable
  have collapse_right:
    "nn_integral ?BR (\<lambda>r.
      ?QN x * ?KL x l * ?KR x r * center_test (-x + ?OL l + ?OR r)) =
      ?QN x * ?KL x l * ?H x (?OL l)" for x l
  proof -
    have pull:
      "nn_integral ?BR (\<lambda>r.
        ?QN x * ?KL x l * ?KR x r * center_test (-x + ?OL l + ?OR r)) =
        (?QN x * ?KL x l) * nn_integral ?BR
          (\<lambda>r. ?KR x r * center_test (-x + ?OL l + ?OR r))"
      using nn_integral_cmult[OF right_weighted[of x l],
        where c = "?QN x * ?KL x l"]
      by (simp only: mult.assoc)
    show ?thesis using pull by (simp only: right_pairing)
  qed
  have collapse_left:
    "nn_integral ?BL (\<lambda>l. ?QN x * ?KL x l * ?H x (?OL l)) =
      nn_integral lborel (\<lambda>u. ?QN x * ?DL x u * ?H x u)" for x
  proof -
    have pull:
      "nn_integral ?BL (\<lambda>l. ?QN x * ?KL x l * ?H x (?OL l)) =
        ?QN x * nn_integral ?BL (\<lambda>l. ?KL x l * ?H x (?OL l))"
      using nn_integral_cmult[OF left_weighted[of x], where c = "?QN x"]
      by (simp only: mult.assoc)
    also have "\<dots> = ?QN x * nn_integral lborel (\<lambda>u. ?H x u * ?DL x u)"
      by (simp only: left_pairing)
    also have "\<dots> = nn_integral lborel (\<lambda>u. ?QN x * ?DL x u * ?H x u)"
      using nn_integral_cmult[OF density_weighted[of x], where c = "?QN x"]
      by (simp add: mult.commute mult.left_commute mult.assoc)
    finally show ?thesis .
  qed
  have root_section:
    "(\<lambda>z. ?J (z,x)) \<in> borel_measurable ?N" for x
    using measurable_Pair1[OF joint_measurable, where y = x] by simp
  have right_sigma: "sigma_finite_measure ?BR" by standard
  have root_expansion:
    "nn_integral ?N (\<lambda>z. ?J (z,x)) =
      nn_integral ?BL (\<lambda>l. nn_integral ?BR (\<lambda>r.
        ?QN x * ?KL x l * ?KR x r * center_test (-x + ?OL l + ?OR r)))" for x
    using sigma_finite_measure.nn_integral_fst[OF right_sigma root_section[of x]]
    by (simp only: fst_conv snd_conv center_eq)
  have root_value:
    "nn_integral ?N (\<lambda>z. ?J (z,x)) =
      nn_integral lborel (\<lambda>u. ?QN x * ?DL x u * ?H x u)" for x
    by (simp only: root_expansion collapse_right collapse_left)
  have move_root:
    "nn_integral ?MJ ?J =
      nn_integral lborel (\<lambda>x. nn_integral ?N (\<lambda>z. ?J (z,x)))"
    using full_measure.nn_integral_snd[OF joint_measurable] by simp
  have raw_to_density:
    "nn_integral ?MJ ?J =
      nn_integral lborel (\<lambda>x. nn_integral lborel
        (\<lambda>u. ?QN x * ?DL x u * ?H x u))"
    using move_root by (simp only: root_value)
  note existing_pairing = slp_mixed_center_density_pairing[
    where R = R and left_order = n and right_order = m,
    OF test_measurable cutoff_measurable q_measurable qt_measurable
      T_weight U_weight Q_measurable]
  have density_to_center:
    "nn_integral lborel (\<lambda>x. nn_integral lborel
      (\<lambda>u. ?QN x * ?DL x u * ?H x u)) =
      nn_integral lborel (\<lambda>center. center_test center *
        slp_mixed_center_density R cutoff q qt
          (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q center)"
    using existing_pairing[symmetric]
    by (simp only: slp_left_positive_output_density_def slp_right_positive_output_density_def)
  note combined = trans[OF raw_to_density density_to_center]
  show ?thesis using combined by (simp only: case_prod_unfold)
qed

end
