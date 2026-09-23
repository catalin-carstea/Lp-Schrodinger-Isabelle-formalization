theory Inverse_Schrodinger_Lp_Natural_Branch_Pair_List
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Inner_Mass_Natural"
begin

section \<open>The finite branch-pair list in natural coordinates\<close>

lemma slp_finite_branch_pair_list_natural_coordinates:
  fixes branch_dummy :: "'i::finite itself"
    and pos_natural neg_natural :: "nat \<Rightarrow> slp_point"
  shows
    "slp_finite_branch_pair_list
        (\<lambda>i::'i. pos_natural (to_nat_on UNIV i))
        (\<lambda>i::'i. neg_natural (to_nat_on UNIV i)) =
      map (\<lambda>k. (pos_natural k, neg_natural k)) [0..<CARD('i)]"
proof -
  have enumeration:
      "bij_betw (to_nat_on (UNIV :: 'i set)) UNIV {..<CARD('i)}"
    by (rule to_nat_on_finite) simp
  have enumeration_image:
      "to_nat_on (UNIV :: 'i set) ` UNIV = {..<CARD('i)}"
    by (rule bij_betw_imp_surj_on[OF enumeration])
  show ?thesis
    unfolding slp_finite_branch_pair_list_def
  proof (rule map_cong)
    show "[0..<CARD('i)] = [0..<CARD('i)]"
      by (rule refl)
    fix k
    assume k_mem: "k \<in> set [0..<CARD('i)]"
    have k_image:
        "k \<in> to_nat_on (UNIV :: 'i set) ` UNIV"
      using k_mem enumeration_image by simp
    have cancel:
        "to_nat_on (UNIV :: 'i set) (from_nat_into UNIV k) = k"
      by (rule to_nat_on_from_nat_into[OF k_image])
    show
      "(pos_natural
          (to_nat_on (UNIV :: 'i set) (from_nat_into UNIV k)),
        neg_natural
          (to_nat_on (UNIV :: 'i set) (from_nat_into UNIV k))) =
        (pos_natural k, neg_natural k)"
      by (simp only: cancel)
  qed
qed

end
