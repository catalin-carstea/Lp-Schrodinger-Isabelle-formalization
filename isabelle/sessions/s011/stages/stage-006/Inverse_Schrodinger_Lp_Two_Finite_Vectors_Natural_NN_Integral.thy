theory Inverse_Schrodinger_Lp_Two_Finite_Vectors_Natural_NN_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Branch_Natural_NN_Integral"
begin

section \<open>Natural coordinates for two finite Euclidean vectors\<close>

theorem slp_nn_integral_two_finite_vectors_natural_coordinates:
  fixes F :: "(('a::euclidean_space^'i::finite) \<times>
      ('b::euclidean_space^'j::finite)) \<Rightarrow> ennreal"
  assumes F_measurable: "F \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ coordinates. F coordinates \<partial>lborel) =
      (\<integral>\<^sup>+ pos_natural. \<integral>\<^sup>+ neg_natural.
        F ((\<chi> i. pos_natural (to_nat_on UNIV i)),
          (\<chi> j. neg_natural (to_nat_on UNIV j)))
        \<partial>(PiM {..<CARD('j)}
          (\<lambda>_::nat. (lborel :: 'b measure)))
      \<partial>(PiM {..<CARD('i)}
        (\<lambda>_::nat. (lborel :: 'a measure))))"
proof -
  let ?MP = "lborel :: ('a^'i) measure"
  let ?MN = "lborel :: ('b^'j) measure"
  let ?PP = "PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))"
  let ?PN = "PiM UNIV (\<lambda>_::'j. (lborel :: 'b measure))"
  let ?RP = "PiM {..<CARD('i)}
    (\<lambda>_::nat. (lborel :: 'a measure))"
  let ?RN = "PiM {..<CARD('j)}
    (\<lambda>_::nat. (lborel :: 'b measure))"
  let ?VP = "\<lambda>f::'i \<Rightarrow> 'a. \<chi> i. f i"
  let ?VN = "\<lambda>f::'j \<Rightarrow> 'b. \<chi> j. f j"
  let ?TP = "\<lambda>omega. \<lambda>i\<in>(UNIV::'i set).
    omega (to_nat_on UNIV i)"
  let ?TN = "\<lambda>omega. \<lambda>j\<in>(UNIV::'j set).
    omega (to_nat_on UNIV j)"
  let ?H = "\<lambda>pos. \<integral>\<^sup>+ neg. F (pos, neg) \<partial>?MN"
  have F_product_measurable:
      "F \<in> borel_measurable (?MP \<Otimes>\<^sub>M ?MN)"
    using F_measurable by (simp only: lborel_prod)
  have H_measurable: "?H \<in> borel_measurable ?MP"
    by (rule lborel.borel_measurable_nn_integral_fst[OF
          F_product_measurable])
  have pair_split:
      "(\<integral>\<^sup>+ coordinates. F coordinates \<partial>lborel) =
        (\<integral>\<^sup>+ pos. ?H pos \<partial>?MP)"
  proof -
    note raw = lborel.nn_integral_fst[OF F_product_measurable]
    show ?thesis
      using raw[symmetric] by (simp only: lborel_prod)
  qed
  have VP_measurable: "?VP \<in> measurable ?PP borel"
    by (rule slp_euclidean_vector_constructor_measurable)
  have VN_measurable: "?VN \<in> measurable ?PN borel"
    by (rule slp_euclidean_vector_constructor_measurable)
  have outer_cartesian:
      "(\<integral>\<^sup>+ pos. ?H pos \<partial>?MP) =
        (\<integral>\<^sup>+ pos_family. ?H (?VP pos_family) \<partial>?PP)"
    by (rule slp_nn_integral_cartesian_euclidean_vector_product[OF
          H_measurable])
  have H_borel_measurable: "?H \<in> borel_measurable borel"
    using H_measurable
    by (simp only: measurable_lborel1 measurable_lborel2)
  have outer_family_measurable:
      "(\<lambda>pos_family. ?H (?VP pos_family)) \<in>
        borel_measurable ?PP"
    using measurable_comp[OF VP_measurable H_borel_measurable]
    by (simp only: comp_def)
  have outer_natural:
      "(\<integral>\<^sup>+ pos_family. ?H (?VP pos_family) \<partial>?PP) =
        (\<integral>\<^sup>+ pos_natural. ?H (?VP (?TP pos_natural))
          \<partial>?RP)"
    by (rule slp_nn_integral_uniform_finite_nat_reindex[OF
          outer_family_measurable])
  have F_slice_measurable:
      "\<And>pos. (\<lambda>neg. F (pos, neg)) \<in> borel_measurable ?MN"
    using F_product_measurable by measurable
  have inner_cartesian:
      "\<And>pos.
        (\<integral>\<^sup>+ neg. F (pos, neg) \<partial>?MN) =
        (\<integral>\<^sup>+ neg_family. F (pos, ?VN neg_family) \<partial>?PN)"
    by (rule slp_nn_integral_cartesian_euclidean_vector_product[OF
          F_slice_measurable])
  have inner_family_measurable:
      "\<And>pos. (\<lambda>neg_family. F (pos, ?VN neg_family)) \<in>
        borel_measurable ?PN"
  proof -
    fix pos
    have slice_borel:
        "(\<lambda>neg. F (pos, neg)) \<in> borel_measurable borel"
      using F_slice_measurable[of pos]
      by (simp only: measurable_lborel1 measurable_lborel2)
    show "(\<lambda>neg_family. F (pos, ?VN neg_family)) \<in>
        borel_measurable ?PN"
      using measurable_comp[OF VN_measurable slice_borel]
      by (simp only: comp_def)
  qed
  have inner_natural:
      "\<And>pos.
        (\<integral>\<^sup>+ neg_family. F (pos, ?VN neg_family) \<partial>?PN) =
        (\<integral>\<^sup>+ neg_natural.
          F (pos, ?VN (?TN neg_natural)) \<partial>?RN)"
    by (rule slp_nn_integral_uniform_finite_nat_reindex[OF
          inner_family_measurable])
  have inner_transport:
      "\<And>pos.
        (\<integral>\<^sup>+ neg. F (pos, neg) \<partial>?MN) =
        (\<integral>\<^sup>+ neg_natural.
          F (pos, ?VN (?TN neg_natural)) \<partial>?RN)"
    using trans[OF inner_cartesian inner_natural] .
  have TP_vector:
      "\<And>pos_natural. ?VP (?TP pos_natural) =
        (\<chi> i. pos_natural (to_nat_on UNIV i))"
    unfolding vec_eq_iff
    by (intro allI)
      (simp only: vec_lambda_beta restrict_apply UNIV_I if_True)
  have TN_vector:
      "\<And>neg_natural. ?VN (?TN neg_natural) =
        (\<chi> j. neg_natural (to_nat_on UNIV j))"
    unfolding vec_eq_iff
    by (intro allI)
      (simp only: vec_lambda_beta restrict_apply UNIV_I if_True)
  show ?thesis
    using pair_split outer_cartesian outer_natural
    by (simp only: inner_transport TP_vector TN_vector)
qed

end
