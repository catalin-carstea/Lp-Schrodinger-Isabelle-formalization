theory Inverse_Schrodinger_Lp_Branch_Natural_NN_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Branch_Functions_NN_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Finite_Product_Nat_NN_Integral"
begin

section \<open>Natural coordinates for both finite branch families\<close>

theorem slp_nn_integral_branch_natural_coordinates:
  fixes F :: "((('a::euclidean_space^'i::finite) \<times>
      ('b::euclidean_space^'j::finite)) \<times>
      'c::euclidean_space) \<Rightarrow> ennreal"
  assumes F_measurable: "F \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ coordinates. F coordinates \<partial>lborel) =
      (\<integral>\<^sup>+ pos_natural. \<integral>\<^sup>+ neg_natural.
        \<integral>\<^sup>+ terminal.
          F (((\<chi> i. pos_natural (to_nat_on UNIV i)),
              (\<chi> j. neg_natural (to_nat_on UNIV j))), terminal)
          \<partial>lborel
        \<partial>(PiM {..<CARD('j)}
          (\<lambda>_::nat. (lborel :: 'b measure)))
      \<partial>(PiM {..<CARD('i)}
        (\<lambda>_::nat. (lborel :: 'a measure))))"
proof -
  let ?PP = "PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))"
  let ?PN = "PiM UNIV (\<lambda>_::'j. (lborel :: 'b measure))"
  let ?RP = "PiM {..<CARD('i)}
    (\<lambda>_::nat. (lborel :: 'a measure))"
  let ?RN = "PiM {..<CARD('j)}
    (\<lambda>_::nat. (lborel :: 'b measure))"
  let ?MT = "lborel :: 'c measure"
  let ?VP = "\<lambda>f::'i \<Rightarrow> 'a. \<chi> i. f i"
  let ?VN = "\<lambda>f::'j \<Rightarrow> 'b. \<chi> j. f j"
  let ?TP = "\<lambda>omega. \<lambda>i\<in>(UNIV::'i set).
    omega (to_nat_on UNIV i)"
  let ?TN = "\<lambda>omega. \<lambda>j\<in>(UNIV::'j set).
    omega (to_nat_on UNIV j)"
  let ?G = "\<lambda>(pos_family, neg_family).
    \<integral>\<^sup>+ terminal.
      F ((?VP pos_family, ?VN neg_family), terminal) \<partial>?MT"
  let ?H = "\<lambda>pos_family.
    \<integral>\<^sup>+ neg_family. ?G (pos_family, neg_family) \<partial>?PN"
  have VP_measurable: "?VP \<in> measurable ?PP borel"
    by (rule slp_euclidean_vector_constructor_measurable)
  have VN_measurable: "?VN \<in> measurable ?PN borel"
    by (rule slp_euclidean_vector_constructor_measurable)
  have F_borel_measurable: "F \<in> borel_measurable borel"
    using F_measurable
    by (simp only: lborel_prod measurable_lborel1 measurable_lborel2)
  have joint_terminal_measurable:
      "(\<lambda>((pos_family, neg_family), terminal).
        F ((?VP pos_family, ?VN neg_family), terminal)) \<in>
        borel_measurable ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT)"
  proof -
    have family_projection:
        "fst \<in> measurable ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT)
          (?PP \<Otimes>\<^sub>M ?PN)"
      by (rule measurable_fst)
    have pos_projection:
        "(fst \<circ> fst) \<in> measurable
          ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT) ?PP"
      using measurable_compose[OF family_projection measurable_fst]
      by (simp only: comp_def)
    have neg_projection:
        "(snd \<circ> fst) \<in> measurable
          ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT) ?PN"
      using measurable_compose[OF family_projection measurable_snd]
      by (simp only: comp_def)
    have pos_on_source:
        "(\<lambda>((pos_family, neg_family), terminal). ?VP pos_family) \<in>
          measurable ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT) borel"
      using measurable_compose[OF pos_projection VP_measurable]
      by (simp only: comp_def split_beta')
    have neg_on_source:
        "(\<lambda>((pos_family, neg_family), terminal). ?VN neg_family) \<in>
          measurable ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT) borel"
      using measurable_compose[OF neg_projection VN_measurable]
      by (simp only: comp_def split_beta')
    have terminal_on_source:
        "(\<lambda>((pos_family, neg_family), terminal). terminal) \<in>
          measurable ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT) borel"
    proof -
      have terminal_projection:
          "snd \<in> measurable ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT) ?MT"
        by (rule measurable_snd)
      show ?thesis
        using terminal_projection
        by (simp only: measurable_lborel1 split_beta')
    qed
    have family_pair_measurable:
        "(\<lambda>((pos_family, neg_family), terminal).
          (?VP pos_family, ?VN neg_family)) \<in>
          measurable ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT)
            (borel \<Otimes>\<^sub>M borel)"
    proof -
      note raw = measurable_Pair[OF pos_on_source neg_on_source]
      show ?thesis
        using raw by (simp only: split_beta')
    qed
    have coordinate_product_measurable:
        "(\<lambda>((pos_family, neg_family), terminal).
          ((?VP pos_family, ?VN neg_family), terminal)) \<in>
          measurable ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT)
            ((borel \<Otimes>\<^sub>M borel) \<Otimes>\<^sub>M borel)"
    proof -
      note raw = measurable_Pair[OF family_pair_measurable terminal_on_source]
      show ?thesis
        using raw by (simp only: split_beta')
    qed
    have coordinate_measurable:
        "(\<lambda>((pos_family, neg_family), terminal).
        ((?VP pos_family, ?VN neg_family), terminal)) \<in>
        measurable ((?PP \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M ?MT) borel"
      using coordinate_product_measurable by (simp only: borel_prod)
    note composed = measurable_comp[OF coordinate_measurable F_borel_measurable]
    show ?thesis
      using composed by (simp only: comp_def split_beta')
  qed
  have G_measurable:
      "?G \<in> borel_measurable (?PP \<Otimes>\<^sub>M ?PN)"
  proof -
    note raw = lborel.borel_measurable_nn_integral_fst[OF
      joint_terminal_measurable]
    show ?thesis
      using raw by (simp only: split_beta' fst_conv snd_conv)
  qed
  interpret neg_product:
    product_sigma_finite "\<lambda>_::'j. (lborel :: 'b measure)"
    by standard
  have PN_sigma: "sigma_finite_measure ?PN"
    by (rule neg_product.sigma_finite) simp
  interpret negative: sigma_finite_measure ?PN
    by (rule PN_sigma)
  have H_measurable: "?H \<in> borel_measurable ?PP"
  proof -
    note raw = negative.borel_measurable_nn_integral_fst[OF G_measurable]
    show ?thesis
      using raw by (simp only: split_beta' fst_conv snd_conv)
  qed
  have G_slice_measurable:
      "\<And>pos_family. (\<lambda>neg_family.
        ?G (pos_family, neg_family)) \<in> borel_measurable ?PN"
  proof -
    fix pos_family
    have pos_in_space: "pos_family \<in> space ?PP"
      by (simp add: space_PiM PiE_iff)
    have pos_constant:
        "(\<lambda>_::'j \<Rightarrow> 'b. pos_family) \<in> measurable ?PN ?PP"
      by (rule measurable_const[OF pos_in_space])
    have pair_measurable:
        "(\<lambda>neg_family. (pos_family, neg_family)) \<in>
          measurable ?PN (?PP \<Otimes>\<^sub>M ?PN)"
    proof -
      note raw = measurable_Pair[OF pos_constant measurable_ident]
      show ?thesis
        using raw by (simp only: id_def)
    qed
    note composed = measurable_comp[OF pair_measurable G_measurable]
    show "(\<lambda>neg_family. ?G (pos_family, neg_family)) \<in>
        borel_measurable ?PN"
      using composed by (simp only: comp_def split_beta')
  qed
  have outer_transport:
      "(\<integral>\<^sup>+ pos_family. ?H pos_family \<partial>?PP) =
        (\<integral>\<^sup>+ pos_natural. ?H (?TP pos_natural) \<partial>?RP)"
    by (rule slp_nn_integral_uniform_finite_nat_reindex[OF H_measurable])
  have inner_transport:
      "\<And>pos_family.
        (\<integral>\<^sup>+ neg_family. ?G (pos_family, neg_family) \<partial>?PN) =
        (\<integral>\<^sup>+ neg_natural.
          ?G (pos_family, ?TN neg_natural) \<partial>?RN)"
    by (rule slp_nn_integral_uniform_finite_nat_reindex[OF
          G_slice_measurable])
  have family_transport:
      "(\<integral>\<^sup>+ pos_family. ?H pos_family \<partial>?PP) =
        (\<integral>\<^sup>+ pos_natural. \<integral>\<^sup>+ neg_natural.
          ?G (?TP pos_natural, ?TN neg_natural) \<partial>?RN \<partial>?RP)"
  proof -
    have inner_cong:
        "(\<integral>\<^sup>+ pos_natural. ?H (?TP pos_natural) \<partial>?RP) =
          (\<integral>\<^sup>+ pos_natural. \<integral>\<^sup>+ neg_natural.
            ?G (?TP pos_natural, ?TN neg_natural) \<partial>?RN \<partial>?RP)"
      by (rule nn_integral_cong, simp only: inner_transport)
    show ?thesis
      using outer_transport inner_cong by simp
  qed
  note branch_functions =
    slp_nn_integral_branch_coordinate_functions[OF F_measurable]
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
    using branch_functions family_transport
    by (simp only: TP_vector TN_vector split_beta' fst_conv snd_conv)
qed

end
