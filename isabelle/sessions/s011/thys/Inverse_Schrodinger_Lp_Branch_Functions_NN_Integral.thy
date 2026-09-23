theory Inverse_Schrodinger_Lp_Branch_Functions_NN_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Branch_Coordinates_NN_Integral"
begin

section \<open>Nonnegative integration on branch-coordinate functions\<close>

theorem slp_nn_integral_branch_coordinate_functions:
  fixes F :: "((('a::euclidean_space^'i::finite) \<times>
      ('b::euclidean_space^'j::finite)) \<times>
      'c::euclidean_space) \<Rightarrow> ennreal"
  assumes F_measurable: "F \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ coordinates. F coordinates \<partial>lborel) =
      (\<integral>\<^sup>+ pos_family. \<integral>\<^sup>+ neg_family.
        \<integral>\<^sup>+ terminal.
          F (((\<chi> i. pos_family i), (\<chi> j. neg_family j)), terminal)
          \<partial>lborel
        \<partial>(PiM UNIV (\<lambda>_::'j. (lborel :: 'b measure)))
      \<partial>(PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))))"
proof -
  let ?MP = "lborel :: ('a^'i) measure"
  let ?MN = "lborel :: ('b^'j) measure"
  let ?MT = "lborel :: 'c measure"
  let ?MPN = "lborel :: (('a^'i) \<times> ('b^'j)) measure"
  let ?PP = "PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))"
  let ?PN = "PiM UNIV (\<lambda>_::'j. (lborel :: 'b measure))"
  let ?VP = "\<lambda>f::'i \<Rightarrow> 'a. \<chi> i. f i"
  let ?VN = "\<lambda>f::'j \<Rightarrow> 'b. \<chi> j. f j"
  let ?G = "\<lambda>pair_coordinates.
    \<integral>\<^sup>+ terminal. F (pair_coordinates, terminal) \<partial>?MT"
  let ?H = "\<lambda>pos. \<integral>\<^sup>+ neg. ?G (pos, neg) \<partial>?MN"
  have F_product_measurable:
      "F \<in> borel_measurable (?MPN \<Otimes>\<^sub>M ?MT)"
    using F_measurable by (simp only: lborel_prod)
  have G_measurable: "?G \<in> borel_measurable ?MPN"
    by (rule lborel.borel_measurable_nn_integral_fst[OF
          F_product_measurable])
  have G_product_measurable:
      "?G \<in> borel_measurable (?MP \<Otimes>\<^sub>M ?MN)"
    using G_measurable by (simp only: lborel_prod)
  have H_measurable: "?H \<in> borel_measurable ?MP"
    by (rule lborel.borel_measurable_nn_integral_fst[OF
          G_product_measurable])
  have outer_transport:
      "(\<integral>\<^sup>+ pos. ?H pos \<partial>?MP) =
        (\<integral>\<^sup>+ pos_family. ?H (?VP pos_family) \<partial>?PP)"
    by (rule slp_nn_integral_cartesian_euclidean_vector_product[OF
          H_measurable])
  have G_slice_measurable:
      "\<And>pos. (\<lambda>neg. ?G (pos, neg)) \<in> borel_measurable ?MN"
    using G_product_measurable by measurable
  have inner_transport:
      "\<And>pos. (\<integral>\<^sup>+ neg. ?G (pos, neg) \<partial>?MN) =
        (\<integral>\<^sup>+ neg_family. ?G (pos, ?VN neg_family) \<partial>?PN)"
    by (rule slp_nn_integral_cartesian_euclidean_vector_product[OF
          G_slice_measurable])
  have family_transport:
      "(\<integral>\<^sup>+ pos. ?H pos \<partial>?MP) =
          (\<integral>\<^sup>+ pos_family. \<integral>\<^sup>+ neg_family.
          ?G (?VP pos_family, ?VN neg_family) \<partial>?PN \<partial>?PP)"
  proof -
    have inner_cong:
          "(\<integral>\<^sup>+ pos_family. ?H (?VP pos_family) \<partial>?PP) =
          (\<integral>\<^sup>+ pos_family. \<integral>\<^sup>+ neg_family.
            ?G (?VP pos_family, ?VN neg_family) \<partial>?PN \<partial>?PP)"
      by (rule nn_integral_cong, simp only: inner_transport)
    show ?thesis
      using outer_transport inner_cong by simp
  qed
  note branch_split = slp_nn_integral_branch_coordinates[OF F_measurable]
  show ?thesis
    using branch_split family_transport by simp
qed

end
