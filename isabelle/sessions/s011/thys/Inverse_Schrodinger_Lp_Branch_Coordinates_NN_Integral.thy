theory Inverse_Schrodinger_Lp_Branch_Coordinates_NN_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cartesian_Euclidean_NN_Integral"
begin

section \<open>Tonelli expansion of finite branch coordinates\<close>

theorem slp_nn_integral_branch_coordinates:
  fixes F :: "((('a::euclidean_space^'i::finite) \<times>
      ('b::euclidean_space^'j::finite)) \<times>
      'c::euclidean_space) \<Rightarrow> ennreal"
  assumes F_measurable:
      "F \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ coordinates. F coordinates \<partial>lborel) =
      (\<integral>\<^sup>+ pos. \<integral>\<^sup>+ neg. \<integral>\<^sup>+ terminal.
        F ((pos, neg), terminal)
        \<partial>lborel \<partial>lborel \<partial>lborel)"
proof -
  let ?MP = "lborel :: ('a^'i) measure"
  let ?MN = "lborel :: ('b^'j) measure"
  let ?MT = "lborel :: 'c measure"
  let ?MPN = "lborel :: (('a^'i) \<times> ('b^'j)) measure"
  let ?G = "\<lambda>pair_coordinates.
    \<integral>\<^sup>+ terminal. F (pair_coordinates, terminal) \<partial>?MT"
  have F_product_measurable:
      "F \<in> borel_measurable (?MPN \<Otimes>\<^sub>M ?MT)"
    using F_measurable by (simp only: lborel_prod)
  have G_measurable: "?G \<in> borel_measurable ?MPN"
    by (rule lborel.borel_measurable_nn_integral_fst[OF
          F_product_measurable])
  have G_product_measurable:
      "?G \<in> borel_measurable (?MP \<Otimes>\<^sub>M ?MN)"
    using G_measurable by (simp only: lborel_prod)
  have terminal_split:
      "(\<integral>\<^sup>+ coordinates. F coordinates \<partial>lborel) =
        (\<integral>\<^sup>+ pair_coordinates. ?G pair_coordinates \<partial>?MPN)"
  proof -
    note split = lborel.nn_integral_fst[OF F_product_measurable]
    show ?thesis
      using split[symmetric] by (simp only: lborel_prod)
  qed
  have pair_split:
      "(\<integral>\<^sup>+ pair_coordinates. ?G pair_coordinates \<partial>?MPN) =
        (\<integral>\<^sup>+ pos. \<integral>\<^sup>+ neg. ?G (pos, neg)
          \<partial>?MN \<partial>?MP)"
  proof -
    note split = lborel.nn_integral_fst[OF G_product_measurable]
    show ?thesis
      using split[symmetric] by (simp only: lborel_prod)
  qed
  show ?thesis
    using terminal_split pair_split by simp
qed

end
