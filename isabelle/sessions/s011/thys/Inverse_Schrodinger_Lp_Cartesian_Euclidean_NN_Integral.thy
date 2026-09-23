theory Inverse_Schrodinger_Lp_Cartesian_Euclidean_NN_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Point_Family_Boolean_Transport"
begin

section \<open>Nonnegative integration on finite Euclidean families\<close>

theorem slp_nn_integral_cartesian_euclidean_vector_product:
  fixes F :: "('a::euclidean_space^'i::finite) \<Rightarrow> ennreal"
  assumes F_measurable:
      "F \<in> borel_measurable (lborel :: ('a^'i) measure)"
  shows
    "(\<integral>\<^sup>+ x. F x \<partial>(lborel :: ('a^'i) measure)) =
      (\<integral>\<^sup>+ f. F (\<chi> i. f i)
        \<partial>(PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))))"
proof -
  let ?P = "PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))"
  let ?V = "\<lambda>f::'i \<Rightarrow> 'a. \<chi> i. f i"
  have V_measurable: "?V \<in> measurable ?P borel"
    by (rule slp_euclidean_vector_constructor_measurable)
  have source_measure:
      "(lborel :: ('a^'i) measure) = distr ?P borel ?V"
    by (rule slp_lborel_cartesian_euclidean_vector_product)
  have F_distr_measurable:
      "F \<in> borel_measurable (distr ?P borel ?V)"
    using F_measurable by (simp only: source_measure[symmetric])
  have transported:
      "(\<integral>\<^sup>+ x. F x \<partial>(distr ?P borel ?V)) =
        (\<integral>\<^sup>+ f. F (?V f) \<partial>?P)"
    by (rule nn_integral_distr[OF V_measurable F_distr_measurable])
  show ?thesis
    using transported by (simp only: source_measure)
qed

end
