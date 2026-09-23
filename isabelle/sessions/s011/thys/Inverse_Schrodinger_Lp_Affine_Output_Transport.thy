theory Inverse_Schrodinger_Lp_Affine_Output_Transport
  imports Inverse_Schrodinger_Lp_Born_Output_Density_Measurable
begin

section \<open>Affine Tonelli transport for branch outputs\<close>

lemma slp_nn_integral_translate:
  fixes f :: "slp_point \<Rightarrow> ennreal"
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+ x. f (shift + x) \<partial>lborel) =
    (\<integral>\<^sup>+ x. f x \<partial>lborel)"
proof -
  have add_measurable: "(+) shift \<in> measurable lborel borel"
    by measurable
  have f_distr_measurable:
      "f \<in> borel_measurable (distr lborel borel ((+) shift))"
    using f_measurable by (simp only: lborel_distr_plus)
  have distr_formula:
      "(\<integral>\<^sup>+ x. f x \<partial>distr lborel borel ((+) shift)) =
        (\<integral>\<^sup>+ x. f (shift + x) \<partial>lborel)"
    by (rule nn_integral_distr[OF add_measurable f_distr_measurable])
  show ?thesis
    using distr_formula by (simp only: lborel_distr_plus)
qed

theorem slp_nn_integral_affine_output_transport:
  fixes test :: "slp_point \<Rightarrow> ennreal"
    and block_weight :: "slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
    and inner_density :: "slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
  assumes test_measurable[measurable]: "test \<in> borel_measurable lborel"
    and block_weight_measurable[measurable]:
      "case_prod block_weight \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and inner_density_measurable[measurable]:
      "case_prod inner_density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  shows
    "(\<integral>\<^sup>+ output. test output *
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          block_weight pos_point neg_point *
          inner_density neg_point (output - pos_point + neg_point)
          \<partial>lborel \<partial>lborel) \<partial>lborel) =
     (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        block_weight pos_point neg_point *
        (\<integral>\<^sup>+ inner_output.
          test (inner_output + pos_point - neg_point) *
          inner_density neg_point inner_output \<partial>lborel)
        \<partial>lborel \<partial>lborel)"
proof -
  let ?integrand = "\<lambda>output pos_point neg_point.
    test output * block_weight pos_point neg_point *
      inner_density neg_point (output - pos_point + neg_point)"
  have expand_left:
      "(\<integral>\<^sup>+ output. test output *
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            block_weight pos_point neg_point *
            inner_density neg_point (output - pos_point + neg_point)
            \<partial>lborel \<partial>lborel) \<partial>lborel) =
        (\<integral>\<^sup>+ output. \<integral>\<^sup>+ pos_point.
          \<integral>\<^sup>+ neg_point. ?integrand output pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel)"
    by (intro nn_integral_cong)
      (simp add: nn_integral_cmult mult.assoc)
  have output_pos_measurable:
      "case_prod (\<lambda>output pos_point.
        \<integral>\<^sup>+ neg_point. ?integrand output pos_point neg_point
          \<partial>lborel) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have swap_output_pos:
      "(\<integral>\<^sup>+ output. \<integral>\<^sup>+ pos_point.
          \<integral>\<^sup>+ neg_point. ?integrand output pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ output.
          \<integral>\<^sup>+ neg_point. ?integrand output pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel)"
    using lborel_pair.Fubini'[OF output_pos_measurable] by simp
  have swap_output_neg:
      "(\<integral>\<^sup>+ output. \<integral>\<^sup>+ neg_point.
          ?integrand output pos_point neg_point \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ neg_point. \<integral>\<^sup>+ output.
          ?integrand output pos_point neg_point \<partial>lborel \<partial>lborel)"
      for pos_point
  proof -
    have measurable_pair:
        "case_prod (\<lambda>output neg_point.
          ?integrand output pos_point neg_point) \<in>
          borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      by measurable
    show ?thesis
      using lborel_pair.Fubini'[OF measurable_pair] by simp
  qed
  have reorder:
      "(\<integral>\<^sup>+ output. \<integral>\<^sup>+ pos_point.
          \<integral>\<^sup>+ neg_point. ?integrand output pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          \<integral>\<^sup>+ output. ?integrand output pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel)"
  proof -
    have swap_inner:
        "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ output.
            \<integral>\<^sup>+ neg_point. ?integrand output pos_point neg_point
            \<partial>lborel \<partial>lborel \<partial>lborel) =
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            \<integral>\<^sup>+ output. ?integrand output pos_point neg_point
            \<partial>lborel \<partial>lborel \<partial>lborel)"
    proof (rule nn_integral_cong)
      fix pos_point
      show "(\<integral>\<^sup>+ output. \<integral>\<^sup>+ neg_point.
            ?integrand output pos_point neg_point \<partial>lborel \<partial>lborel) =
          (\<integral>\<^sup>+ neg_point. \<integral>\<^sup>+ output.
            ?integrand output pos_point neg_point \<partial>lborel \<partial>lborel)"
        by (rule swap_output_neg)
    qed
    show ?thesis
      using swap_output_pos swap_inner by simp
  qed
  have translate_output:
      "(\<integral>\<^sup>+ output. ?integrand output pos_point neg_point
          \<partial>lborel) =
        (\<integral>\<^sup>+ inner_output.
          test (inner_output + pos_point - neg_point) *
          block_weight pos_point neg_point *
          inner_density neg_point inner_output \<partial>lborel)"
      for pos_point neg_point
  proof -
    let ?translated = "\<lambda>inner_output.
      test (inner_output + pos_point - neg_point) *
      block_weight pos_point neg_point *
      inner_density neg_point inner_output"
    have translated_measurable: "?translated \<in> borel_measurable lborel"
      by measurable
    have invariant:
        "(\<integral>\<^sup>+ output. ?translated (- pos_point + neg_point + output)
            \<partial>lborel) =
          (\<integral>\<^sup>+ inner_output. ?translated inner_output \<partial>lborel)"
      by (rule slp_nn_integral_translate[OF translated_measurable])
    show ?thesis
      using invariant
      by (simp add: algebra_simps)
  qed
  have translate_all:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          \<integral>\<^sup>+ output. ?integrand output pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          \<integral>\<^sup>+ inner_output.
            test (inner_output + pos_point - neg_point) *
            block_weight pos_point neg_point *
            inner_density neg_point inner_output
          \<partial>lborel \<partial>lborel \<partial>lborel)"
  proof (rule nn_integral_cong)
    fix pos_point
    show "(\<integral>\<^sup>+ neg_point. \<integral>\<^sup>+ output.
          ?integrand output pos_point neg_point
          \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ neg_point. \<integral>\<^sup>+ inner_output.
          test (inner_output + pos_point - neg_point) *
          block_weight pos_point neg_point *
          inner_density neg_point inner_output
          \<partial>lborel \<partial>lborel)"
    proof (rule nn_integral_cong)
      fix neg_point
      show "(\<integral>\<^sup>+ output. ?integrand output pos_point neg_point
            \<partial>lborel) =
          (\<integral>\<^sup>+ inner_output.
            test (inner_output + pos_point - neg_point) *
            block_weight pos_point neg_point *
            inner_density neg_point inner_output \<partial>lborel)"
        by (rule translate_output)
    qed
  qed
  have factor_all:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          \<integral>\<^sup>+ inner_output.
            test (inner_output + pos_point - neg_point) *
            block_weight pos_point neg_point *
            inner_density neg_point inner_output
          \<partial>lborel \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          block_weight pos_point neg_point *
          (\<integral>\<^sup>+ inner_output.
            test (inner_output + pos_point - neg_point) *
            inner_density neg_point inner_output \<partial>lborel)
          \<partial>lborel \<partial>lborel)"
  proof (rule nn_integral_cong)
    fix pos_point
    show "(\<integral>\<^sup>+ neg_point. \<integral>\<^sup>+ inner_output.
          test (inner_output + pos_point - neg_point) *
          block_weight pos_point neg_point *
          inner_density neg_point inner_output
          \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ neg_point.
          block_weight pos_point neg_point *
          (\<integral>\<^sup>+ inner_output.
            test (inner_output + pos_point - neg_point) *
            inner_density neg_point inner_output \<partial>lborel)
          \<partial>lborel)"
    proof (rule nn_integral_cong)
      fix neg_point
      show "(\<integral>\<^sup>+ inner_output.
            test (inner_output + pos_point - neg_point) *
            block_weight pos_point neg_point *
            inner_density neg_point inner_output \<partial>lborel) =
          block_weight pos_point neg_point *
          (\<integral>\<^sup>+ inner_output.
            test (inner_output + pos_point - neg_point) *
            inner_density neg_point inner_output \<partial>lborel)"
      proof -
        have inner_measurable:
            "(\<lambda>inner_output.
              test (inner_output + pos_point - neg_point) *
              inner_density neg_point inner_output)
            \<in> borel_measurable lborel"
          by measurable
        have pull_constant:
            "(\<integral>\<^sup>+ inner_output.
              block_weight pos_point neg_point *
              (test (inner_output + pos_point - neg_point) *
               inner_density neg_point inner_output) \<partial>lborel) =
            block_weight pos_point neg_point *
            (\<integral>\<^sup>+ inner_output.
              test (inner_output + pos_point - neg_point) *
              inner_density neg_point inner_output \<partial>lborel)"
          by (rule nn_integral_cmult[OF inner_measurable])
        show ?thesis
          using pull_constant
          by (simp add: mult.assoc mult.commute mult.left_commute)
      qed
    qed
  qed
  show ?thesis
    using expand_left reorder translate_all factor_all by simp
qed

end
