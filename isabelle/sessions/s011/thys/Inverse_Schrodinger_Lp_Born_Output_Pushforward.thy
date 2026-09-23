theory Inverse_Schrodinger_Lp_Born_Output_Pushforward
  imports Inverse_Schrodinger_Lp_Born_Branch_Functional
begin

section \<open>Exact positive Born output push-forward\<close>

theorem slp_positive_output_density_pushforward:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
    and test_measurable:
      "test \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ output.
        test output *
        slp_positive_output_density R cutoff potential terminal_weight n
          origin output
        \<partial>lborel) =
      slp_positive_branch_functional R cutoff potential terminal_weight n
        origin test"
  using test_measurable
proof (induction n arbitrary: origin test)
  case 0
  show ?case
    by (simp add: mult.assoc)
next
  case (Suc n)
  note test_measurable[measurable] = Suc.prems
  let ?constant = "ennreal (inverse (pi ^ 2))"
  let ?block = "slp_positive_branch_block_weight R cutoff potential origin"
  let ?density =
    "slp_positive_output_density R cutoff potential terminal_weight n"

  have block_measurable:
      "case_prod ?block \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_branch_block_weight_measurable;
        measurable)
  have density_measurable:
      "case_prod ?density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable;
        measurable)
  have output_integrand_measurable:
      "(\<lambda>output. test output *
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ?block pos_point neg_point *
          ?density neg_point (output - pos_point + neg_point)
          \<partial>lborel \<partial>lborel))
      \<in> borel_measurable lborel"
    using block_measurable density_measurable by measurable
  have pull_constant:
      "(\<integral>\<^sup>+ output. test output *
          (?constant *
            (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
              ?block pos_point neg_point *
              ?density neg_point (output - pos_point + neg_point)
              \<partial>lborel \<partial>lborel))
          \<partial>lborel) =
        ?constant *
          (\<integral>\<^sup>+ output. test output *
            (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
              ?block pos_point neg_point *
              ?density neg_point (output - pos_point + neg_point)
              \<partial>lborel \<partial>lborel)
            \<partial>lborel)"
  proof -
    have extracted:
        "(\<integral>\<^sup>+ output. ?constant *
          (test output *
            (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
              ?block pos_point neg_point *
              ?density neg_point (output - pos_point + neg_point)
              \<partial>lborel \<partial>lborel))
          \<partial>lborel) =
        ?constant *
          (\<integral>\<^sup>+ output. test output *
            (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
              ?block pos_point neg_point *
              ?density neg_point (output - pos_point + neg_point)
              \<partial>lborel \<partial>lborel)
            \<partial>lborel)"
      by (rule nn_integral_cmult[OF output_integrand_measurable])
    show ?thesis
      using extracted by (simp add: mult.assoc mult.commute mult.left_commute)
  qed
  have transported:
      "(\<integral>\<^sup>+ output. test output *
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            ?block pos_point neg_point *
            ?density neg_point (output - pos_point + neg_point)
            \<partial>lborel \<partial>lborel) \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ?block pos_point neg_point *
          (\<integral>\<^sup>+ inner_output.
            test (inner_output + pos_point - neg_point) *
            ?density neg_point inner_output \<partial>lborel)
          \<partial>lborel \<partial>lborel)"
    by (rule slp_nn_integral_affine_output_transport[OF
          Suc.prems block_measurable density_measurable])
  have apply_induction:
      "(\<integral>\<^sup>+ inner_output.
          test (inner_output + pos_point - neg_point) *
          ?density neg_point inner_output \<partial>lborel) =
        slp_positive_branch_functional R cutoff potential terminal_weight n
          neg_point (\<lambda>inner_output.
            test (inner_output + pos_point - neg_point))"
      for pos_point neg_point
  proof (rule Suc.IH)
    show "(\<lambda>inner_output.
        test (inner_output + pos_point - neg_point))
      \<in> borel_measurable lborel"
      by (rule slp_positive_branch_translated_test_measurable[OF Suc.prems])
  qed
  have apply_induction_all:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ?block pos_point neg_point *
          (\<integral>\<^sup>+ inner_output.
            test (inner_output + pos_point - neg_point) *
            ?density neg_point inner_output \<partial>lborel)
          \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ?block pos_point neg_point *
          slp_positive_branch_functional R cutoff potential terminal_weight n
            neg_point (\<lambda>inner_output.
              test (inner_output + pos_point - neg_point))
          \<partial>lborel \<partial>lborel)"
  proof (rule nn_integral_cong)
    fix pos_point
    show "(\<integral>\<^sup>+ neg_point.
          ?block pos_point neg_point *
          (\<integral>\<^sup>+ inner_output.
            test (inner_output + pos_point - neg_point) *
            ?density neg_point inner_output \<partial>lborel)
          \<partial>lborel) =
        (\<integral>\<^sup>+ neg_point.
          ?block pos_point neg_point *
          slp_positive_branch_functional R cutoff potential terminal_weight n
            neg_point (\<lambda>inner_output.
              test (inner_output + pos_point - neg_point))
          \<partial>lborel)"
    by (intro nn_integral_cong)
      (simp only: apply_induction)
  qed
  have transported_inducted:
      "(\<integral>\<^sup>+ output. test output *
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            ?block pos_point neg_point *
            ?density neg_point (output - pos_point + neg_point)
            \<partial>lborel \<partial>lborel) \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ?block pos_point neg_point *
          slp_positive_branch_functional R cutoff potential terminal_weight n
            neg_point (\<lambda>inner_output.
              test (inner_output + pos_point - neg_point))
          \<partial>lborel \<partial>lborel)"
    by (rule trans[OF transported apply_induction_all])
  have scaled_transported_inducted:
      "?constant *
          (\<integral>\<^sup>+ output. test output *
            (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
              ?block pos_point neg_point *
              ?density neg_point (output - pos_point + neg_point)
              \<partial>lborel \<partial>lborel)
            \<partial>lborel) =
        ?constant *
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            ?block pos_point neg_point *
            slp_positive_branch_functional R cutoff potential terminal_weight n
              neg_point (\<lambda>inner_output.
                test (inner_output + pos_point - neg_point))
            \<partial>lborel \<partial>lborel)"
    by (rule arg_cong[OF transported_inducted])
  have recursive_identity:
      "(\<integral>\<^sup>+ output. test output *
          (?constant *
            (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
              ?block pos_point neg_point *
              ?density neg_point (output - pos_point + neg_point)
              \<partial>lborel \<partial>lborel))
          \<partial>lborel) =
        ?constant *
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            ?block pos_point neg_point *
            slp_positive_branch_functional R cutoff potential terminal_weight n
              neg_point (\<lambda>inner_output.
                test (inner_output + pos_point - neg_point))
            \<partial>lborel \<partial>lborel)"
    by (rule trans[OF pull_constant scaled_transported_inducted])
  show ?case
    using recursive_identity
    by (simp only: slp_positive_output_density.simps
        slp_positive_branch_functional.simps
        slp_positive_branch_block_weight_def)
qed

end
