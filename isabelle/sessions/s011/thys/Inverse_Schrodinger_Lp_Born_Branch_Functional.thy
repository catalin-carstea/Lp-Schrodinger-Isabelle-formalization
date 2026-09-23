theory Inverse_Schrodinger_Lp_Born_Branch_Functional
  imports Inverse_Schrodinger_Lp_Affine_Output_Transport
begin

section \<open>Positive finite Born branch testing functional\<close>

definition slp_positive_branch_block_weight ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal" where
  "slp_positive_branch_block_weight R cutoff potential origin pos_point
      neg_point =
    ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
    ennreal (norm (cutoff pos_point)) *
    ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
    ennreal (norm (potential neg_point))"

primrec slp_positive_branch_functional ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow>
      nat \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow> ennreal" where
  "slp_positive_branch_functional R cutoff potential terminal_weight 0
      origin test =
    (\<integral>\<^sup>+ terminal.
      test terminal *
      (ennreal (inverse pi) *
       ennreal (slp_localized_cauchy_kernel R (origin - terminal)) *
       ennreal (norm (cutoff terminal)) * terminal_weight terminal)
      \<partial>lborel)"
| "slp_positive_branch_functional R cutoff potential terminal_weight (Suc n)
      origin test =
    ennreal (inverse (pi ^ 2)) *
      (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        slp_positive_branch_block_weight R cutoff potential origin pos_point
          neg_point *
        slp_positive_branch_functional R cutoff potential terminal_weight n
          neg_point (\<lambda>inner_output.
            test (inner_output + pos_point - neg_point))
        \<partial>lborel \<partial>lborel)"

lemma slp_positive_branch_block_weight_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
  shows "case_prod
      (slp_positive_branch_block_weight R cutoff potential origin)
    \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
  show ?thesis
    unfolding slp_positive_branch_block_weight_def
    by measurable
qed

lemma slp_positive_branch_translated_test_measurable:
  assumes test_measurable[measurable]:
      "test \<in> borel_measurable lborel"
  shows "(\<lambda>inner_output.
      test (inner_output + pos_point - neg_point))
    \<in> borel_measurable lborel"
  by measurable

lemma slp_positive_branch_functional_zero:
  "slp_positive_branch_functional R cutoff potential terminal_weight 0
      origin test =
    (\<integral>\<^sup>+ terminal.
      test terminal *
      (ennreal (inverse pi) *
       ennreal (slp_localized_cauchy_kernel R (origin - terminal)) *
       ennreal (norm (cutoff terminal)) * terminal_weight terminal)
      \<partial>lborel)"
  by simp

lemma slp_positive_branch_functional_Suc:
  "slp_positive_branch_functional R cutoff potential terminal_weight (Suc n)
      origin test =
    ennreal (inverse (pi ^ 2)) *
      (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        slp_positive_branch_block_weight R cutoff potential origin pos_point
          neg_point *
        slp_positive_branch_functional R cutoff potential terminal_weight n
          neg_point (\<lambda>inner_output.
            test (inner_output + pos_point - neg_point))
        \<partial>lborel \<partial>lborel)"
  by simp

end
