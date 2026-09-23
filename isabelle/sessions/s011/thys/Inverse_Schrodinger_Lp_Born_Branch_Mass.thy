theory Inverse_Schrodinger_Lp_Born_Branch_Mass
  imports Inverse_Schrodinger_Lp_Born_Output_Integrable
begin

section \<open>Constant-test positive branch mass recursion\<close>

lemma slp_positive_branch_mass_zero:
  "slp_positive_branch_functional R cutoff potential terminal_weight 0
      origin (\<lambda>_. 1) =
    (\<integral>\<^sup>+ terminal.
      ennreal (inverse pi) *
      ennreal (slp_localized_cauchy_kernel R (origin - terminal)) *
      ennreal (norm (cutoff terminal)) * terminal_weight terminal
      \<partial>lborel)"
  by simp

lemma slp_positive_branch_mass_Suc:
  "slp_positive_branch_functional R cutoff potential terminal_weight (Suc n)
      origin (\<lambda>_. 1) =
    ennreal (inverse (pi ^ 2)) *
      (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        slp_positive_branch_block_weight R cutoff potential origin pos_point
          neg_point *
        slp_positive_branch_functional R cutoff potential terminal_weight n
          neg_point (\<lambda>_. 1)
        \<partial>lborel \<partial>lborel)"
  by simp

end
