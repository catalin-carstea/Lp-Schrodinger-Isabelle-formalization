theory Inverse_Schrodinger_Lp_Born_Output_Density
  imports Inverse_Schrodinger_Lp_Born_Phase_Modulation
begin

section \<open>Positive finite Born output densities\<close>

primrec slp_positive_output_density ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow>
      nat \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal" where
  "slp_positive_output_density R cutoff potential terminal_weight 0 origin output =
    ennreal (inverse pi) *
      ennreal (slp_localized_cauchy_kernel R (origin - output)) *
      ennreal (norm (cutoff output)) * terminal_weight output"
| "slp_positive_output_density R cutoff potential terminal_weight (Suc n)
      origin output =
    ennreal (inverse (pi ^ 2)) *
      (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
        ennreal (norm (cutoff pos_point)) *
        ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
        ennreal (norm (potential neg_point)) *
        slp_positive_output_density R cutoff potential terminal_weight n
          neg_point (output - pos_point + neg_point)
        \<partial>lborel \<partial>lborel)"

definition slp_left_positive_output_density ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow>
      nat \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal" where
  "slp_left_positive_output_density R cutoff potential terminal_weight =
    slp_positive_output_density R cutoff potential terminal_weight"

definition slp_right_positive_output_density ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow>
      nat \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal" where
  "slp_right_positive_output_density R cutoff potential terminal_weight =
    slp_positive_output_density R cutoff potential terminal_weight"

lemma slp_left_positive_output_density_zero:
  "slp_left_positive_output_density R cutoff potential terminal_weight 0
      origin output =
    ennreal (inverse pi) *
      ennreal (slp_localized_cauchy_kernel R (origin - output)) *
      ennreal (norm (cutoff output)) * terminal_weight output"
  by (simp add: slp_left_positive_output_density_def)

lemma slp_right_positive_output_density_zero:
  "slp_right_positive_output_density R cutoff potential terminal_weight 0
      origin output =
    ennreal (inverse pi) *
      ennreal (slp_localized_cauchy_kernel R (origin - output)) *
      ennreal (norm (cutoff output)) * terminal_weight output"
  by (simp add: slp_right_positive_output_density_def)

lemma slp_left_positive_output_density_Suc:
  "slp_left_positive_output_density R cutoff potential terminal_weight
      (Suc n) origin output =
    ennreal (inverse (pi ^ 2)) *
      (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
        ennreal (norm (cutoff pos_point)) *
        ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
        ennreal (norm (potential neg_point)) *
        slp_left_positive_output_density R cutoff potential terminal_weight
          n neg_point (output - pos_point + neg_point)
        \<partial>lborel \<partial>lborel)"
  by (simp add: slp_left_positive_output_density_def)

lemma slp_right_positive_output_density_Suc:
  "slp_right_positive_output_density R cutoff potential terminal_weight
      (Suc n) origin output =
    ennreal (inverse (pi ^ 2)) *
      (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
        ennreal (norm (cutoff pos_point)) *
        ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
        ennreal (norm (potential neg_point)) *
        slp_right_positive_output_density R cutoff potential terminal_weight
          n neg_point (output - pos_point + neg_point)
        \<partial>lborel \<partial>lborel)"
  by (simp add: slp_right_positive_output_density_def)

lemma slp_branch_output_translation:
  "slp_left_branch_output (pair # pairs) terminal = output \<longleftrightarrow>
    slp_left_branch_output pairs terminal =
      output - fst pair + snd pair"
  by (simp add: slp_branch_increment_def algebra_simps)

end
