theory Inverse_Schrodinger_Lp_Born_Output_Pushforward_Aliases
  imports Inverse_Schrodinger_Lp_Born_Output_Pushforward
begin

section \<open>Named branch push-forward and mass identities\<close>

corollary slp_left_positive_output_density_pushforward:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and test_measurable: "test \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ output.
        test output *
        slp_left_positive_output_density R cutoff potential terminal_weight n
          origin output
        \<partial>lborel) =
      slp_positive_branch_functional R cutoff potential terminal_weight n
        origin test"
  unfolding slp_left_positive_output_density_def
  by (rule slp_positive_output_density_pushforward[OF cutoff_measurable
        potential_measurable terminal_weight_measurable test_measurable])

corollary slp_right_positive_output_density_pushforward:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and test_measurable: "test \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ output.
        test output *
        slp_right_positive_output_density R cutoff potential terminal_weight n
          origin output
        \<partial>lborel) =
      slp_positive_branch_functional R cutoff potential terminal_weight n
        origin test"
  unfolding slp_right_positive_output_density_def
  by (rule slp_positive_output_density_pushforward[OF cutoff_measurable
        potential_measurable terminal_weight_measurable test_measurable])

corollary slp_positive_output_density_mass:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ output.
        slp_positive_output_density R cutoff potential terminal_weight n
          origin output
        \<partial>lborel) =
      slp_positive_branch_functional R cutoff potential terminal_weight n
        origin (\<lambda>_. 1)"
proof -
  have one_measurable:
      "(\<lambda>_ :: slp_point. (1 :: ennreal)) \<in> borel_measurable lborel"
    by measurable
  note identity = slp_positive_output_density_pushforward[OF
      cutoff_measurable potential_measurable terminal_weight_measurable
      one_measurable, of R n origin]
  show ?thesis
    using identity by simp
qed

corollary slp_left_positive_output_density_mass:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ output.
        slp_left_positive_output_density R cutoff potential terminal_weight n
          origin output
        \<partial>lborel) =
      slp_positive_branch_functional R cutoff potential terminal_weight n
        origin (\<lambda>_. 1)"
  unfolding slp_left_positive_output_density_def
  by (rule slp_positive_output_density_mass[OF cutoff_measurable
        potential_measurable terminal_weight_measurable])

corollary slp_right_positive_output_density_mass:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ output.
        slp_right_positive_output_density R cutoff potential terminal_weight n
          origin output
        \<partial>lborel) =
      slp_positive_branch_functional R cutoff potential terminal_weight n
        origin (\<lambda>_. 1)"
  unfolding slp_right_positive_output_density_def
  by (rule slp_positive_output_density_mass[OF cutoff_measurable
        potential_measurable terminal_weight_measurable])

end
