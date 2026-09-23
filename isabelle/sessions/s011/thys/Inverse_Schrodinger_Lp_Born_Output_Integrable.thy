theory Inverse_Schrodinger_Lp_Born_Output_Integrable
  imports Inverse_Schrodinger_Lp_Born_Output_Pushforward_Aliases
begin

section \<open>Finite positive output mass and complex integrability\<close>

theorem slp_positive_output_density_dominates_integrable:
  fixes amplitude :: "slp_point \<Rightarrow> complex"
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and amplitude_measurable:
      "amplitude \<in> borel_measurable lborel"
    and dominated:
      "AE output in lborel.
        ennreal (norm (amplitude output)) \<le>
          slp_positive_output_density R cutoff potential terminal_weight n
            origin output"
    and finite_mass:
      "slp_positive_branch_functional R cutoff potential terminal_weight n
          origin (\<lambda>_. 1) < top"
  shows "integrable lborel amplitude"
proof -
  have density_mass:
      "(\<integral>\<^sup>+ output.
          slp_positive_output_density R cutoff potential terminal_weight n
            origin output
          \<partial>lborel) =
        slp_positive_branch_functional R cutoff potential terminal_weight n
          origin (\<lambda>_. 1)"
    by (rule slp_positive_output_density_mass[OF cutoff_measurable
          potential_measurable terminal_weight_measurable])
  have norm_bound:
      "(\<integral>\<^sup>+ output. ennreal (norm (amplitude output)) \<partial>lborel) \<le>
        (\<integral>\<^sup>+ output.
          slp_positive_output_density R cutoff potential terminal_weight n
            origin output
          \<partial>lborel)"
    by (rule nn_integral_mono_AE[OF dominated])
  have density_finite:
      "(\<integral>\<^sup>+ output.
          slp_positive_output_density R cutoff potential terminal_weight n
            origin output
          \<partial>lborel) < top"
    using density_mass finite_mass by simp
  have norm_finite:
      "(\<integral>\<^sup>+ output. ennreal (norm (amplitude output)) \<partial>lborel) < top"
    using order.strict_trans1[OF norm_bound density_finite] .
  show ?thesis
  proof (rule integrableI_bounded[where f = amplitude and M = lborel])
    show "amplitude \<in> borel_measurable lborel"
      by (rule amplitude_measurable)
    show "(\<integral>\<^sup>+ output. norm (amplitude output) \<partial>lborel) < \<infinity>"
      using norm_finite by (simp add: norm_complex_def)
  qed
qed

corollary slp_left_positive_output_density_dominates_integrable:
  fixes amplitude :: "slp_point \<Rightarrow> complex"
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and amplitude_measurable:
      "amplitude \<in> borel_measurable lborel"
    and dominated:
      "AE output in lborel.
        ennreal (norm (amplitude output)) \<le>
          slp_left_positive_output_density R cutoff potential terminal_weight n
            origin output"
    and finite_mass:
      "slp_positive_branch_functional R cutoff potential terminal_weight n
          origin (\<lambda>_. 1) < top"
  shows "integrable lborel amplitude"
  apply (rule slp_positive_output_density_dominates_integrable[OF
        cutoff_measurable potential_measurable terminal_weight_measurable
        amplitude_measurable _ finite_mass])
  using dominated
  by (simp add: slp_left_positive_output_density_def)

corollary slp_right_positive_output_density_dominates_integrable:
  fixes amplitude :: "slp_point \<Rightarrow> complex"
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and amplitude_measurable:
      "amplitude \<in> borel_measurable lborel"
    and dominated:
      "AE output in lborel.
        ennreal (norm (amplitude output)) \<le>
          slp_right_positive_output_density R cutoff potential terminal_weight n
            origin output"
    and finite_mass:
      "slp_positive_branch_functional R cutoff potential terminal_weight n
          origin (\<lambda>_. 1) < top"
  shows "integrable lborel amplitude"
  apply (rule slp_positive_output_density_dominates_integrable[OF
        cutoff_measurable potential_measurable terminal_weight_measurable
        amplitude_measurable _ finite_mass])
  using dominated
  by (simp add: slp_right_positive_output_density_def)

end
