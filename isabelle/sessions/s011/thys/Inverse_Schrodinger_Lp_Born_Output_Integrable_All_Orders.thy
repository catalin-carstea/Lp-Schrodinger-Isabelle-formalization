theory Inverse_Schrodinger_Lp_Born_Output_Integrable_All_Orders
  imports
    Inverse_Schrodinger_Lp_Born_Output_Integrable
    Inverse_Schrodinger_Lp_Born_Branch_Uniform_Mass
begin

section \<open>All-orders dominated positive-branch output integrability\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_branch_mass_unweighted_finite:
  fixes R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
        origin (\<lambda>_. 1) < top"
proof -
  obtain M where M_finite: "M < top"
    and mass_le:
      "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
          origin (\<lambda>_. 1) \<le> M"
    using slp_positive_branch_mass_unweighted_uniform[OF radius_nonnegative
      p_lower p_upper cutoff_measurable potential_lp cutoff_bound
      C_nonnegative]
    by blast
  show ?thesis
    by (rule le_less_trans[OF mass_le M_finite])
qed

theorem slp_left_positive_output_dominated_integrable_all_orders:
  fixes R C p :: real
    and cutoff potential amplitude :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and amplitude_measurable: "amplitude \<in> borel_measurable lborel"
    and dominated:
      "AE output in lborel.
        ennreal (norm (amplitude output)) \<le>
          slp_left_positive_output_density R cutoff potential (\<lambda>_. 1) n
            origin output"
  shows "integrable lborel amplitude"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_weight_measurable:
      "(\<lambda>_ :: slp_point. 1 :: ennreal) \<in> borel_measurable lborel"
    by measurable
  have finite_mass:
      "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
          origin (\<lambda>_. 1) < top"
    by (rule slp_positive_branch_mass_unweighted_finite[OF
          radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
          cutoff_bound C_nonnegative])
  show ?thesis
    by (rule slp_left_positive_output_density_dominates_integrable[OF
          cutoff_measurable potential_measurable terminal_weight_measurable
          amplitude_measurable dominated finite_mass])
qed

theorem slp_right_positive_output_dominated_integrable_all_orders:
  fixes R C p :: real
    and cutoff potential amplitude :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and amplitude_measurable: "amplitude \<in> borel_measurable lborel"
    and dominated:
      "AE output in lborel.
        ennreal (norm (amplitude output)) \<le>
          slp_right_positive_output_density R cutoff potential (\<lambda>_. 1) n
            origin output"
  shows "integrable lborel amplitude"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_weight_measurable:
      "(\<lambda>_ :: slp_point. 1 :: ennreal) \<in> borel_measurable lborel"
    by measurable
  have finite_mass:
      "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
          origin (\<lambda>_. 1) < top"
    by (rule slp_positive_branch_mass_unweighted_finite[OF
          radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
          cutoff_bound C_nonnegative])
  show ?thesis
    by (rule slp_right_positive_output_density_dominates_integrable[OF
          cutoff_measurable potential_measurable terminal_weight_measurable
          amplitude_measurable dominated finite_mass])
qed

end

end
