theory Inverse_Schrodinger_Lp_Output_Density_Finite_Unit_Mass_Uniform
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Output_Density"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Uniform"
begin

section \<open>Uniform finite-order total output-density mass\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_output_density_finite_unit_mass_uniform:
  fixes branch_dummy :: "'i::finite itself"
    and R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "\<exists>(massbound815 :: ennreal). massbound815 < top_class.top \<and>
      (\<forall>origin.
        nn_integral lborel
          (slp_positive_output_density R cutoff potential (\<lambda>_. 1)
            CARD('i) origin) \<le> massbound815)"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  obtain massbound815 where massbound815_finite:
      "massbound815 < top_class.top"
    and massbound815_bound:
      "\<And>origin.
        slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
          potential (\<lambda>_. 1) (\<lambda>_. 1) origin \<le> massbound815"
    using slp_left_branch_positive_inner_mass_finite_unit_uniform[
      where 'i = 'i and R = R and C = C and p = p and cutoff = cutoff
        and potential = potential,
      OF radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
        cutoff_bound C_nonnegative]
    by blast
  have identify:
      "nn_integral lborel
          (slp_positive_output_density R cutoff potential (\<lambda>_. 1)
            CARD('i) origin) =
        slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
          potential (\<lambda>_. 1) (\<lambda>_. 1) origin"
    for origin
    using slp_left_branch_positive_inner_mass_finite_unit_output_density[
      where 'i = 'i and R = R and cutoff = cutoff and potential = potential
        and root = origin,
      OF cutoff_measurable potential_measurable]
    by simp
  show ?thesis
    by (intro exI[of _ massbound815] conjI massbound815_finite allI)
      (simp only: identify; rule massbound815_bound)
qed

end

end
