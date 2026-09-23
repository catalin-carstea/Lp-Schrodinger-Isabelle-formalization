theory Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Uniform
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Mass_Factorization"
begin

section \<open>Uniform finite-coordinate unit inner-mass bound\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_branch_positive_inner_mass_finite_unit_uniform:
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
    "\<exists>(massbound782 :: ennreal). massbound782 < top_class.top \<and>
      (\<forall>origin.
        slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
          potential (\<lambda>_. 1) (\<lambda>_. 1) origin \<le> massbound782)"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable:
      "(\<lambda>_ :: slp_point. 1 :: complex) \<in> borel_measurable lborel"
    by measurable
  obtain massbound782 where massbound782_finite: "massbound782 < top_class.top"
    and massbound782_bound:
      "\<And>origin.
        slp_positive_branch_functional R cutoff potential (\<lambda>_. 1)
          CARD('i) origin (\<lambda>_. 1) \<le> massbound782"
    using slp_positive_branch_mass_unweighted_uniform[OF radius_nonnegative
      p_lower p_upper cutoff_measurable potential_lp cutoff_bound
      C_nonnegative]
    by blast
  have identify:
      "slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
          potential (\<lambda>_. 1) (\<lambda>_. 1) origin =
        slp_positive_branch_functional R cutoff potential (\<lambda>_. 1)
          CARD('i) origin (\<lambda>_. 1)"
    for origin
    using slp_left_branch_positive_inner_mass_finite_functional[
      where 'i = 'i and R = R and cutoff = cutoff and potential = potential
        and terminal_value = "\<lambda>_ :: slp_point. 1 :: complex"
        and output_factor = "\<lambda>_ :: slp_point. 1 :: complex"
        and origin = origin,
      OF cutoff_measurable potential_measurable unit_measurable
        unit_measurable]
    by (simp only: norm_one ennreal_1)
  show ?thesis
    by (intro exI[of _ massbound782] conjI massbound782_finite allI)
      (simp only: identify; rule massbound782_bound)
qed

end

end
