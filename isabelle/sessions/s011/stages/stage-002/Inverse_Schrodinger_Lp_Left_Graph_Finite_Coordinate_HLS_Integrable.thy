theory Inverse_Schrodinger_Lp_Left_Graph_Finite_Coordinate_HLS_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Finite_Coordinate_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Inner_Mass_Functional"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Output_Integrable_All_Orders"
begin

section \<open>The frozen HLS mass bound supplies finite-coordinate integrability\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_branch_positive_inner_mass_unit_finite:
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
    "slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff potential
      (\<lambda>_. 1) (\<lambda>_. 1) origin < \<infinity>"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp
    unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable:
      "(\<lambda>_ :: slp_point. 1 :: complex) \<in> borel_measurable lborel"
    by measurable
  have functional:
      "slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff potential
          (\<lambda>_. 1) (\<lambda>_. 1) origin =
        slp_positive_branch_functional R cutoff potential (\<lambda>_. 1)
          CARD('i) origin (\<lambda>_. 1)"
    using slp_left_branch_positive_inner_mass_finite_functional[
      where 'i = 'i and R = R and cutoff = cutoff and potential = potential
        and terminal_value = "\<lambda>_ :: slp_point. 1 :: complex"
        and output_factor = "\<lambda>_ :: slp_point. 1 :: complex"
        and origin = origin,
      OF cutoff_measurable potential_measurable unit_measurable
        unit_measurable]
    by (simp only: norm_one ennreal_1)
  have finite_functional:
      "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1)
        CARD('i) origin (\<lambda>_. 1) < \<infinity>"
    using slp_positive_branch_mass_unweighted_finite[
      where R = R and C = C and p = p and cutoff = cutoff
        and potential = potential and n = "CARD('i)" and origin = origin,
      OF radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
        cutoff_bound C_nonnegative]
    unfolding infinity_ennreal_def .
  show ?thesis
    using functional finite_functional by simp
qed

theorem slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_integrable_hls:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real
    and center origin :: slp_point
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integrable lborel
      (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>_. 1) origin ::
          (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point)
            \<Rightarrow> complex)"
proof -
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp
    unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable:
      "(\<lambda>_ :: slp_point. 1 :: complex) \<in> borel_measurable lborel"
    by measurable
  have positive_inner_mass_finite:
      "slp_left_branch_positive_inner_mass_finite TYPE('i) (2 * B) cutoff
        potential (\<lambda>_. 1) (\<lambda>_. 1) origin < \<infinity>"
    by (rule slp_left_branch_positive_inner_mass_unit_finite[OF
          radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
          cutoff_bound C_nonnegative])
  show ?thesis
    by (rule
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_integrable[OF
        B_nonnegative origin_bound cutoff_support potential_support
        cutoff_measurable potential_measurable unit_measurable
        positive_inner_mass_finite])
qed

end

end
