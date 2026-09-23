theory Inverse_Schrodinger_Lp_Right_Graph_Finite_Primitive_Difference_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Finite_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Primitive_Difference"
begin

section \<open>Finite right-graph transport for the Cauchy primitive difference\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem
    slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_primitive_diff_integrable:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real
    and center origin :: slp_point
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "Real_Vector_Spaces.norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integrable
      (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
        slp_point) measure)
      (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential
          (\<lambda>x. slp_cauchy_transform orientation potential x -
            slp_cauchy_transform orientation potential center)
        origin)"
proof -
  let ?terminal = "slp_cauchy_transform orientation potential"
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_measurable:
      "?terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper potential_lp])
  have terminal_diff_measurable:
      "(\<lambda>x. ?terminal x - ?terminal center) \<in>
        borel_measurable lborel"
    using terminal_measurable by measurable
  have natural_integrable:
      "integrable
        (((PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))
        (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau
          center cutoff potential
            (\<lambda>x. ?terminal x - ?terminal center) origin)"
    by (rule
      slp_right_branch_oscillatory_graph_kernel_natural_primitive_diff_integrable[
        OF B_nonnegative origin_bound cutoff_support potential_support
          p_lower p_upper cutoff_measurable potential_lp cutoff_bound
          C_nonnegative])
  have transported:
      "integrable
          (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
            slp_point) measure)
          (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. ?terminal x - ?terminal center) origin) \<longleftrightarrow>
        integrable
          (((PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
            (PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
          (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau
            center cutoff potential
              (\<lambda>x. ?terminal x - ?terminal center) origin)"
    by (rule slp_right_branch_graph_natural_finite_integrable_iff[OF
          cutoff_measurable potential_measurable terminal_diff_measurable])
  show ?thesis
    using transported natural_integrable by blast
qed

theorem
    slp_right_branch_oscillatory_graph_kernel_natural_finite_primitive_diff_integral:
  fixes branch_dummy :: "'i::finite itself"
    and p tau :: real
    and center origin :: slp_point
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
  shows
    "integral\<^sup>L
        (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
          slp_point) measure)
        (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
          cutoff potential
            (\<lambda>x. slp_cauchy_transform orientation potential x -
              slp_cauchy_transform orientation potential center)
          origin) =
      integral\<^sup>L
        (((PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))
        (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau
          center cutoff potential
            (\<lambda>x. slp_cauchy_transform orientation potential x -
              slp_cauchy_transform orientation potential center)
          origin)"
proof -
  let ?terminal = "slp_cauchy_transform orientation potential"
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_measurable:
      "?terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper potential_lp])
  have terminal_diff_measurable:
      "(\<lambda>x. ?terminal x - ?terminal center) \<in>
        borel_measurable lborel"
    using terminal_measurable by measurable
  show ?thesis
    by (rule slp_right_branch_graph_natural_finite_integral[OF
          cutoff_measurable potential_measurable terminal_diff_measurable])
qed

theorem
    slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_integral_eq_neumann_iterate:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real
    and center origin :: slp_point
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "Real_Vector_Spaces.norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integral\<^sup>L
        (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
          slp_point) measure)
        (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
          cutoff potential
            (\<lambda>x. slp_cauchy_transform orientation potential x -
              slp_cauchy_transform orientation potential center)
          origin) =
      slp_right_neumann_iterate CARD('i) tau center cutoff potential
        orientation origin"
proof -
  note finite_natural =
    slp_right_branch_oscillatory_graph_kernel_natural_finite_primitive_diff_integral[
      where 'i = 'i, OF p_lower p_upper cutoff_measurable potential_lp]
  note natural_representation =
    slp_right_branch_oscillatory_graph_kernel_natural_integral_eq_neumann_iterate[
      OF B_nonnegative origin_bound cutoff_support potential_support p_lower
        p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative]
  show ?thesis
    using finite_natural natural_representation by simp
qed

end

end
