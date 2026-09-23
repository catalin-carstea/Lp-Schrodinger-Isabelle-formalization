theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Primitive_Difference_Recursive_Identity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Natural_Primitive_Difference_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Nested_Identity_Integrable"
begin

section \<open>Primitive-difference natural graph as the recursive left branch\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_nested_primitive_diff:
  fixes B C p tau :: real
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
        (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
          (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
            \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential
            (\<lambda>x. slp_cauchy_transform orientation potential x -
              slp_cauchy_transform orientation potential center)
          origin) =
      slp_left_branch_nested_graph_functional n tau center cutoff potential
        (\<lambda>x. slp_cauchy_transform orientation potential x -
          slp_cauchy_transform orientation potential center)
        origin"
proof (rule
    slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_nested_integrable[
      OF origin_bound potential_support])
  fix m :: nat and root :: slp_point
  assume root_bound: "Real_Vector_Spaces.norm root \<le> B"
  show
    "integrable
      (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))
          \<Otimes>\<^sub>M
        (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_left_branch_oscillatory_graph_kernel_natural m tau center cutoff
        potential
          (\<lambda>x. slp_cauchy_transform orientation potential x -
            slp_cauchy_transform orientation potential center)
        root)"
    by (rule
        slp_left_branch_oscillatory_graph_kernel_natural_primitive_diff_integrable[
          OF B_nonnegative root_bound cutoff_support potential_support
            p_lower p_upper cutoff_measurable potential_lp cutoff_bound
            C_nonnegative])
qed

theorem slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_recursive_primitive_diff:
  fixes B C p tau :: real
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
        (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
          (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
            \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential
            (\<lambda>x. slp_cauchy_transform orientation potential x -
              slp_cauchy_transform orientation potential center)
          origin) =
      slp_left_recursive_branch n tau center cutoff potential
        (\<lambda>x. slp_cauchy_transform orientation potential x -
          slp_cauchy_transform orientation potential center)
        origin"
  apply (subst slp_left_recursive_branch_eq_nested_graph_functional)
  by (rule
      slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_nested_primitive_diff[
        OF B_nonnegative origin_bound cutoff_support potential_support p_lower
          p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative])

end

end
