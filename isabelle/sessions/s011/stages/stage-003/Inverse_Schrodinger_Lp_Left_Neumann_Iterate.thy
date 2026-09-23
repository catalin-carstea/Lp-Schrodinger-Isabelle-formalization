theory Inverse_Schrodinger_Lp_Left_Neumann_Iterate
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Natural_Primitive_Difference_Recursive_Identity"
begin

section \<open>The exact manuscript left Neumann iterate\<close>

definition slp_left_neumann_iterate ::
    "nat \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_cauchy_orientation \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_left_neumann_iterate n tau center cutoff potential orientation =
    slp_left_recursive_branch n tau center cutoff potential
      (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center)"

lemma slp_left_neumann_iterate_zero:
  "slp_left_neumann_iterate 0 tau center cutoff potential orientation =
    slp_partial_psi_inverse tau center
      (\<lambda>terminal. cutoff terminal *
        (slp_cauchy_transform orientation potential terminal -
          slp_cauchy_transform orientation potential center))"
  unfolding slp_left_neumann_iterate_def
  by (rule slp_left_recursive_branch.simps)

lemma slp_left_neumann_iterate_Suc:
  "slp_left_neumann_iterate (Suc n) tau center cutoff potential orientation =
    slp_partial_psi_inverse tau center
      (\<lambda>pos. cutoff pos *
        slp_dbar_psi_inverse tau center
          (\<lambda>neg. potential neg *
            slp_left_neumann_iterate n tau center cutoff potential orientation
              neg)
          pos)"
  unfolding slp_left_neumann_iterate_def
  by (rule slp_left_recursive_branch.simps)

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_neumann_iterate:
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
      slp_left_neumann_iterate n tau center cutoff potential orientation origin"
  unfolding slp_left_neumann_iterate_def
  by (rule
      slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_recursive_primitive_diff[
        OF B_nonnegative origin_bound cutoff_support potential_support p_lower
          p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative])

end

end
