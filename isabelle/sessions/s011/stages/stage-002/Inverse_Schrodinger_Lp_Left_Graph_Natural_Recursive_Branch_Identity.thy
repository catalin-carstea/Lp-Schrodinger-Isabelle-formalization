theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Recursive_Branch_Identity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Nested_Identity"
begin

section \<open>Natural graph integral as the recursive left branch\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_recursive_hls:
  fixes B C p tau :: real
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
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integral\<^sup>L
        (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
          (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
            \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential (\<lambda>_. 1) origin) =
      slp_left_recursive_branch n tau center cutoff potential (\<lambda>_. 1)
        origin"
  apply (subst slp_left_recursive_branch_eq_nested_graph_functional)
  by (rule
      slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_nested_hls[
        OF B_nonnegative origin_bound cutoff_support potential_support p_lower
          p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative])

end

end
