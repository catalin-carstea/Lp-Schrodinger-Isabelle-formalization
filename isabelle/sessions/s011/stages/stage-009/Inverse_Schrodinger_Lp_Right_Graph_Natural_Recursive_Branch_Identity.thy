theory Inverse_Schrodinger_Lp_Right_Graph_Natural_Recursive_Branch_Identity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Center_Average_Error_Transpose"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Conjugate"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Recursive_Branch_Identity"
begin

section \<open>The natural graph integral as the recursive right branch\<close>

context aim_planar_riesz_hls
begin

theorem slp_right_branch_oscillatory_graph_kernel_natural_integral_eq_recursive_hls:
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
    and cutoff_measurable:
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
        (slp_right_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential (\<lambda>_. 1) origin) =
      slp_right_recursive_branch n tau center cutoff potential (\<lambda>_. 1)
        origin"
proof -
  let ?M =
    "((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
        \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
        \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  have cutoff_support_cnj:
      "\<And>x. cnj (cutoff x) \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    by (rule cutoff_support) simp
  have potential_support_cnj:
      "\<And>x. cnj (potential x) \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    by (rule potential_support) simp
  have cutoff_measurable_cnj:
      "(\<lambda>x. cnj (cutoff x)) \<in> borel_measurable lborel"
  proof -
    have cnj_borel_measurable: "cnj \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF
            continuous_on_cnj[OF continuous_on_id]])
    show ?thesis
      using measurable_comp[OF cutoff_measurable cnj_borel_measurable]
      by (simp add: comp_def)
  qed
  have potential_lp_cnj:
      "aim_complex_lp_on_plane p (\<lambda>x. cnj (potential x))"
    using potential_lp by simp
  have cutoff_bound_cnj:
      "\<And>x. norm (cnj (cutoff x)) \<le> C"
    using cutoff_bound by simp
  have left_representation:
      "integral\<^sup>L ?M
        (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
          (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
          (\<lambda>_. 1) origin) =
        slp_left_recursive_branch n (- tau) center
          (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
          (\<lambda>_. 1) origin"
    by (rule
        slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_recursive_hls[
          OF B_nonnegative origin_bound cutoff_support_cnj
            potential_support_cnj p_lower p_upper cutoff_measurable_cnj
            potential_lp_cnj cutoff_bound_cnj C_nonnegative])
  note right_integral =
    slp_right_branch_oscillatory_graph_kernel_natural_integral[
      where M = ?M and n = n and tau = tau and center = center
        and cutoff = cutoff and potential = potential
        and terminal_value = "\<lambda>_. 1" and origin = origin]
  note branch_conjugate = slp_left_recursive_branch_conjugate_eq_right[
    of n tau center cutoff potential "\<lambda>_. 1" origin]
  show ?thesis
    using right_integral left_representation branch_conjugate by simp
qed

end

end
