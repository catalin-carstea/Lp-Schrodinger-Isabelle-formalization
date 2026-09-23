theory Inverse_Schrodinger_Lp_Right_Graph_Natural_Primitive_Difference
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Conjugate"
begin

section \<open>The right primitive-difference graph as the Neumann iterate\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_branch_oscillatory_graph_kernel_natural_primitive_diff_integrable:
  fixes B C p tau :: real
    and center origin :: slp_point
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "Real_Vector_Spaces.norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integrable
      (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
          \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_right_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential
          (\<lambda>x. slp_cauchy_transform orientation potential x -
            slp_cauchy_transform orientation potential center)
        origin)"
proof -
  let ?M =
    "((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
        \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
        \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  have cutoff_support_cnj:
      "\<And>x. cnj (cutoff x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    by (rule cutoff_support) simp
  have potential_support_cnj:
      "\<And>x. cnj (potential x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
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
      "\<And>x. cmod (cnj (cutoff x)) \<le> C"
    using cutoff_bound by simp
  have left_integrable:
      "integrable ?M
        (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
          (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
          (\<lambda>x.
            slp_cauchy_transform
                (slp_opposite_cauchy_orientation orientation)
                (\<lambda>y. cnj (potential y)) x -
              slp_cauchy_transform
                (slp_opposite_cauchy_orientation orientation)
                (\<lambda>y. cnj (potential y)) center)
          origin)"
    by (rule
        slp_left_branch_oscillatory_graph_kernel_natural_primitive_diff_integrable[
          OF B_nonnegative origin_bound cutoff_support_cnj
            potential_support_cnj p_lower p_upper cutoff_measurable_cnj
            potential_lp_cnj cutoff_bound_cnj C_nonnegative])
  have terminal_conjugate:
      "(\<lambda>x. cnj
          (slp_cauchy_transform orientation potential x -
            slp_cauchy_transform orientation potential center)) =
        (\<lambda>x.
          slp_cauchy_transform
              (slp_opposite_cauchy_orientation orientation)
              (\<lambda>y. cnj (potential y)) x -
            slp_cauchy_transform
              (slp_opposite_cauchy_orientation orientation)
              (\<lambda>y. cnj (potential y)) center)"
    by (rule ext) simp
  note conjugate_iff =
    slp_right_branch_oscillatory_graph_kernel_natural_integrable_iff[
      where M = ?M and n = n and tau = tau and center = center
        and cutoff = cutoff and potential = potential
        and terminal_value =
          "\<lambda>x. slp_cauchy_transform orientation potential x -
            slp_cauchy_transform orientation potential center"
        and origin = origin]
  show ?thesis
    using conjugate_iff left_integrable terminal_conjugate by simp
qed

theorem slp_right_branch_oscillatory_graph_kernel_natural_integral_eq_neumann_iterate:
  fixes B C p tau :: real
    and center origin :: slp_point
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "Real_Vector_Spaces.norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> Real_Vector_Spaces.norm x \<le> B"
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
      (slp_right_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential
          (\<lambda>x. slp_cauchy_transform orientation potential x -
            slp_cauchy_transform orientation potential center)
        origin) =
      slp_right_neumann_iterate n tau center cutoff potential orientation
        origin"
proof -
  let ?M =
    "((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
        \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
        \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  have cutoff_support_cnj:
      "\<And>x. cnj (cutoff x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    by (rule cutoff_support) simp
  have potential_support_cnj:
      "\<And>x. cnj (potential x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
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
      "\<And>x. cmod (cnj (cutoff x)) \<le> C"
    using cutoff_bound by simp
  have terminal_conjugate:
      "(\<lambda>x. cnj
          (slp_cauchy_transform orientation potential x -
            slp_cauchy_transform orientation potential center)) =
        (\<lambda>x.
          slp_cauchy_transform
              (slp_opposite_cauchy_orientation orientation)
              (\<lambda>y. cnj (potential y)) x -
            slp_cauchy_transform
              (slp_opposite_cauchy_orientation orientation)
              (\<lambda>y. cnj (potential y)) center)"
    by (rule ext) simp
  have left_representation:
      "integral\<^sup>L ?M
        (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
          (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
          (\<lambda>x.
            slp_cauchy_transform
                (slp_opposite_cauchy_orientation orientation)
                (\<lambda>y. cnj (potential y)) x -
              slp_cauchy_transform
                (slp_opposite_cauchy_orientation orientation)
                (\<lambda>y. cnj (potential y)) center)
          origin) =
        slp_left_neumann_iterate n (- tau) center
          (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
          (slp_opposite_cauchy_orientation orientation) origin"
    by (rule
        slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_neumann_iterate[
          OF B_nonnegative origin_bound cutoff_support_cnj
            potential_support_cnj p_lower p_upper cutoff_measurable_cnj
            potential_lp_cnj cutoff_bound_cnj C_nonnegative])
  note right_integral =
    slp_right_branch_oscillatory_graph_kernel_natural_integral[
      where M = ?M and n = n and tau = tau and center = center
        and cutoff = cutoff and potential = potential
        and terminal_value =
          "\<lambda>x. slp_cauchy_transform orientation potential x -
            slp_cauchy_transform orientation potential center"
        and origin = origin]
  show ?thesis
    using right_integral terminal_conjugate left_representation
      slp_left_neumann_iterate_conjugate_eq_right[of n tau center cutoff
        potential orientation origin]
    by simp
qed

end

end
