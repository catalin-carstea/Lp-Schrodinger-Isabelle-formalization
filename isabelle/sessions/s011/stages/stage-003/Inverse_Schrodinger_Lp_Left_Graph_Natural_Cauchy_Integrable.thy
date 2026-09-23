theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Cauchy_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Natural_Integrable_Finite"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Cauchy_Terminal_Branch_Functional_Finite"
begin

section \<open>Natural-coordinate integrability for the Cauchy terminal\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_oscillatory_graph_kernel_natural_cauchy_integrable:
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
    "integrable
      (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
          \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential (slp_cauchy_transform orientation potential) origin)"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_measurable:
      "slp_cauchy_transform orientation potential
        \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper potential_lp])
  have support_radius:
      "\<And>x y. \<lbrakk>cutoff x \<noteq> 0; potential y \<noteq> 0\<rbrakk> \<Longrightarrow>
        Real_Vector_Spaces.norm (x - y) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          cutoff_support potential_support])
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  have functional_finite:
      "slp_positive_branch_functional (2 * B) cutoff potential
          (\<lambda>x. ennreal (cmod
            (slp_cauchy_transform orientation potential x)))
          n origin (\<lambda>_. 1) < top_class.top"
    by (rule slp_positive_branch_functional_cauchy_terminal_unit_finite[OF
          radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
          cutoff_bound C_nonnegative support_radius])
  show ?thesis
  proof (rule
      slp_left_branch_oscillatory_graph_kernel_natural_integrable_finite[
        where B = B and cutoff = cutoff and potential = potential
          and terminal_value = "slp_cauchy_transform orientation potential"
          and origin = origin])
    show "0 \<le> B" by (rule B_nonnegative)
  next
    show "Real_Vector_Spaces.norm origin \<le> B"
      by (rule origin_bound)
  next
    fix x :: slp_point
    assume "cutoff x \<noteq> 0"
    then show "Real_Vector_Spaces.norm x \<le> B"
      by (rule cutoff_support)
  next
    fix x :: slp_point
    assume "potential x \<noteq> 0"
    then show "Real_Vector_Spaces.norm x \<le> B"
      by (rule potential_support)
  next
    show "cutoff \<in> borel_measurable lborel"
      by (rule cutoff_measurable)
  next
    show "potential \<in> borel_measurable lborel"
      by (rule potential_measurable)
  next
    show "slp_cauchy_transform orientation potential
        \<in> borel_measurable lborel"
      by (rule terminal_measurable)
  next
    show
      "slp_positive_branch_functional (2 * B) cutoff potential
          (\<lambda>x. ennreal (cmod
            (slp_cauchy_transform orientation potential x)))
          n origin (\<lambda>_. 1) < \<infinity>"
      using functional_finite unfolding infinity_ennreal_def .
  qed
qed

end

end
