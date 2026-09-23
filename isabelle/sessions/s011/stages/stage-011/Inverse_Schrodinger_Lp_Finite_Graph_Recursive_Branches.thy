theory Inverse_Schrodinger_Lp_Finite_Graph_Recursive_Branches
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Right_Graph_Natural_Recursive_Branch_Identity"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Natural_Finite_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Finite_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Finite_Coordinate_HLS_Integrable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Finite graph integrals retain the exact recursive Born meaning\<close>

context aim_planar_riesz_hls
begin

theorem slp_finite_graph_integrals_eq_recursive:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real and center origin :: slp_point
    and cutoff potential :: slp_scalar_field
  assumes B_nonnegative: "0 \<le> B" and origin_bound: "norm origin \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>_. 1) origin) = slp_left_recursive_branch CARD('i) tau center cutoff potential (\<lambda>_. 1) origin"
    "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>_. 1) origin) = slp_right_recursive_branch CARD('i) tau center cutoff potential (\<lambda>_. 1) origin"
proof -
  have potential_measurable: "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable: "(\<lambda>_::slp_point. 1::complex) \<in> borel_measurable lborel"
    by measurable
  have left_transport: "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>_. 1) origin) = integral\<^sup>L (((PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_natural CARD('i) tau center
          cutoff potential (\<lambda>_. 1) origin)"
    by (rule slp_left_branch_graph_natural_finite_integral[OF
        cutoff_measurable potential_measurable unit_measurable])
  have left_natural: "integral\<^sup>L (((PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_natural CARD('i) tau center
          cutoff potential (\<lambda>_. 1) origin) = slp_left_recursive_branch CARD('i) tau center cutoff potential (\<lambda>_. 1) origin"
    by (rule slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_recursive_hls[OF
        B_nonnegative origin_bound cutoff_support potential_support p_lower
        p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative])
  show "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>_. 1) origin) = slp_left_recursive_branch CARD('i) tau center cutoff potential (\<lambda>_. 1) origin"
    by (rule trans[OF left_transport left_natural])
  have right_transport: "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>_. 1) origin) = integral\<^sup>L (((PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
        (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
          cutoff potential (\<lambda>_. 1) origin)"
    by (rule slp_right_branch_graph_natural_finite_integral[OF
        cutoff_measurable potential_measurable unit_measurable])
  have right_natural: "integral\<^sup>L (((PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
        (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
          cutoff potential (\<lambda>_. 1) origin) = slp_right_recursive_branch CARD('i) tau center cutoff potential (\<lambda>_. 1) origin"
    by (rule slp_right_branch_oscillatory_graph_kernel_natural_integral_eq_recursive_hls[OF
        B_nonnegative origin_bound cutoff_support potential_support p_lower
        p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative])
  show "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>_. 1) origin) = slp_right_recursive_branch CARD('i) tau center cutoff potential (\<lambda>_. 1) origin"
    by (rule trans[OF right_transport right_natural])
qed

section \<open>Absolute integrability of the right finite graph\<close>

theorem slp_right_finite_graph_integrable:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real and center origin :: slp_point
    and cutoff potential :: slp_scalar_field
  assumes B_nonnegative: "0 \<le> B" and origin_bound: "norm origin \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows "integrable (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
    (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
      cutoff potential (\<lambda>_. 1) origin)"
proof -
  have cutoff_support_cnj:
      "\<And>x. cnj (cutoff x) \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    by (rule cutoff_support) simp
  have potential_support_cnj:
      "\<And>x. cnj (potential x) \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    by (rule potential_support) simp
  have cnj_borel: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
        continuous_on_cnj[OF continuous_on_id]])
  have cutoff_measurable_cnj:
      "(\<lambda>x. cnj (cutoff x)) \<in> borel_measurable lborel"
    using measurable_comp[OF cutoff_measurable cnj_borel]
    by (simp add: comp_def)
  have potential_lp_cnj:
      "aim_complex_lp_on_plane p (\<lambda>x. cnj (potential x))"
    using potential_lp by simp
  have cutoff_bound_cnj: "\<And>x. norm (cnj (cutoff x)) \<le> C"
    using cutoff_bound by simp
  have left_integrable:
      "integrable (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
        (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite (-tau) center
          (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
          (\<lambda>_. 1) origin)"
    by (rule slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_integrable_hls[OF
        B_nonnegative origin_bound cutoff_support_cnj potential_support_cnj
        p_lower p_upper cutoff_measurable_cnj potential_lp_cnj cutoff_bound_cnj C_nonnegative])
  have conjugate_integrable:
      "integrable (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
        (\<lambda>coordinates. cnj
          (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite (-tau) center
            (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
            (\<lambda>_. 1) origin coordinates))"
    by (rule integrable_cnj[OF left_integrable])
  show ?thesis
    using conjugate_integrable
    unfolding slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_def
    by simp
qed

end

end

