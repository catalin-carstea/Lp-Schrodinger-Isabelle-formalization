theory Inverse_Schrodinger_Lp_Mixed_Primitive_Branch_Separation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Cauchy_Preaverage"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Primitive_Difference"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Absolute convergence and separation of the actual branches\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_finite_primitive_graphs_integrable:
  fixes branch_type :: "'i::finite itself" and B C p tau :: real
    and center origin :: slp_point and cutoff potential :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"

  shows "integrable (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin)"
    and "integrable (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin)"
proof -
  have potential_measurable: "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have cauchy_measurable:
    "slp_cauchy_transform orientation potential \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper potential_lp])
  have terminal_measurable:
    "(\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) \<in> borel_measurable lborel"
    using cauchy_measurable by measurable
  have left_natural: "integrable (((PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure)))
      \<Otimes>\<^sub>M (PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure))))
      \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_left_branch_oscillatory_graph_kernel_natural CARD('i) tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin)"
    by (rule slp_left_branch_oscillatory_graph_kernel_natural_primitive_diff_integrable[OF
        B_nonnegative origin_bound cutoff_support potential_support p_lower
        p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative])
  note left_finite = slp_left_branch_graph_natural_finite_integrable_iff[
      where 'i='i and tau=tau and center=center and origin=origin,
      OF cutoff_measurable potential_measurable terminal_measurable]
  show "integrable (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin)"
    using left_finite left_natural by blast
  have right_natural: "integrable (((PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure)))
      \<Otimes>\<^sub>M (PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure))))
      \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin)"
    by (rule slp_right_branch_oscillatory_graph_kernel_natural_primitive_diff_integrable[OF
        B_nonnegative origin_bound cutoff_support potential_support p_lower
        p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative])
  note right_finite = slp_right_branch_graph_natural_finite_integrable_iff[
      where 'i='i and tau=tau and center=center and origin=origin,
      OF cutoff_measurable potential_measurable terminal_measurable]
  show "integrable (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin)"
    using right_finite right_natural by blast
qed

theorem slp_mixed_primitive_fixed_root_branch_separation:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B C p tau :: real and target origin :: slp_point
    and cutoff left_potential right_potential :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_support: "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_support: "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_lp: "aim_complex_lp_on_plane p left_potential"
    and right_lp: "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integrable
      (lborel :: ((((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
        ((slp_point^'j) \<times> (slp_point^'j))) measure)
      (\<lambda>coordinates.
        slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          cutoff left_potential
          (\<lambda>x. slp_cauchy_transform lo left_potential x -
            slp_cauchy_transform lo left_potential target) origin (fst coordinates) *
        (\<integral>terminal.
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            cutoff right_potential
          (\<lambda>x. slp_cauchy_transform ro right_potential x -
            slp_cauchy_transform ro right_potential target) origin
            (snd coordinates, terminal) \<partial>lborel))"
    "(\<integral>(coordinates ::
        (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
        ((slp_point^'j) \<times> (slp_point^'j))).
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
        cutoff left_potential
          (\<lambda>x. slp_cauchy_transform lo left_potential x -
            slp_cauchy_transform lo left_potential target) origin (fst coordinates) *
      (\<integral>terminal.
        slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          cutoff right_potential
          (\<lambda>x. slp_cauchy_transform ro right_potential x -
            slp_cauchy_transform ro right_potential target) origin
          (snd coordinates, terminal) \<partial>lborel) \<partial>lborel) =
      slp_left_neumann_iterate CARD('i) tau target cutoff left_potential lo origin *
      slp_right_neumann_iterate CARD('j) tau target cutoff right_potential ro origin"
proof -
  let ?L = "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
    cutoff left_potential
          (\<lambda>x. slp_cauchy_transform lo left_potential x -
            slp_cauchy_transform lo left_potential target) origin ::
      (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow> complex"
  let ?R = "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
    cutoff right_potential
          (\<lambda>x. slp_cauchy_transform ro right_potential x -
            slp_cauchy_transform ro right_potential target) origin ::
      (((slp_point^'j) \<times> (slp_point^'j)) \<times> slp_point) \<Rightarrow> complex"
  let ?S = "\<lambda>arrays. \<integral>terminal. ?R (arrays, terminal) \<partial>lborel"
  have left_integrable: "integrable lborel ?L"
    by (rule slp_finite_primitive_graphs_integrable(1)[
        OF B_nonnegative origin_bound cutoff_support left_support p_lower
          p_upper cutoff_measurable left_lp cutoff_bound C_nonnegative])
  have right_integrable: "integrable lborel ?R"
    by (rule slp_finite_primitive_graphs_integrable(2)[
        OF B_nonnegative origin_bound cutoff_support right_support p_lower
          p_upper cutoff_measurable right_lp cutoff_bound C_nonnegative])
  have right_product:
      "integrable
        ((lborel :: ((slp_point^'j) \<times> (slp_point^'j)) measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))
        (case_prod (\<lambda>arrays terminal. ?R (arrays, terminal)))"
    using right_integrable by (simp only: lborel_prod case_prod_eta)
  have section_integrable: "integrable lborel ?S"
    by (rule lborel_pair.integrable_fst[OF right_product])
  have section_value: "integral\<^sup>L lborel ?S = integral\<^sup>L lborel ?R"
    using lborel_pair.integral_fst[OF right_product]
    by (simp only: lborel_prod case_prod_eta)
  have left_value: "integral\<^sup>L lborel ?L =
      slp_left_neumann_iterate CARD('i) tau target cutoff left_potential lo origin"
    by (rule slp_finite_graph_integrals_eq_neumann(1)[
        OF B_nonnegative origin_bound cutoff_support left_support p_lower
          p_upper cutoff_measurable left_lp cutoff_bound C_nonnegative])
  have right_value: "integral\<^sup>L lborel ?R =
      slp_right_neumann_iterate CARD('j) tau target cutoff right_potential ro origin"
    by (rule slp_finite_graph_integrals_eq_neumann(2)[
        OF B_nonnegative origin_bound cutoff_support right_support p_lower
          p_upper cutoff_measurable right_lp cutoff_bound C_nonnegative])
  show "integrable
      (lborel :: ((((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
        ((slp_point^'j) \<times> (slp_point^'j))) measure)
      (\<lambda>coordinates. ?L (fst coordinates) * ?S (snd coordinates))"
    by (rule slp_complex_lborel_product_integral(1)[OF
        left_integrable section_integrable])
  show "(\<integral>coordinates. ?L (fst coordinates) * ?S (snd coordinates)
        \<partial>lborel) =
      slp_left_neumann_iterate CARD('i) tau target cutoff left_potential lo origin *
      slp_right_neumann_iterate CARD('j) tau target cutoff right_potential ro origin"
    using slp_complex_lborel_product_integral(2)[OF
        left_integrable section_integrable]
    by (simp only: section_value left_value right_value)
qed

end

end
