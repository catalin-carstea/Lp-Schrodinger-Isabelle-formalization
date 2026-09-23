theory Inverse_Schrodinger_Lp_Mixed_Root_Branch_Separation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Center_Terminal_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Finite_Graph_Recursive_Branches"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Product integration for the separated mixed branches\<close>

lemma slp_complex_lborel_product_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> complex"
    and g :: "'b::euclidean_space \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
  shows "integrable (lborel :: ('a \<times> 'b) measure)
      (\<lambda>xy. f (fst xy) * g (snd xy))"
    "(\<integral>(xy::'a \<times> 'b). f (fst xy) * g (snd xy) \<partial>lborel) =
      integral\<^sup>L lborel f * integral\<^sup>L lborel g"
proof -
  have f_measurable[measurable]: "f \<in> borel_measurable lborel"
    using f_integrable by measurable
  have g_measurable[measurable]: "g \<in> borel_measurable lborel"
    using g_integrable by measurable
  have product_measurable:
      "(\<lambda>xy. f (fst xy) * g (snd xy)) \<in>
        borel_measurable ((lborel :: 'a measure) \<Otimes>\<^sub>M
          (lborel :: 'b measure))"
    by measurable
  have norm_identity:
      "(\<lambda>x. \<integral>y. norm (f x * g y) \<partial>lborel) =
        (\<lambda>x. norm (f x) * (\<integral>y. norm (g y) \<partial>lborel))"
    by (rule ext)
      (simp only: norm_mult Bochner_Integration.integral_mult_right_zero)
  have outer_norm:
      "integrable lborel (\<lambda>x. \<integral>y. norm (f x * g y) \<partial>lborel)"
    unfolding norm_identity
    by (intro integrable_mult_left integrable_norm f_integrable)
  have sections:
      "AE x in lborel. integrable lborel (\<lambda>y. f x * g y)"
    by (intro AE_I2 integrable_mult_right g_integrable)
  have product_integrable:
      "integrable ((lborel :: 'a measure) \<Otimes>\<^sub>M (lborel :: 'b measure))
        (\<lambda>xy. f (fst xy) * g (snd xy))"
    by (rule lborel_pair.Fubini_integrable[OF product_measurable])
      (simp_all only: fst_conv snd_conv outer_norm sections)
  show "integrable (lborel :: ('a \<times> 'b) measure)
      (\<lambda>xy. f (fst xy) * g (snd xy))"
    using product_integrable by (simp only: lborel_prod)
  note product_value = lborel_pair.integral_fst'[OF product_integrable]
  show "(\<integral>(xy::'a \<times> 'b). f (fst xy) * g (snd xy) \<partial>lborel) =
      integral\<^sup>L lborel f * integral\<^sup>L lborel g"
    using product_value[symmetric]
    by (simp only: fst_conv snd_conv lborel_prod
        Bochner_Integration.integral_mult_right_zero
        Bochner_Integration.integral_mult_left_zero)
qed

context aim_planar_riesz_hls
begin

theorem slp_mixed_fixed_root_branch_separation:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B C p tau :: real and target origin :: slp_point
    and cutoff left_potential right_potential :: slp_scalar_field
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
          cutoff left_potential (\<lambda>_. 1) origin (fst coordinates) *
        (\<integral>terminal.
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            cutoff right_potential (\<lambda>_. 1) origin
            (snd coordinates, terminal) \<partial>lborel))"
    "(\<integral>(coordinates ::
        (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
        ((slp_point^'j) \<times> (slp_point^'j))).
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
        cutoff left_potential (\<lambda>_. 1) origin (fst coordinates) *
      (\<integral>terminal.
        slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          cutoff right_potential (\<lambda>_. 1) origin
          (snd coordinates, terminal) \<partial>lborel) \<partial>lborel) =
      slp_left_recursive_branch CARD('i) tau target cutoff left_potential
        (\<lambda>_. 1) origin *
      slp_right_recursive_branch CARD('j) tau target cutoff right_potential
        (\<lambda>_. 1) origin"
proof -
  let ?L = "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
    cutoff left_potential (\<lambda>_. 1) origin ::
      (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow> complex"
  let ?R = "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
    cutoff right_potential (\<lambda>_. 1) origin ::
      (((slp_point^'j) \<times> (slp_point^'j)) \<times> slp_point) \<Rightarrow> complex"
  let ?S = "\<lambda>arrays. \<integral>terminal. ?R (arrays, terminal) \<partial>lborel"
  have left_integrable: "integrable lborel ?L"
    by (rule slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_integrable_hls[
        OF B_nonnegative origin_bound cutoff_support left_support p_lower
          p_upper cutoff_measurable left_lp cutoff_bound C_nonnegative])
  have right_integrable: "integrable lborel ?R"
    by (rule slp_right_finite_graph_integrable[
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
      slp_left_recursive_branch CARD('i) tau target cutoff left_potential
        (\<lambda>_. 1) origin"
    by (rule slp_finite_graph_integrals_eq_recursive(1)[
        OF B_nonnegative origin_bound cutoff_support left_support p_lower
          p_upper cutoff_measurable left_lp cutoff_bound C_nonnegative])
  have right_value: "integral\<^sup>L lborel ?R =
      slp_right_recursive_branch CARD('j) tau target cutoff right_potential
        (\<lambda>_. 1) origin"
    by (rule slp_finite_graph_integrals_eq_recursive(2)[
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
      slp_left_recursive_branch CARD('i) tau target cutoff left_potential
        (\<lambda>_. 1) origin *
      slp_right_recursive_branch CARD('j) tau target cutoff right_potential
        (\<lambda>_. 1) origin"
    using slp_complex_lborel_product_integral(2)[OF
        left_integrable section_integrable]
    by (simp only: section_value left_value right_value)
qed

theorem slp_mixed_terminal_reduced_integrable:
  fixes tau B C p :: real
    and target :: slp_point
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_weight_integrable: "integrable lborel root_weight"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows "integrable
      (lborel :: ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates measure)
      (\<lambda>coordinates. root_weight (fst coordinates) *
          slp_center_kernel (- tau) target (fst coordinates) *
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            cutoff left_potential (\<lambda>_. 1) (fst coordinates)
            (fst (snd coordinates)) *
          (\<integral>terminal.
            slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
              cutoff right_potential (\<lambda>_. 1) (fst coordinates)
              (snd (snd coordinates), terminal) \<partial>lborel))"
proof -
  have right_measurable: "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have joint:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: ('i, 'j) slp_mixed_center_finite_coordinates measure))
        (case_prod (\<lambda>center coordinates.
          slp_center_kernel tau target center *
            slp_mixed_center_finite_oscillatory_integrand tau root_weight
              cutoff left_potential cutoff right_potential center coordinates))"
    by (rule slp_mixed_center_finite_center_kernel_joint_integrable[OF
        B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
        right_potential_lp cutoff_bound C_nonnegative root_weight_integrable
        root_support cutoff_support left_potential_support right_potential_support])
  have iterated:
      "integrable (lborel ::
          ('i, 'j) slp_mixed_center_finite_coordinates measure)
        (\<lambda>coordinates. \<integral>center.
          slp_center_kernel tau target center *
            slp_mixed_center_finite_oscillatory_integrand tau root_weight
              cutoff left_potential cutoff right_potential center coordinates
          \<partial>lborel)"
    by (rule lborel_pair.integrable_snd[OF joint])
  show ?thesis
    using iterated
    by (simp only: slp_mixed_center_finite_terminal_integral[
        OF cutoff_measurable right_measurable])
qed

end

end
