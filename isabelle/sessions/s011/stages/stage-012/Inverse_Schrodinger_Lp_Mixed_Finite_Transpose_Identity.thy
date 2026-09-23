theory Inverse_Schrodinger_Lp_Mixed_Finite_Transpose_Identity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Root_Branch_Separation"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exact root integral for the finite mixed transpose\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_root_integral_identification:
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
  shows
    "integrable lborel (\<lambda>root. root_weight root * slp_center_kernel (-tau) target root *
        slp_left_recursive_branch CARD('i) tau target cutoff left_potential
          (\<lambda>_. 1) root *
        slp_right_recursive_branch CARD('j) tau target cutoff right_potential
          (\<lambda>_. 1) root)"
    "(\<integral>(coordinates ::
        ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates).
      root_weight (fst coordinates) *
          slp_center_kernel (- tau) target (fst coordinates) *
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            cutoff left_potential (\<lambda>_. 1) (fst coordinates)
            (fst (snd coordinates)) *
          (\<integral>terminal.
            slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
              cutoff right_potential (\<lambda>_. 1) (fst coordinates)
              (snd (snd coordinates), terminal) \<partial>lborel) \<partial>lborel) =
      (\<integral>root. root_weight root * slp_center_kernel (-tau) target root *
        slp_left_recursive_branch CARD('i) tau target cutoff left_potential
          (\<lambda>_. 1) root *
        slp_right_recursive_branch CARD('j) tau target cutoff right_potential
          (\<lambda>_. 1) root \<partial>lborel)"
proof -
  let ?J = "\<lambda>coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates.
    root_weight (fst coordinates) *
          slp_center_kernel (- tau) target (fst coordinates) *
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            cutoff left_potential (\<lambda>_. 1) (fst coordinates)
            (fst (snd coordinates)) *
          (\<integral>terminal.
            slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
              cutoff right_potential (\<lambda>_. 1) (fst coordinates)
              (snd (snd coordinates), terminal) \<partial>lborel)"
  let ?F = "\<lambda>root. \<integral>(branches :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
      ((slp_point^'j) \<times> (slp_point^'j))). ?J (root, branches) \<partial>lborel"
  let ?H = "\<lambda>root. root_weight root * slp_center_kernel (-tau) target root *
        slp_left_recursive_branch CARD('i) tau target cutoff left_potential
          (\<lambda>_. 1) root *
        slp_right_recursive_branch CARD('j) tau target cutoff right_potential
          (\<lambda>_. 1) root"
  have joint_integrable: "integrable lborel ?J"
    by (rule slp_mixed_terminal_reduced_integrable[OF
        B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
        right_potential_lp cutoff_bound C_nonnegative root_weight_integrable
        root_support cutoff_support left_potential_support right_potential_support])
  have product_integrable:
      "integrable ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: ((((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
      ((slp_point^'j) \<times> (slp_point^'j))) measure))
        ?J"
    using joint_integrable by (simp only: lborel_prod)
  have root_integrable: "integrable lborel ?F"
    by (rule lborel_pair.integrable_fst'[OF product_integrable])
  have root_integral:
      "integral\<^sup>L lborel ?F = integral\<^sup>L lborel ?J"
    using lborel_pair.integral_fst'[OF product_integrable]
    by (simp only: lborel_prod)
  have root_identity: "?F root = ?H root" for root
  proof (cases "root_weight root = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have root_bound: "norm root \<le> B"
      by (rule root_support[OF False])
    have separation:
        "(\<integral>(branches :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
      ((slp_point^'j) \<times> (slp_point^'j))).
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            cutoff left_potential (\<lambda>_. 1) root (fst branches) *
          (\<integral>terminal.
            slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
              cutoff right_potential (\<lambda>_. 1) root
              (snd branches, terminal) \<partial>lborel) \<partial>lborel) =
          slp_left_recursive_branch CARD('i) tau target cutoff left_potential
            (\<lambda>_. 1) root *
          slp_right_recursive_branch CARD('j) tau target cutoff right_potential
            (\<lambda>_. 1) root"
      by (rule slp_mixed_fixed_root_branch_separation(2)[OF
          B_nonnegative root_bound cutoff_support left_potential_support
          right_potential_support p_lower p_upper cutoff_measurable
          left_potential_lp right_potential_lp cutoff_bound C_nonnegative])
    show ?thesis
      by (simp only: fst_conv snd_conv mult.assoc
          Bochner_Integration.integral_mult_right_zero separation)
  qed
  show "integrable lborel ?H"
    using root_integrable by (simp only: root_identity)
  show "integral\<^sup>L lborel ?J = integral\<^sup>L lborel ?H"
    using root_integral[symmetric] by (simp only: root_identity)
qed

theorem slp_mixed_finite_center_average_transpose:
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
  shows
    "slp_center_average tau
        (slp_mixed_center_finite_fiber_integral TYPE('i::finite) TYPE('j::finite)
          tau root_weight cutoff left_potential cutoff right_potential) target =
      of_real (tau / pi) * (\<integral>root. root_weight root * slp_center_kernel (-tau) target root *
        slp_left_recursive_branch CARD('i) tau target cutoff left_potential
          (\<lambda>_. 1) root *
        slp_right_recursive_branch CARD('j) tau target cutoff right_potential
          (\<lambda>_. 1) root \<partial>lborel)"
proof -
  have center_to_coordinates:
      "(\<integral>center. slp_center_kernel tau target center *
          slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) tau root_weight
            cutoff left_potential cutoff right_potential center \<partial>lborel) =
        (\<integral>(coordinates ::
            ('i, 'j) slp_mixed_center_finite_coordinates).
          root_weight (fst coordinates) *
          slp_center_kernel (- tau) target (fst coordinates) *
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            cutoff left_potential (\<lambda>_. 1) (fst coordinates)
            (fst (snd coordinates)) *
          (\<integral>terminal.
            slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
              cutoff right_potential (\<lambda>_. 1) (fst coordinates)
              (snd (snd coordinates), terminal) \<partial>lborel) \<partial>lborel)"
    by (rule slp_mixed_center_finite_terminal_fubini[OF
        B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
        right_potential_lp cutoff_bound C_nonnegative root_weight_integrable
        root_support cutoff_support left_potential_support right_potential_support])
  have coordinates_to_root:
      "(\<integral>(coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates).
        root_weight (fst coordinates) *
          slp_center_kernel (- tau) target (fst coordinates) *
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            cutoff left_potential (\<lambda>_. 1) (fst coordinates)
            (fst (snd coordinates)) *
          (\<integral>terminal.
            slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
              cutoff right_potential (\<lambda>_. 1) (fst coordinates)
              (snd (snd coordinates), terminal) \<partial>lborel) \<partial>lborel) =
        (\<integral>root. root_weight root * slp_center_kernel (-tau) target root *
        slp_left_recursive_branch CARD('i) tau target cutoff left_potential
          (\<lambda>_. 1) root *
        slp_right_recursive_branch CARD('j) tau target cutoff right_potential
          (\<lambda>_. 1) root \<partial>lborel)"
    by (rule slp_mixed_root_integral_identification(2)[OF
        B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
        right_potential_lp cutoff_bound C_nonnegative root_weight_integrable
        root_support cutoff_support left_potential_support right_potential_support])
  have core:
      "(\<integral>center. slp_center_kernel tau target center *
          slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) tau root_weight
            cutoff left_potential cutoff right_potential center \<partial>lborel) =
        (\<integral>root. root_weight root * slp_center_kernel (-tau) target root *
        slp_left_recursive_branch CARD('i) tau target cutoff left_potential
          (\<lambda>_. 1) root *
        slp_right_recursive_branch CARD('j) tau target cutoff right_potential
          (\<lambda>_. 1) root \<partial>lborel)"
    by (rule trans[OF center_to_coordinates coordinates_to_root])
  show ?thesis
    unfolding slp_center_average_def
    by (simp only: core)
qed

end

end
