theory Inverse_Schrodinger_Lp_Right_Graph_Finite_Primitive_Difference_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Amplitude_Integrable_Lp_Root"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Primitive_Difference"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Primitive_Difference_Fubini"
begin

section \<open>Root-first Fubini for the finite right primitive-difference graph\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_branch_fixed_primitive_diff_joint_integrable_lp_root:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real
    and center :: slp_point
    and X :: "slp_point set"
    and root_weight cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and root_support:
      "\<And>x :: slp_point. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and cutoff_support:
      "\<And>x :: slp_point. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x :: slp_point. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integrable lborel
      (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        root_weight (fst coordinates) *
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            (fst coordinates) (snd coordinates))"
proof -
  have root_support_cnj:
      "\<And>x :: slp_point. cnj (root_weight x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    by (rule root_support) simp
  have cutoff_support_cnj:
      "\<And>x :: slp_point. cnj (cutoff x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    by (rule cutoff_support) simp
  have potential_support_cnj:
      "\<And>x :: slp_point. cnj (potential x) \<noteq> 0 \<Longrightarrow>
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
  have root_weight_lp_cnj:
      "aim_complex_lp_on_plane p (\<lambda>x. cnj (root_weight x))"
    using root_weight_lp by simp
  have root_weight_outside_cnj:
      "\<And>x. x \<notin> X \<Longrightarrow> cnj (root_weight x) = 0"
    using root_weight_outside by simp
  have cutoff_bound_cnj:
      "\<And>x. cmod (cnj (cutoff x)) \<le> C"
    using cutoff_bound by simp
  let ?left =
    "\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      cnj (root_weight (fst coordinates)) *
        slp_left_branch_oscillatory_graph_kernel_fixed_root_finite (- tau)
          center (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
            (\<lambda>x.
              slp_cauchy_transform
                (slp_opposite_cauchy_orientation orientation)
                (\<lambda>y. cnj (potential y)) x -
              slp_cauchy_transform
                (slp_opposite_cauchy_orientation orientation)
                (\<lambda>y. cnj (potential y)) center)
          (fst coordinates) (snd coordinates)"
  have left_integrable: "integrable lborel ?left"
    by (rule slp_left_branch_fixed_primitive_diff_joint_integrable_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support_cnj cutoff_support_cnj
            potential_support_cnj p_lower p_upper X_measurable X_bounded
            cutoff_measurable_cnj potential_lp_cnj root_weight_lp_cnj
            root_weight_outside_cnj cutoff_bound_cnj C_nonnegative])
  have conjugate_integrable:
      "integrable lborel (\<lambda>coordinates. cnj (?left coordinates))"
    by (rule integrable_cnj[OF left_integrable])
  have graph_eq:
      "(\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        root_weight (fst coordinates) *
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            (fst coordinates) (snd coordinates)) =
        (\<lambda>coordinates. cnj (?left coordinates))"
    by (rule ext)
      (simp add:
        slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_def)
  show ?thesis
    unfolding graph_eq
    by (rule conjugate_integrable)
qed

theorem slp_right_branch_fixed_primitive_diff_root_fubini_lp_root:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real
    and center :: slp_point
    and X :: "slp_point set"
    and root_weight cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and root_support:
      "\<And>x :: slp_point. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and cutoff_support:
      "\<And>x :: slp_point. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x :: slp_point. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "(\<integral>root. root_weight root *
        (\<integral>inner.
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            root inner
          \<partial>(lborel ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure))
      \<partial>(lborel :: slp_point measure)) =
      (\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        root_weight (fst coordinates) *
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            (fst coordinates) (snd coordinates)
        \<partial>lborel)"
proof -
  let ?graph =
    "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
      cutoff potential
        (\<lambda>x. slp_cauchy_transform orientation potential x -
          slp_cauchy_transform orientation potential center)"
  have joint_integrable:
      "integrable lborel
        (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
          root_weight (fst coordinates) *
            ?graph (fst coordinates) (snd coordinates))"
    by (rule slp_right_branch_fixed_primitive_diff_joint_integrable_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative])
  have joint_product_integrable:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure))
        (\<lambda>(root, inner). root_weight root * ?graph root inner)"
    using joint_integrable
    by (simp only: lborel_prod split_beta')
  have root_pull:
      "(\<integral>inner. root_weight root * ?graph root inner
          \<partial>(lborel ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)) =
        root_weight root *
          (\<integral>inner. ?graph root inner
            \<partial>(lborel ::
              (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure))"
    for root :: slp_point
    by simp
  have root_split:
      "(\<integral>root. (\<integral>inner. root_weight root * ?graph root inner
          \<partial>(lborel ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure))
        \<partial>(lborel :: slp_point measure)) =
      (\<integral>(root, inner). root_weight root * ?graph root inner
        \<partial>((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)))"
    using lborel_pair.integral_fst[OF joint_product_integrable]
    by simp
  show ?thesis
    using root_split
    by (simp only: root_pull lborel_prod split_beta')
qed

end

end
