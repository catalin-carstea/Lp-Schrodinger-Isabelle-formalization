theory Inverse_Schrodinger_Lp_Left_Graph_Finite_Primitive_Difference_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Primitive_Difference_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Amplitude_Integrable_Lp_Root"
begin

section \<open>Root-first Fubini for the finite primitive-difference graph\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_fixed_primitive_diff_joint_integrable_lp_root:
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
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            (fst coordinates) (snd coordinates))"
proof -
  let ?primitive = "slp_cauchy_transform orientation potential"
  let ?primitive_amplitude =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      ?primitive (\<lambda>_. 1) ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?unit_amplitude =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      (\<lambda>_. 1) (\<lambda>_. 1) ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?oscillation =
    "\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      exp (\<i> * of_real
        (tau * slp_one_sided_finite_residual coordinates))"
  have primitive_amplitude_integrable:
      "integrable lborel ?primitive_amplitude"
    by (rule slp_left_branch_complex_amplitude_finite_cauchy_integrable_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative])
  have unit_amplitude_integrable:
      "integrable lborel ?unit_amplitude"
    by (rule slp_left_branch_complex_amplitude_finite_unit_integrable_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative])
  have residual_measurable:
      "(slp_one_sided_finite_residual ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> real) \<in>
        borel_measurable lborel"
    unfolding slp_one_sided_finite_residual_def
    using measurable_compose[
      OF measurable_compose[
        OF slp_one_sided_finite_to_packed_coordinates_measurable measurable_snd]
        slp_one_sided_packed_residual_measurable]
    by (simp only: comp_def)
  have phase_measurable:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        tau * slp_one_sided_finite_residual coordinates) \<in>
        borel_measurable lborel"
    using residual_measurable by measurable
  have primitive_oscillatory_integrable:
      "integrable lborel
        (\<lambda>coordinates. ?oscillation coordinates *
          ?primitive_amplitude coordinates)"
    by (rule slp_unit_modulus_real_phase_integrable[OF
          primitive_amplitude_integrable phase_measurable])
  have unit_oscillatory_integrable:
      "integrable lborel
        (\<lambda>coordinates. ?oscillation coordinates *
          ?unit_amplitude coordinates)"
    by (rule slp_unit_modulus_real_phase_integrable[OF
          unit_amplitude_integrable phase_measurable])
  have scaled_unit_integrable:
      "integrable lborel
        (\<lambda>coordinates. ?primitive center *
          (?oscillation coordinates * ?unit_amplitude coordinates))"
    by (rule Bochner_Integration.integrable_mult_right[OF
          unit_oscillatory_integrable])
  have bracket_integrable:
      "integrable lborel
        (\<lambda>coordinates.
          ?oscillation coordinates * ?primitive_amplitude coordinates -
          ?primitive center *
            (?oscillation coordinates * ?unit_amplitude coordinates))"
    by (rule Bochner_Integration.integrable_diff[OF
          primitive_oscillatory_integrable scaled_unit_integrable])
  have output_measurable:
      "(\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        slp_left_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd coordinates)) $ i)
            (\<lambda>i. snd (fst (snd coordinates)) $ i))
          (snd (snd coordinates))) \<in> borel_measurable lborel"
    by (rule slp_left_branch_finite_output_measurable)
  have center_kernel_factor_measurable:
      "(\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        slp_center_kernel tau center
          (slp_left_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates)))) \<in> borel_measurable lborel"
  proof -
    have center_kernel_borel_measurable:
        "slp_center_kernel tau center \<in> borel_measurable borel"
      using slp_center_kernel_measurable[of tau center]
      by (simp only: measurable_lborel2)
    show ?thesis
      using measurable_compose[OF output_measurable
          center_kernel_borel_measurable]
    by (simp only: comp_def)
  qed
  have bracket_measurable:
      "(\<lambda>coordinates.
        ?oscillation coordinates * ?primitive_amplitude coordinates -
        ?primitive center *
          (?oscillation coordinates * ?unit_amplitude coordinates)) \<in>
        borel_measurable lborel"
    using bracket_integrable by measurable
  have factored_integrable:
      "integrable lborel
        (\<lambda>coordinates.
          slp_center_kernel tau center
            (slp_left_branch_output
              (slp_finite_branch_pair_list
                (\<lambda>i. fst (fst (snd coordinates)) $ i)
                (\<lambda>i. snd (fst (snd coordinates)) $ i))
              (snd (snd coordinates))) *
          (?oscillation coordinates * ?primitive_amplitude coordinates -
            ?primitive center *
              (?oscillation coordinates * ?unit_amplitude coordinates)))"
  proof (rule Bochner_Integration.integrable_bound[OF bracket_integrable])
    show "(\<lambda>coordinates.
        slp_center_kernel tau center
          (slp_left_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates))) *
        (?oscillation coordinates * ?primitive_amplitude coordinates -
          ?primitive center *
            (?oscillation coordinates * ?unit_amplitude coordinates))) \<in>
      borel_measurable lborel"
      using center_kernel_factor_measurable bracket_measurable
      by measurable
    show "AE coordinates in lborel.
        norm_class.norm
          (slp_center_kernel tau center
            (slp_left_branch_output
              (slp_finite_branch_pair_list
                (\<lambda>i. fst (fst (snd coordinates)) $ i)
                (\<lambda>i. snd (fst (snd coordinates)) $ i))
              (snd (snd coordinates))) *
            (?oscillation coordinates * ?primitive_amplitude coordinates -
              ?primitive center *
                (?oscillation coordinates * ?unit_amplitude coordinates)))
        \<le> norm_class.norm
          (?oscillation coordinates * ?primitive_amplitude coordinates -
            ?primitive center *
              (?oscillation coordinates * ?unit_amplitude coordinates))"
      unfolding slp_center_kernel_def
      by (simp only: norm_mult norm_exp_i_times mult_1_left order_refl
          eventually_True)
  qed
  have graph_eq:
      "(\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
          root_weight (fst coordinates) *
            slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
              center cutoff potential
                (\<lambda>x. ?primitive x - ?primitive center)
              (fst coordinates) (snd coordinates)) =
        (\<lambda>coordinates.
          slp_center_kernel tau center
            (slp_left_branch_output
              (slp_finite_branch_pair_list
                (\<lambda>i. fst (fst (snd coordinates)) $ i)
                (\<lambda>i. snd (fst (snd coordinates)) $ i))
              (snd (snd coordinates))) *
          (?oscillation coordinates * ?primitive_amplitude coordinates -
            ?primitive center *
              (?oscillation coordinates * ?unit_amplitude coordinates)))"
    by (rule ext)
      (rule
        slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_primitive_diff)
  show ?thesis
    apply (subst graph_eq)
    by (rule factored_integrable)
qed

theorem slp_left_branch_fixed_primitive_diff_root_fubini_lp_root:
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
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            root inner
          \<partial>(lborel ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure))
      \<partial>(lborel :: slp_point measure)) =
      (\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        root_weight (fst coordinates) *
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            (fst coordinates) (snd coordinates)
        \<partial>lborel)"
proof -
  let ?graph =
    "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
      cutoff potential
        (\<lambda>x. slp_cauchy_transform orientation potential x -
          slp_cauchy_transform orientation potential center)"
  have joint_integrable:
      "integrable lborel
        (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
          root_weight (fst coordinates) *
            ?graph (fst coordinates) (snd coordinates))"
    by (rule slp_left_branch_fixed_primitive_diff_joint_integrable_lp_root[
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
