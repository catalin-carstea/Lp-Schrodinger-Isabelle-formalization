theory Inverse_Schrodinger_Lp_Right_Graph_Finite_Amplitude_Integrable_Lp_Root
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Amplitude_Conjugate"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Amplitude_Integrable_Lp_Root"
begin

section \<open>Physical integrability of finite right amplitudes\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_branch_complex_amplitude_finite_unit_integrable_lp_root:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and root_weight cutoff potential :: "slp_point \<Rightarrow> complex"
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
      (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
        (\<lambda>_. 1) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
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
  have left_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite
          (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x)) (\<lambda>_. 1) (\<lambda>_. 1) ::
            'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
        slp_left_branch_complex_amplitude_finite_unit_integrable_lp_root[
          OF B_nonnegative root_support_cnj cutoff_support_cnj
            potential_support_cnj p_lower p_upper X_measurable X_bounded
            cutoff_measurable_cnj potential_lp_cnj root_weight_lp_cnj
            root_weight_outside_cnj cutoff_bound_cnj C_nonnegative])
  note conjugate_iff =
    slp_right_branch_complex_amplitude_finite_integrable_iff[
      where M = lborel and root_weight = root_weight and cutoff = cutoff
        and potential = potential and terminal_value = "\<lambda>_. 1"
        and output_factor = "\<lambda>_. 1" and 'i = 'i]
  show ?thesis
    using conjugate_iff left_integrable by simp
qed

theorem slp_right_branch_complex_amplitude_finite_cauchy_integrable_lp_root:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
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
      (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
        (slp_cauchy_transform orientation potential) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
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
  have left_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite
          (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x))
          (slp_cauchy_transform (slp_opposite_cauchy_orientation orientation)
            (\<lambda>x. cnj (potential x)))
          (\<lambda>_. 1) ::
            'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
        slp_left_branch_complex_amplitude_finite_cauchy_integrable_lp_root[
          OF B_nonnegative root_support_cnj cutoff_support_cnj
            potential_support_cnj p_lower p_upper X_measurable X_bounded
            cutoff_measurable_cnj potential_lp_cnj root_weight_lp_cnj
            root_weight_outside_cnj cutoff_bound_cnj C_nonnegative])
  note conjugate_iff =
    slp_right_branch_complex_amplitude_finite_integrable_iff[
      where M = lborel and root_weight = root_weight and cutoff = cutoff
        and potential = potential
        and terminal_value = "slp_cauchy_transform orientation potential"
        and output_factor = "\<lambda>_. 1" and 'i = 'i]
  show ?thesis
    using conjugate_iff left_integrable by simp
qed

end

end
