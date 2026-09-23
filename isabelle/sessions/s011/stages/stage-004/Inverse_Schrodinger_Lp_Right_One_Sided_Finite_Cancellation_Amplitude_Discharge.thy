theory Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Cancellation_Amplitude_Discharge
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Cancellation_Algebra"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_One_Sided_Finite_Cancellation_Amplitude_Discharge"
begin

section \<open>Direct right finite cancellation-amplitude premise discharge\<close>

theorem slp_right_branch_complex_amplitude_finite_bounded_output_integrable:
  fixes branch_dummy :: "'i::finite itself"
    and output_factor :: "slp_point \<Rightarrow> complex"
    and K :: real
  assumes unit_output_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    and output_factor_bound:
      "\<And>x. Real_Vector_Spaces.norm (output_factor x) \<le> K"
  shows
    "integrable lborel
      (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
        terminal_value output_factor ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
proof -
  have output_factor_cnj_measurable:
      "(\<lambda>x. cnj (output_factor x)) \<in> borel_measurable lborel"
  proof -
    have cnj_borel_measurable: "cnj \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF
            continuous_on_cnj[OF continuous_on_id]])
    show ?thesis
      using measurable_comp[OF output_factor_measurable cnj_borel_measurable]
      by (simp add: comp_def)
  qed
  have output_factor_cnj_bound:
      "\<And>x. Real_Vector_Spaces.norm (cnj (output_factor x)) \<le> K"
    using output_factor_bound by simp
  note unit_conjugate_iff =
    slp_right_branch_complex_amplitude_finite_integrable_iff[
      where M = lborel and root_weight = root_weight and cutoff = cutoff
        and potential = potential and terminal_value = terminal_value
        and output_factor = "\<lambda>_. 1" and 'i = 'i]
  have left_unit_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite
          (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
          (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    using unit_conjugate_iff unit_output_integrable by simp
  have left_target_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite
          (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
          (\<lambda>x. cnj (output_factor x)) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_left_branch_complex_amplitude_finite_bounded_output_integrable[
        OF left_unit_integrable output_factor_cnj_measurable
          output_factor_cnj_bound])
  note target_conjugate_iff =
    slp_right_branch_complex_amplitude_finite_integrable_iff[
      where M = lborel and root_weight = root_weight and cutoff = cutoff
        and potential = potential and terminal_value = terminal_value
        and output_factor = output_factor and 'i = 'i]
  show ?thesis
    using target_conjugate_iff left_target_integrable by simp
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_branch_complex_amplitude_finite_unit_terminal_l2_integrable:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and cutoff potential output_factor :: "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
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
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and output_factor_l2: "aim_complex_lp_on_plane 2 output_factor"
  shows
    "integrable lborel
      (slp_right_branch_complex_amplitude_finite potential cutoff potential
        (\<lambda>_. 1) output_factor ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
proof -
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
  have potential_outside_cnj:
      "\<And>x. x \<notin> X \<Longrightarrow> cnj (potential x) = 0"
    using potential_outside by simp
  have cutoff_bound_cnj:
      "\<And>x. cmod (cnj (cutoff x)) \<le> C"
    using cutoff_bound by simp
  have output_factor_l2_cnj:
      "aim_complex_lp_on_plane 2 (\<lambda>x. cnj (output_factor x))"
    using output_factor_l2 by simp
  have left_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite
          (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x)) (\<lambda>_. 1)
          (\<lambda>x. cnj (output_factor x)) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_left_branch_complex_amplitude_finite_unit_terminal_l2_integrable[
        where B = B and C = C and p = p and X = X,
        OF B_nonnegative cutoff_support_cnj potential_support_cnj p_lower
          p_upper X_measurable X_bounded potential_lp_cnj
          potential_outside_cnj cutoff_measurable_cnj cutoff_bound_cnj
          C_nonnegative output_factor_l2_cnj])
  note conjugate_iff =
    slp_right_branch_complex_amplitude_finite_integrable_iff[
      where M = lborel and root_weight = potential and cutoff = cutoff
        and potential = potential and terminal_value = "\<lambda>_. 1"
        and output_factor = output_factor and 'i = 'i]
  show ?thesis
    using conjugate_iff left_integrable by simp
qed

theorem slp_right_branch_finite_cancellation_model_eq_evaluated_pair_lp_root:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real
    and X :: "slp_point set"
    and cutoff potential phi :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
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
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and phi_test: "slp_test_function_on UNIV phi"
    and source_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)"
    and center_source_l2:
      "aim_complex_lp_on_plane 2
        (slp_center_average tau
          (\<lambda>u. phi u * slp_cauchy_transform orientation potential u))"
  shows
    "slp_right_branch_finite_cancellation_model TYPE('i) tau potential
        cutoff potential (slp_cauchy_transform orientation potential) phi =
      slp_right_branch_finite_oscillatory_integral TYPE('i) tau potential
          cutoff potential (slp_cauchy_transform orientation potential)
            (slp_center_average tau phi) -
        slp_right_branch_finite_oscillatory_integral TYPE('i) tau potential
          cutoff potential (\<lambda>_. 1)
            (slp_center_average tau
              (\<lambda>u.
                phi u * slp_cauchy_transform orientation potential u))"
proof -
  let ?terminal = "slp_cauchy_transform orientation potential"
  let ?source = "\<lambda>u. phi u * ?terminal u"
  note phi_data = slp_test_function_integrable_bounded[OF phi_test]
  have phi_integrable: "integrable lborel phi"
    by (rule phi_data(1))
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  obtain K where phi_bound:
      "\<And>x. Real_Vector_Spaces.norm (phi x) \<le> K"
    using phi_data(2) unfolding bounded_iff by blast
  have center_phi_measurable:
      "slp_center_average tau phi \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF phi_integrable])
  have center_phi_bound:
      "\<And>x. Real_Vector_Spaces.norm (slp_center_average tau phi x) \<le>
        Real_Vector_Spaces.norm (of_real (tau / pi) :: complex) *
          integral\<^sup>L lborel (\<lambda>z. Real_Vector_Spaces.norm (phi z))"
    by (rule slp_center_average_fixed_tau_bound)
  have cauchy_unit_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite potential cutoff potential
          ?terminal (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_right_branch_complex_amplitude_finite_cauchy_integrable_lp_root[
        where B = B and C = C and p = p and X = X and root_weight = potential
          and cutoff = cutoff and potential = potential
          and orientation = orientation,
        OF B_nonnegative potential_support cutoff_support potential_support
          p_lower p_upper X_measurable X_bounded cutoff_measurable
          potential_lp potential_lp potential_outside cutoff_bound
          C_nonnegative])
  have terminal_base_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite potential cutoff potential
          ?terminal phi ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_right_branch_complex_amplitude_finite_bounded_output_integrable[
        OF cauchy_unit_amplitude_integrable phi_measurable phi_bound])
  have terminal_center_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite potential cutoff potential
          ?terminal (slp_center_average tau phi) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_right_branch_complex_amplitude_finite_bounded_output_integrable[
        OF cauchy_unit_amplitude_integrable center_phi_measurable
          center_phi_bound])
  have unit_base_source_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite potential cutoff potential
          (\<lambda>_. 1) ?source ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_right_branch_complex_amplitude_finite_unit_terminal_l2_integrable[
        where B = B and C = C and p = p and X = X and cutoff = cutoff
          and potential = potential and output_factor = ?source,
        OF B_nonnegative cutoff_support potential_support p_lower p_upper
          X_measurable X_bounded potential_lp potential_outside
          cutoff_measurable cutoff_bound C_nonnegative source_l2])
  have unit_center_source_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite potential cutoff potential
          (\<lambda>_. 1) (slp_center_average tau ?source) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_right_branch_complex_amplitude_finite_unit_terminal_l2_integrable[
        where B = B and C = C and p = p and X = X and cutoff = cutoff
          and potential = potential
          and output_factor = "slp_center_average tau ?source",
        OF B_nonnegative cutoff_support potential_support p_lower p_upper
          X_measurable X_bounded potential_lp potential_outside
          cutoff_measurable cutoff_bound C_nonnegative center_source_l2])
  show ?thesis
    by (rule
      slp_right_branch_finite_cancellation_model_eq_evaluated_pair[
        OF terminal_center_amplitude_integrable
          terminal_base_amplitude_integrable
          unit_center_source_amplitude_integrable
          unit_base_source_amplitude_integrable])
qed

end

end
