theory Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Cancellation_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Principal_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Smooth_Error_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_One_Sided_Finite_L2_Error_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Cancellation_Amplitude_Discharge"
begin

section \<open>Decay of the physical direct right finite cancellation model\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_branch_finite_cancellation_model_decay:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and cutoff potential phi :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and B_nonnegative: "0 \<le> B"
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
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and phi_test: "slp_test_function_on UNIV phi"
    and uniform_convergence:
      "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi at_top"
    and source_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)"
    and center_average_l2:
      "\<And>tau. aim_complex_lp_on_plane 2
        (slp_center_average tau
          (\<lambda>u. phi u * slp_cauchy_transform orientation potential u))"
    and center_average_error_square_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm
            (slp_center_average tau
                (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)
                x -
              phi x * slp_cauchy_transform orientation potential x)) ^ 2
          \<partial>lborel) \<longlongrightarrow> 0) at_top"
  shows
    "((\<lambda>tau. slp_right_branch_finite_cancellation_model TYPE('i) tau
        potential cutoff potential
          (slp_cauchy_transform orientation potential) phi)
      \<longlongrightarrow> 0) at_top"
proof -
  let ?terminal = "slp_cauchy_transform orientation potential"
  let ?source = "\<lambda>u. phi u * ?terminal u"
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_measurable:
      "?terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper potential_lp])
  note phi_data = slp_test_function_integrable_bounded[OF phi_test]
  have phi_integrable: "integrable lborel phi"
    by (rule phi_data(1))
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  obtain K where phi_bound:
      "\<And>x. Real_Vector_Spaces.norm (phi x) \<le> K"
    using phi_data(2) unfolding bounded_iff by blast
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
  have terminal_test_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite potential cutoff potential
          ?terminal phi ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_right_branch_complex_amplitude_finite_bounded_output_integrable[
        OF cauchy_unit_amplitude_integrable phi_measurable phi_bound])
  have unit_source_amplitude_integrable:
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
  have principal_decay:
      "((\<lambda>tau. slp_right_branch_principal_finite_integral TYPE('i) tau
          potential cutoff potential ?terminal phi)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_right_branch_principal_finite_integral_decay[OF
          stationary_phase density potential_measurable cutoff_measurable
          potential_measurable terminal_measurable phi_measurable
          terminal_test_amplitude_integrable unit_source_amplitude_integrable])
  have smooth_error_decay:
      "((\<lambda>tau.
          slp_right_branch_finite_oscillatory_integral TYPE('i) tau potential
            cutoff potential ?terminal
            (\<lambda>output. slp_center_average tau phi output - phi output))
        \<longlongrightarrow> 0) at_top"
    by (rule
      slp_right_branch_finite_oscillatory_center_average_error_decay[
        where B = B and C = C and p = p and X = X,
        OF B_nonnegative p_lower p_upper X_measurable X_bounded potential_lp
          potential_outside cutoff_measurable cutoff_bound C_nonnegative
          cutoff_support potential_support phi_integrable uniform_convergence])
  have l2_error_decay:
      "((\<lambda>tau.
          slp_right_branch_finite_oscillatory_integral TYPE('i) tau potential
            cutoff potential (\<lambda>_. 1)
            (\<lambda>output.
              slp_center_average tau ?source output - ?source output))
        \<longlongrightarrow> 0) at_top"
    by (rule
      slp_right_branch_finite_oscillatory_center_average_l2_error_decay_at_residual_frequency[
        where B = B and C = C and p = p and X = X,
        OF B_nonnegative p_lower p_upper X_measurable X_bounded potential_lp
          potential_outside cutoff_measurable cutoff_bound C_nonnegative
          cutoff_support potential_support source_l2 center_average_l2
          center_average_error_square_decay])
  have principal_and_smooth_decay:
      "((\<lambda>tau.
          slp_right_branch_principal_finite_integral TYPE('i) tau potential
              cutoff potential ?terminal phi +
            slp_right_branch_finite_oscillatory_integral TYPE('i) tau
              potential cutoff potential ?terminal
                (\<lambda>output.
                  slp_center_average tau phi output - phi output))
        \<longlongrightarrow> 0 + 0) at_top"
    by (rule tendsto_add[OF principal_decay smooth_error_decay])
  have combined_decay:
      "((\<lambda>tau.
          (slp_right_branch_principal_finite_integral TYPE('i) tau potential
              cutoff potential ?terminal phi +
            slp_right_branch_finite_oscillatory_integral TYPE('i) tau
              potential cutoff potential ?terminal
                (\<lambda>output.
                  slp_center_average tau phi output - phi output)) -
            slp_right_branch_finite_oscillatory_integral TYPE('i) tau
              potential cutoff potential (\<lambda>_. 1)
                (\<lambda>output.
                  slp_center_average tau ?source output - ?source output))
        \<longlongrightarrow> (0 + 0) - 0) at_top"
    by (rule tendsto_diff[OF principal_and_smooth_decay l2_error_decay])
  show ?thesis
    using combined_decay
    unfolding slp_right_branch_finite_cancellation_model_def
    by simp
qed

end

end
