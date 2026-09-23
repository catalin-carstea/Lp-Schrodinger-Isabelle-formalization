theory Inverse_Schrodinger_Lp_Left_Born_Finite_Decay_Hormander
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Born_Finite_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Center_Error_L2_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Left_One_Sided_Finite_L2_Error_Positive_Tail"
begin

section \<open>Finite left Born decay from the physical strong L2 theory\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_born_functional_finite_decay_hormander:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and cutoff potential phi :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes fourier_plancherel:
      "hormander_euclidean_l2_fourier_plancherel_claim"
    and stationary_phase:
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
  shows
    "((\<lambda>tau.
        slp_left_born_functional CARD('i) tau phi potential cutoff potential
          orientation)
      \<longlongrightarrow> 0) at_top"
proof -
  interpret hf: hormander_euclidean_l2_fourier_plancherel
    by standard (rule fourier_plancherel)
  let ?terminal = "slp_cauchy_transform orientation potential"
  let ?source = "\<lambda>u. phi u * ?terminal u"
  let ?model = "\<lambda>tau.
    slp_left_branch_finite_cancellation_model_v2 TYPE('i) tau potential
      cutoff potential ?terminal phi"
  have source_integrable: "integrable lborel ?source"
    by (rule slp_test_cauchy_product_integrable[OF
          p_lower p_upper potential_lp phi_test])
  have source_l2: "aim_complex_lp_on_plane 2 ?source"
    by (rule slp_test_cauchy_product_l2[OF
          p_lower p_upper potential_lp phi_test])
  have center_source_l2:
      "aim_complex_lp_on_plane 2 (slp_center_average tau ?source)"
    if tau_positive: "0 < tau" for tau
    by (rule hf.slp_center_average_l2_l1_l2[OF
          tau_positive source_integrable source_l2])
  have center_source_error_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm
            (slp_center_average tau ?source x - ?source x)) ^ 2
          \<partial>lborel) \<longlongrightarrow> 0) at_top"
    by (rule hf.slp_center_average_error_square_nn_integral_tendsto_zero[OF
          source_integrable source_l2])
  have l2_error_decay:
      "((\<lambda>tau.
          slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
            cutoff potential (\<lambda>_. 1)
            (\<lambda>output.
              slp_center_average tau ?source output - ?source output))
        \<longlongrightarrow> 0) at_top"
    by (rule
        slp_left_branch_finite_oscillatory_center_average_l2_error_decay_positive_tail[
          where B = B and C = C and p = p and X = X,
          OF B_nonnegative p_lower p_upper X_measurable X_bounded
            potential_lp potential_outside cutoff_measurable cutoff_bound
            C_nonnegative cutoff_support potential_support source_l2
            center_source_l2 center_source_error_decay])
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have principal_decay:
      "((\<lambda>tau. slp_left_branch_principal_finite_integral TYPE('i) tau
          potential cutoff potential ?terminal phi)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_left_branch_principal_finite_integral_cauchy_decay[
          where B = B and C = C and p = p and X = X,
          OF stationary_phase density B_nonnegative p_lower p_upper
            X_measurable X_bounded potential_lp potential_outside
            cutoff_measurable cutoff_bound C_nonnegative cutoff_support
            potential_support phi_test])
  have smooth_error_decay:
      "((\<lambda>tau.
          slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
            cutoff potential ?terminal
            (\<lambda>output. slp_center_average tau phi output - phi output))
        \<longlongrightarrow> 0) at_top"
    by (rule
        slp_left_branch_finite_oscillatory_center_average_error_decay[
          where B = B and C = C and p = p and X = X,
          OF B_nonnegative p_lower p_upper X_measurable X_bounded
            potential_lp potential_outside cutoff_measurable cutoff_bound
            C_nonnegative cutoff_support potential_support phi_integrable
            uniform_convergence])
  have principal_and_smooth_decay:
      "((\<lambda>tau.
          slp_left_branch_principal_finite_integral TYPE('i) tau potential
              cutoff potential ?terminal phi +
            slp_left_branch_finite_oscillatory_integral TYPE('i) tau
              potential cutoff potential ?terminal
                (\<lambda>output.
                  slp_center_average tau phi output - phi output))
        \<longlongrightarrow> 0 + 0) at_top"
    by (rule tendsto_add[OF principal_decay smooth_error_decay])
  have combined_decay:
      "((\<lambda>tau.
          (slp_left_branch_principal_finite_integral TYPE('i) tau potential
              cutoff potential ?terminal phi +
            slp_left_branch_finite_oscillatory_integral TYPE('i) tau
              potential cutoff potential ?terminal
                (\<lambda>output.
                  slp_center_average tau phi output - phi output)) -
            slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
              cutoff potential (\<lambda>_. 1)
                (\<lambda>output.
                  slp_center_average tau ?source output - ?source output))
        \<longlongrightarrow> (0 + 0) - 0) at_top"
    by (rule tendsto_diff[OF principal_and_smooth_decay l2_error_decay])
  have model_decay: "(?model \<longlongrightarrow> 0) at_top"
    using combined_decay
    unfolding slp_left_branch_finite_cancellation_model_v2_def
    by simp
  have tau_positive:
      "eventually (\<lambda>tau :: real. 0 < tau) at_top"
    by simp
  have eventual_born_eq:
      "eventually (\<lambda>tau.
        slp_left_born_functional CARD('i) tau phi potential cutoff potential
            orientation = ?model tau) at_top"
    using tau_positive
  proof eventually_elim
    fix tau :: real
    assume tau: "0 < tau"
    show
      "slp_left_born_functional CARD('i) tau phi potential cutoff potential
          orientation = ?model tau"
      by (rule slp_left_born_functional_eq_finite_cancellation_model_v2[
            where B = B and C = C and p = p and X = X,
            OF B_nonnegative cutoff_support potential_support p_lower p_upper
              X_measurable X_bounded potential_lp potential_outside
              cutoff_measurable cutoff_bound C_nonnegative phi_test source_l2
              center_source_l2[OF tau]])
  qed
  from model_decay show ?thesis
    by (rule tendsto_cong[OF eventual_born_eq, THEN iffD2])
qed

end

end
