theory Inverse_Schrodinger_Lp_Left_Born_Finite_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Born_Finite_Cancellation_V2"
begin

section \<open>Decay of each finite left Born term\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_born_functional_finite_decay:
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
    "((\<lambda>tau.
        slp_left_born_functional CARD('i) tau phi potential cutoff potential
          orientation)
      \<longlongrightarrow> 0) at_top"
proof -
  let ?terminal = "slp_cauchy_transform orientation potential"
  have born_eq_cancellation:
      "(\<lambda>tau.
          slp_left_born_functional CARD('i) tau phi potential cutoff potential
            orientation) =
        (\<lambda>tau.
          slp_left_branch_finite_cancellation_model_v2 TYPE('i) tau potential
            cutoff potential ?terminal phi)"
  proof (rule ext)
    fix tau :: real
    show
      "slp_left_born_functional CARD('i) tau phi potential cutoff potential
          orientation =
        slp_left_branch_finite_cancellation_model_v2 TYPE('i) tau potential
          cutoff potential ?terminal phi"
      by (rule slp_left_born_functional_eq_finite_cancellation_model_v2[
            where B = B and C = C and p = p and X = X,
            OF B_nonnegative cutoff_support potential_support p_lower p_upper
              X_measurable X_bounded potential_lp potential_outside
              cutoff_measurable cutoff_bound C_nonnegative phi_test source_l2
              center_average_l2])
  qed
  have cancellation_decay:
      "((\<lambda>tau.
          slp_left_branch_finite_cancellation_model_v2 TYPE('i) tau potential
            cutoff potential ?terminal phi)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_left_branch_finite_cancellation_model_v2_decay[
          where B = B and C = C and p = p and X = X,
          OF stationary_phase density B_nonnegative p_lower p_upper
            X_measurable X_bounded potential_lp potential_outside
            cutoff_measurable cutoff_bound C_nonnegative cutoff_support
            potential_support phi_test uniform_convergence source_l2
            center_average_l2 center_average_error_square_decay])
  show ?thesis
    unfolding born_eq_cancellation
    by (rule cancellation_decay)
qed

end

end
