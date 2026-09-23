theory Inverse_Schrodinger_Lp_Mixed_Born_Conditional_Cancellation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Born_Bracket_Identity"
begin

section \<open>Conditional cancellation of the original mixed Born functional\<close>

context slp_mixed_center_error_hls_plancherel
begin

theorem slp_mixed_born_functional_tendsto_zero:
  fixes active_type ::
      "((unit + (((('i::finite) + 'i) + unit) + (('j::finite) + 'j))) \<times> bool) itself"
    and p :: real and Y :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and Y_bounded: "bounded Y" and Y_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
    and phi_test: "slp_test_function_on UNIV phi"

    and stationary_phase: "hormander_quadratic_stationary_phase_decay_claim active_type"
    and density: "evans_compact_smooth_l1_density_claim active_type"
    and smooth_uniform:
      "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi at_top"
  shows "((\<lambda>tau. slp_mixed_born_functional CARD('i) CARD('j)
      tau phi Q cutoff q qt lo ro) \<longlongrightarrow> 0) at_top"
proof -
  interpret mixed_hls: aim_planar_riesz_hls_cauchy by unfold_locales
  have identity:
    "slp_mixed_born_functional CARD('i) CARD('j) tau phi Q cutoff q qt lo ro =
      integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
    for tau
    by (rule mixed_hls.slp_mixed_born_functional_eq_bracket(1)[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in phi_test])
  have limit:
    "((\<lambda>tau. integral\<^sup>L lborel
      (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_mixed_cauchy_bracket_tendsto_zero[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in phi_test stationary_phase density smooth_uniform])
  show ?thesis using limit by (simp only: identity)
qed


end

end
