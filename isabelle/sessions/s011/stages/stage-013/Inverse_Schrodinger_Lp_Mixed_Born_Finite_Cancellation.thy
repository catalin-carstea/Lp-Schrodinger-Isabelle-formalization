theory Inverse_Schrodinger_Lp_Mixed_Born_Finite_Cancellation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Born_Conditional_Cancellation"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Center_Average_Smooth_Convergence"
begin

section \<open>Mixed Born cancellation on the existing finite carriers\<close>

context slp_mixed_center_error_hls_plancherel
begin

theorem slp_mixed_born_functional_finite_cancellation:
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
  shows "((\<lambda>tau. slp_mixed_born_functional CARD('i) CARD('j)
      tau phi Q cutoff q qt lo ro) \<longlongrightarrow> 0) at_top"
  by (rule slp_mixed_born_functional_tendsto_zero[OF
      p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
      cutoff_q cutoff_qt Q_in phi_test stationary_phase density
      slp_center_average_smooth_uniform_limit[OF phi_test]])

end

end
