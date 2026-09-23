theory Inverse_Schrodinger_Lp_Common_CGO_Finite_Born_Family_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Born_Cancellation"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Born_Cancellation"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Born_Cancellation"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Finite Born-family decay for physical-domain-supported coefficients\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_common_cgo_finite_born_families_tendsto_zero:
  fixes N M :: nat and p :: real
    and Omega X :: "slp_point set"
    and phi cutoff q qt Q :: slp_scalar_field
  assumes stationary:
      "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and fourier_plancherel:
      "hormander_euclidean_l2_fourier_plancherel_claim"
    and exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_bounded: "bounded X"
    and X_measurable: "X \<in> sets lborel"
    and Omega_subset: "Omega \<subseteq> X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and cutoff_one: "\<And>x. x \<in> Omega \<Longrightarrow> cutoff x = 1"
    and q_lp: "aim_complex_lp_on_plane p q"
    and q_support: "{x. q x \<noteq> 0} \<subseteq> Omega"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and qt_support: "{x. qt x \<noteq> 0} \<subseteq> Omega"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_support: "{x. Q x \<noteq> 0} \<subseteq> Omega"
    and phi_test: "slp_test_function_on Omega phi"
  shows
    "((\<lambda>tau. \<Sum>j<N.
        slp_left_born_functional j tau phi Q cutoff q
          SLP_Dbar_Inverse) \<longlongrightarrow> 0) at_top
    \<and> ((\<lambda>tau. \<Sum>k<M.
        slp_right_born_functional k tau phi Q cutoff qt
          SLP_Partial_Inverse) \<longlongrightarrow> 0) at_top
    \<and> ((\<lambda>tau. \<Sum>j<N. \<Sum>k<M.
        slp_mixed_born_functional j k tau phi Q cutoff q qt
          SLP_Dbar_Inverse SLP_Partial_Inverse) \<longlongrightarrow> 0) at_top"
proof -
  have cutoff_q: "\<forall>x. cutoff x * q x = q x"
  proof
    fix x
    show "cutoff x * q x = q x"
    proof (cases "q x = 0")
      case True
      then show ?thesis by simp
    next
      case False
      then have x_in: "x \<in> Omega" using q_support by blast
      show ?thesis by (simp add: cutoff_one[OF x_in])
    qed
  qed
  have cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
  proof
    fix x
    show "cutoff x * qt x = qt x"
    proof (cases "qt x = 0")
      case True
      then show ?thesis by simp
    next
      case False
      then have x_in: "x \<in> Omega" using qt_support by blast
      show ?thesis by (simp add: cutoff_one[OF x_in])
    qed
  qed
  have Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> X"
    using Q_support Omega_subset by blast
  have phi_test_UNIV: "slp_test_function_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast

  have left_term:
      "((\<lambda>tau. slp_left_born_functional j tau phi Q cutoff q
          SLP_Dbar_Inverse) \<longlongrightarrow> 0) at_top" for j
    by (rule slp_left_born_functional_natural_cancellation[
          OF stationary density fourier_plancherel exponent_lower
            exponent_upper X_bounded X_measurable cutoff_test q_lp Q_lp
            cutoff_q Q_in phi_test_UNIV])
  have left_limit:
      "((\<lambda>tau. \<Sum>j<N.
          slp_left_born_functional j tau phi Q cutoff q
            SLP_Dbar_Inverse) \<longlongrightarrow> 0) at_top"
  proof -
    have
      "((\<lambda>tau. \<Sum>j<N.
          slp_left_born_functional j tau phi Q cutoff q
            SLP_Dbar_Inverse) \<longlongrightarrow> (\<Sum>j<N. 0)) at_top"
      by (rule tendsto_sum) (use left_term in blast)
    then show ?thesis by simp
  qed

  have right_term:
      "((\<lambda>tau. slp_right_born_functional k tau phi Q cutoff qt
          SLP_Partial_Inverse) \<longlongrightarrow> 0) at_top" for k
    by (rule slp_right_born_functional_natural_cancellation[
          OF stationary density fourier_plancherel exponent_lower
            exponent_upper X_bounded X_measurable cutoff_test qt_lp Q_lp
            cutoff_qt Q_in phi_test_UNIV])
  have right_limit:
      "((\<lambda>tau. \<Sum>k<M.
          slp_right_born_functional k tau phi Q cutoff qt
            SLP_Partial_Inverse) \<longlongrightarrow> 0) at_top"
  proof -
    have
      "((\<lambda>tau. \<Sum>k<M.
          slp_right_born_functional k tau phi Q cutoff qt
            SLP_Partial_Inverse) \<longlongrightarrow> (\<Sum>k<M. 0)) at_top"
      by (rule tendsto_sum) (use right_term in blast)
    then show ?thesis by simp
  qed

  have mixed_term:
      "((\<lambda>tau. slp_mixed_born_functional j k tau phi Q cutoff q qt
          SLP_Dbar_Inverse SLP_Partial_Inverse) \<longlongrightarrow> 0) at_top"
    for j k
    by (rule slp_mixed_born_functional_natural_cancellation[
          OF stationary density fourier_plancherel exponent_lower
            exponent_upper X_bounded X_measurable cutoff_test q_lp qt_lp
            Q_lp cutoff_q cutoff_qt Q_in phi_test_UNIV])
  have mixed_inner:
      "((\<lambda>tau. \<Sum>k<M.
          slp_mixed_born_functional j k tau phi Q cutoff q qt
            SLP_Dbar_Inverse SLP_Partial_Inverse) \<longlongrightarrow> 0) at_top"
    for j
  proof -
    have
      "((\<lambda>tau. \<Sum>k<M.
          slp_mixed_born_functional j k tau phi Q cutoff q qt
            SLP_Dbar_Inverse SLP_Partial_Inverse) \<longlongrightarrow>
        (\<Sum>k<M. 0)) at_top"
      by (rule tendsto_sum) (use mixed_term in blast)
    then show ?thesis by simp
  qed
  have mixed_limit:
      "((\<lambda>tau. \<Sum>j<N. \<Sum>k<M.
          slp_mixed_born_functional j k tau phi Q cutoff q qt
            SLP_Dbar_Inverse SLP_Partial_Inverse) \<longlongrightarrow> 0) at_top"
  proof -
    have
      "((\<lambda>tau. \<Sum>j<N. \<Sum>k<M.
          slp_mixed_born_functional j k tau phi Q cutoff q qt
            SLP_Dbar_Inverse SLP_Partial_Inverse) \<longlongrightarrow>
        (\<Sum>j<N. 0)) at_top"
      by (rule tendsto_sum) (use mixed_inner in blast)
    then show ?thesis by simp
  qed

  show ?thesis using left_limit right_limit mixed_limit by blast
qed

end

end
