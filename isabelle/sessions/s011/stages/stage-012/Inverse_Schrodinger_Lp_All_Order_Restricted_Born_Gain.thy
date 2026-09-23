theory Inverse_Schrodinger_Lp_All_Order_Restricted_Born_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Bounded_Support_Lp_Norm"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Recursive_Born_Uniform_Gain"
begin

hide_const (open) Commutative_Ring.norm

section \<open>One restricted Ls gain for zero and positive Born orders\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

lemma slp_zero_born_branches_restricted_gain:
  fixes cutoff :: slp_scalar_field and Y :: "slp_point set"
  assumes s_lower: "2 < s" and target_bounded: "bounded Y"
    and target_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau c q. 2 \<le> tau \<longrightarrow>
    aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_left_recursive_branch 0 tau c cutoff q (\<lambda>_. 1))) \<and>
    aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_right_recursive_branch 0 tau c cutoff q (\<lambda>_. 1))) \<and>
    aim_complex_lp_norm s
      (slp_restrict_field Y (slp_left_recursive_branch 0 tau c cutoff q (\<lambda>_. 1)))
        \<le> C * inverse (sqrt tau) \<and>
    aim_complex_lp_norm s
      (slp_restrict_field Y (slp_right_recursive_branch 0 tau c cutoff q (\<lambda>_. 1)))
        \<le> C * inverse (sqrt tau))"
proof -
  have s_positive: "0 < s" using s_lower by linarith
  obtain H::real where H_positive: "0 < H"
    and raw_gain: "\<And>tau c f epsilon orientation.
      2 \<le> tau \<Longrightarrow> slp_test_function_on Y f \<Longrightarrow>
      epsilon \<in> {-1, 1} \<Longrightarrow>
      aim_complex_lp_on_plane s
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation (epsilon * tau) c f)) \<and>
      aim_complex_lp_norm s
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation (epsilon * tau) c f))
        \<le> H * inverse (sqrt tau) *
          slp_w1p_norm_on (slp_hls_source_exponent s) UNIV f (slp_classical_gradient f)"
    using slp_uniform_terminal_w1p_gain_plane[OF s_lower target_bounded] by blast
  let ?W = "slp_w1p_norm_on (slp_hls_source_exponent s) UNIV cutoff
    (slp_classical_gradient cutoff)"
  let ?C = "H * (abs ?W + 1)"
  have factor_positive: "0 < abs ?W + 1" by simp
  have C_positive: "0 < ?C"
    by (rule mult_pos_pos[OF H_positive factor_positive])
  have W_bound: "?W \<le> abs ?W + 1"
    using abs_ge_self[of ?W] by linarith
  have restricted_gain:
      "aim_complex_lp_on_plane s
        (slp_restrict_field Y (slp_cauchy_transform orientation
          (slp_oscillatory_modulation tau c cutoff))) \<and>
      aim_complex_lp_norm s
        (slp_restrict_field Y (slp_cauchy_transform orientation
          (slp_oscillatory_modulation tau c cutoff))) \<le> ?C * inverse (sqrt tau)"
    if tau_lower: "2 \<le> tau"
    for tau :: real and c :: slp_point and orientation :: slp_cauchy_orientation
  proof -
    let ?T = "slp_cauchy_transform orientation (slp_oscillatory_modulation tau c cutoff)"
    have sign: "(1::real) \<in> {-1, 1}" by simp
    have global_data: "aim_complex_lp_on_plane s ?T \<and>
        aim_complex_lp_norm s ?T \<le> H * inverse (sqrt tau) * ?W"
      using raw_gain[OF tau_lower cutoff_test sign]
      by (simp only: mult.left_neutral)
    have global_lp: "aim_complex_lp_on_plane s ?T"
      by (rule conjunct1[OF global_data])
    have local_lp: "aim_complex_lp_on_plane s (slp_restrict_field Y ?T)"
      by (rule slp_restriction_lp_norm_contraction(1)[OF
          s_positive target_measurable global_lp])
    have local_le: "aim_complex_lp_norm s (slp_restrict_field Y ?T) \<le>
        aim_complex_lp_norm s ?T"
      by (rule slp_restriction_lp_norm_contraction(2)[OF
          s_positive target_measurable global_lp])
    have scale_nonnegative: "0 \<le> H * inverse (sqrt tau)"
      using H_positive tau_lower by (intro mult_nonneg_nonneg) auto
    have scale_bound: "H * inverse (sqrt tau) * ?W \<le> ?C * inverse (sqrt tau)"
      using mult_left_mono[OF W_bound scale_nonnegative]
      by (simp only: mult.assoc mult.left_commute mult.commute)
    have local_bound: "aim_complex_lp_norm s (slp_restrict_field Y ?T)
        \<le> ?C * inverse (sqrt tau)"
      by (rule order_trans[OF local_le],
          rule order_trans[OF conjunct2[OF global_data] scale_bound])
    show ?thesis by (rule conjI[OF local_lp local_bound])
  qed
  have all: "\<forall>tau c q. 2 \<le> tau \<longrightarrow>
    aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_left_recursive_branch 0 tau c cutoff q (\<lambda>_. 1))) \<and>
    aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_right_recursive_branch 0 tau c cutoff q (\<lambda>_. 1))) \<and>
    aim_complex_lp_norm s
      (slp_restrict_field Y (slp_left_recursive_branch 0 tau c cutoff q (\<lambda>_. 1)))
        \<le> ?C * inverse (sqrt tau) \<and>
    aim_complex_lp_norm s
      (slp_restrict_field Y (slp_right_recursive_branch 0 tau c cutoff q (\<lambda>_. 1)))
        \<le> ?C * inverse (sqrt tau)"
  proof (intro allI impI)
    fix tau :: real and c :: slp_point and q :: slp_scalar_field
    assume tau_lower: "2 \<le> tau"
    have left: "slp_left_recursive_branch 0 tau c cutoff q (\<lambda>_. 1) =
        slp_cauchy_transform SLP_Partial_Inverse (slp_oscillatory_modulation tau c cutoff)"
      by (simp add: slp_partial_psi_inverse_def)
    have right: "slp_right_recursive_branch 0 tau c cutoff q (\<lambda>_. 1) =
        slp_cauchy_transform SLP_Dbar_Inverse (slp_oscillatory_modulation tau c cutoff)"
      by (simp add: slp_dbar_psi_inverse_def)
    have left_gain: "aim_complex_lp_on_plane s
        (slp_restrict_field Y (slp_cauchy_transform SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c cutoff))) \<and>
      aim_complex_lp_norm s
        (slp_restrict_field Y (slp_cauchy_transform SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c cutoff))) \<le> ?C * inverse (sqrt tau)"
      by (rule restricted_gain[OF tau_lower])
    have right_gain: "aim_complex_lp_on_plane s
        (slp_restrict_field Y (slp_cauchy_transform SLP_Dbar_Inverse
          (slp_oscillatory_modulation tau c cutoff))) \<and>
      aim_complex_lp_norm s
        (slp_restrict_field Y (slp_cauchy_transform SLP_Dbar_Inverse
          (slp_oscillatory_modulation tau c cutoff))) \<le> ?C * inverse (sqrt tau)"
      by (rule restricted_gain[OF tau_lower])
    show "aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_left_recursive_branch 0 tau c cutoff q (\<lambda>_. 1))) \<and>
      aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_right_recursive_branch 0 tau c cutoff q (\<lambda>_. 1))) \<and>
      aim_complex_lp_norm s
      (slp_restrict_field Y (slp_left_recursive_branch 0 tau c cutoff q (\<lambda>_. 1)))
        \<le> ?C * inverse (sqrt tau) \<and>
      aim_complex_lp_norm s
      (slp_restrict_field Y (slp_right_recursive_branch 0 tau c cutoff q (\<lambda>_. 1)))
        \<le> ?C * inverse (sqrt tau)"
      unfolding left right using left_gain right_gain by blast
  qed
  show ?thesis by (rule exI[of _ ?C], rule conjI[OF C_positive all])
qed

lemma slp_positive_born_branches_restricted_gain:
  fixes cutoff :: slp_scalar_field and Y :: "slp_point set" and m :: nat
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and s_positive: "0 < s" and target_bounded: "bounded Y"
    and target_measurable: "Y \<in> sets lborel"
    and order_positive: "0 < m" and cutoff_test: "slp_test_function_on Y cutoff"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau c q.
    2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      (\<forall>x. cutoff x * q x = q x) \<longrightarrow>
    aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1))) \<and>
    aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1))) \<and>
    aim_complex_lp_norm s
      (slp_restrict_field Y (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1)))
        \<le> C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m \<and>
    aim_complex_lp_norm s
      (slp_restrict_field Y (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1)))
        \<le> C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m)"
proof -
  have auxiliary_lower:
      "2 * slp_holder_conjugate p < 2 * slp_holder_conjugate p + 1" by simp
  obtain H::real where H_positive: "0 < H"
    and H_gain: "\<And>tau c q. 2 \<le> tau \<Longrightarrow>
      aim_complex_lp_on_plane p q \<Longrightarrow> (\<forall>x. cutoff x * q x = q x) \<Longrightarrow>
      slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel \<and>
      slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) z)
        \<le> H * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m \<and>
        norm (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) z)
        \<le> H * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m)"
    using slp_positive_born_branches_uniform_gain[OF p_lower p_upper
        auxiliary_lower target_bounded order_positive cutoff_test] by blast
  let ?V = "measure lborel Y powr (1 / s)"
  let ?C = "H * (?V + 1)"
  have V_nonnegative: "0 \<le> ?V" by simp
  have factor_positive: "0 < ?V + 1" using V_nonnegative by linarith
  have C_positive: "0 < ?C"
    by (rule mult_pos_pos[OF H_positive factor_positive])
  have V_bound: "?V \<le> ?V + 1" by simp
  have restricted_gain:
      "aim_complex_lp_on_plane s (slp_restrict_field Y F) \<and>
        aim_complex_lp_norm s (slp_restrict_field Y F)
          \<le> ?C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
    if tau_lower: "2 \<le> tau"
      and field_measurable: "F \<in> borel_measurable lborel"
      and local_bound: "\<And>x. x \<in> Y \<Longrightarrow> norm (F x) \<le>
        H * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
    for tau :: real and q F :: slp_scalar_field
  proof -
    let ?A = "H * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
    have power_nonnegative: "0 \<le> (aim_complex_lp_norm p q)^m"
      by (rule zero_le_power) (simp add: aim_complex_lp_norm_def)
    have A_nonnegative: "0 \<le> ?A"
      using H_positive tau_lower power_nonnegative
      by (intro mult_nonneg_nonneg) auto
    have local_lp: "aim_complex_lp_on_plane s (slp_restrict_field Y F)"
      by (rule slp_bounded_restriction_lp_norm(1)[OF s_positive
          target_measurable target_bounded field_measurable A_nonnegative local_bound])
    have volume_bound: "aim_complex_lp_norm s (slp_restrict_field Y F) \<le> ?A * ?V"
      by (rule slp_bounded_restriction_lp_norm(2)[OF s_positive
          target_measurable target_bounded field_measurable A_nonnegative local_bound])
    have constant_bound: "?A * ?V \<le>
        ?C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
      using mult_left_mono[OF V_bound A_nonnegative]
      by (simp only: mult.assoc mult.left_commute mult.commute)
    have norm_bound: "aim_complex_lp_norm s (slp_restrict_field Y F) \<le>
        ?C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
      by (rule order_trans[OF volume_bound constant_bound])
    show ?thesis by (rule conjI[OF local_lp norm_bound])
  qed
  have all: "\<forall>tau c q.
    2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      (\<forall>x. cutoff x * q x = q x) \<longrightarrow>
    aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1))) \<and>
    aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1))) \<and>
    aim_complex_lp_norm s
      (slp_restrict_field Y (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1)))
        \<le> ?C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m \<and>
    aim_complex_lp_norm s
      (slp_restrict_field Y (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1)))
        \<le> ?C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
  proof (intro allI impI)
    fix tau :: real and c :: slp_point and q :: slp_scalar_field
    assume hypotheses: "2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      (\<forall>x. cutoff x * q x = q x)"
    have tau_lower: "2 \<le> tau" by (rule conjunct1[OF hypotheses])
    note rest = hypotheses[THEN conjunct2]
    have q_lp: "aim_complex_lp_on_plane p q" by (rule conjunct1[OF rest])
    have cutoff_identity: "\<forall>x. cutoff x * q x = q x"
      by (rule conjunct2[OF rest])
    note data = H_gain[OF tau_lower q_lp cutoff_identity, of c]
    have left_measurable:
        "slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel"
      by (rule conjunct1[OF data])
    note data_rest = data[THEN conjunct2]
    have right_measurable:
        "slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel"
      by (rule conjunct1[OF data_rest])
    note bounds = data_rest[THEN conjunct2]
    have left_bound: "norm (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) x)
        \<le> H * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
      if "x \<in> Y" for x
      by (rule conjunct1[OF bounds[rule_format, OF that]])
    have right_bound: "norm (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) x)
        \<le> H * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
      if "x \<in> Y" for x
      by (rule conjunct2[OF bounds[rule_format, OF that]])
    have left: "aim_complex_lp_on_plane s
        (slp_restrict_field Y (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1))) \<and>
      aim_complex_lp_norm s
        (slp_restrict_field Y (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1)))
        \<le> ?C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
      by (rule restricted_gain[OF tau_lower left_measurable left_bound])
    have right: "aim_complex_lp_on_plane s
        (slp_restrict_field Y (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1))) \<and>
      aim_complex_lp_norm s
        (slp_restrict_field Y (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1)))
        \<le> ?C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
      by (rule restricted_gain[OF tau_lower right_measurable right_bound])
    show "aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1))) \<and>
      aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1))) \<and>
      aim_complex_lp_norm s
      (slp_restrict_field Y (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1)))
        \<le> ?C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m \<and>
      aim_complex_lp_norm s
      (slp_restrict_field Y (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1)))
        \<le> ?C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
      using left right by blast
  qed
  show ?thesis by (rule exI[of _ ?C], rule conjI[OF C_positive all])
qed

theorem slp_all_order_born_branches_restricted_gain:
  fixes cutoff :: slp_scalar_field and Y :: "slp_point set" and m :: nat
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and s_lower: "2 < s" and target_bounded: "bounded Y"
    and target_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau c q.
    2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      (\<forall>x. cutoff x * q x = q x) \<longrightarrow>
    aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1))) \<and>
    aim_complex_lp_on_plane s
      (slp_restrict_field Y (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1))) \<and>
    aim_complex_lp_norm s
      (slp_restrict_field Y (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1)))
        \<le> C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m \<and>
    aim_complex_lp_norm s
      (slp_restrict_field Y (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1)))
        \<le> C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m)"
proof (cases "m = 0")
  case True
  show ?thesis
    using slp_zero_born_branches_restricted_gain[OF s_lower target_bounded
      target_measurable cutoff_test]
    by (simp only: True power_0 mult.right_neutral) blast
next
  case False
  have order_positive: "0 < m" using False by simp
  have s_positive: "0 < s" using s_lower by linarith
  show ?thesis
    by (rule slp_positive_born_branches_restricted_gain[OF p_lower p_upper
        s_positive target_bounded target_measurable order_positive cutoff_test])
qed

end

end
