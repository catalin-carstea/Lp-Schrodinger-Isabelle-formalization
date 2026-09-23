theory Inverse_Schrodinger_Lp_Qstar_Right_Zero_Positive_Tau_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Dbar_Psi_Quarter_Turn_Covariance"
begin

section \<open>Positive-parameter right zero-branch gain by quarter-turn transport\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_right_zero_positive_tau_compact_center_gain:
  fixes s :: real
    and cutoff terminal_value potential :: slp_scalar_field
    and Z :: "slp_point set"
  assumes s_lower: "2 < s"
    and product_test:
      "slp_test_function_on UNIV (\<lambda>x. cutoff x * terminal_value x)"
    and Z_compact: "compact Z"
  shows
    "\<exists>K R::real. 0 < K \<and> 0 < R \<and>
      (\<forall>c\<in>Z. \<forall>y.
        cutoff y * terminal_value y \<noteq> 0
        \<longrightarrow> norm_class.norm (y - c) \<le> R) \<and>
      (\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        aim_complex_lp_norm s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau))"
proof -
  let ?g = "\<lambda>x. cutoff x * terminal_value x"
  let ?gR = "\<lambda>x. ?g (- slp_quarter_turn x)"
  let ?RZ = "slp_quarter_turn ` Z"
  have gR_test: "slp_test_function_on UNIV ?gR"
    by (rule slp_test_function_on_inverse_quarter_turn[OF product_test])
  have RZ_compact: "compact ?RZ"
    by (rule slp_quarter_turn_compact_image[OF Z_compact])
  obtain K R::real where K_positive: "0 < K"
    and R_positive: "0 < R"
    and rotated_support:
      "\<forall>c\<in>?RZ. \<forall>y.
        ?gR y \<noteq> 0 \<longrightarrow> norm_class.norm (y - c) \<le> R"
    and rotated_terminal:
      "\<forall>tau c.
        2 \<le> tau \<and> c \<in> ?RZ
        \<longrightarrow>
        aim_complex_lp_on_plane s
          (slp_partial_psi_inverse tau c ?gR) \<and>
        aim_complex_lp_on_plane s
          (slp_dbar_psi_inverse tau c ?gR) \<and>
        aim_complex_lp_norm s
            (slp_partial_psi_inverse tau c ?gR)
          \<le> K * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s
            (slp_dbar_psi_inverse tau c ?gR)
          \<le> K * inverse (sqrt tau)"
    using slp_qstar_smooth_fixed_terminal_gain_on_compact_centers[
      OF s_lower gR_test RZ_compact] by blast
  have original_support:
      "\<forall>c\<in>Z. \<forall>y.
        ?g y \<noteq> 0 \<longrightarrow> norm_class.norm (y - c) \<le> R"
  proof (intro ballI allI impI)
    fix c y
    assume c_in: "c \<in> Z" and y_nonzero: "?g y \<noteq> 0"
    have Rc_in: "slp_quarter_turn c \<in> ?RZ"
      using c_in by blast
    have gR_Ry_nonzero: "?gR (slp_quarter_turn y) \<noteq> 0"
      using y_nonzero by simp
    have rotated_bound:
        "norm_class.norm
          (slp_quarter_turn y - slp_quarter_turn c) \<le> R"
      using rotated_support Rc_in gR_Ry_nonzero by blast
    have diff_rotation:
        "slp_quarter_turn (y - c) =
          slp_quarter_turn y - slp_quarter_turn c"
      by (rule linear_diff[OF slp_quarter_turn_linear])
    show "norm_class.norm (y - c) \<le> R"
      using rotated_bound
      by (simp only: diff_rotation[symmetric] slp_quarter_turn_norm)
  qed
  have terminal:
      "\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        aim_complex_lp_norm s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau)"
  proof (intro allI impI)
    fix tau :: real and c :: slp_point
    assume hypotheses: "2 \<le> tau \<and> c \<in> Z"
    then have tau_lower: "2 \<le> tau" and c_in: "c \<in> Z"
      by blast+
    have s_positive: "0 < s"
      using s_lower by linarith
    have Rc_in: "slp_quarter_turn c \<in> ?RZ"
      using c_in by blast
    have rotated_data:
        "aim_complex_lp_on_plane s
            (slp_partial_psi_inverse tau (slp_quarter_turn c) ?gR) \<and>
          aim_complex_lp_on_plane s
            (slp_dbar_psi_inverse tau (slp_quarter_turn c) ?gR) \<and>
          aim_complex_lp_norm s
              (slp_partial_psi_inverse tau (slp_quarter_turn c) ?gR)
            \<le> K * inverse (sqrt tau) \<and>
          aim_complex_lp_norm s
              (slp_dbar_psi_inverse tau (slp_quarter_turn c) ?gR)
            \<le> K * inverse (sqrt tau)"
      using rotated_terminal tau_lower Rc_in by blast
    have rotated_dbar_lp:
        "aim_complex_lp_on_plane s
          (slp_dbar_psi_inverse tau (slp_quarter_turn c) ?gR)"
      by (rule rotated_data[THEN conjunct2, THEN conjunct1])
    have rotated_dbar_bound:
        "aim_complex_lp_norm s
            (slp_dbar_psi_inverse tau (slp_quarter_turn c) ?gR)
          \<le> K * inverse (sqrt tau)"
      by (rule rotated_data[THEN conjunct2, THEN conjunct2, THEN conjunct2])
    let ?F = "slp_dbar_psi_inverse (- tau) c ?g"
    let ?H = "\<lambda>z.
      slp_dbar_psi_inverse tau (slp_quarter_turn c) ?gR
        (slp_quarter_turn z)"
    have pullback_data:
        "aim_complex_lp_on_plane s ?H \<and>
          aim_complex_lp_norm s ?H =
            aim_complex_lp_norm s
              (slp_dbar_psi_inverse tau (slp_quarter_turn c) ?gR)"
      by (rule slp_aim_complex_lp_on_plane_quarter_turn[OF
            rotated_dbar_lp])
    have covariance: "\<And>z. ?H z = - \<i> * ?F z"
      by (rule slp_dbar_psi_inverse_quarter_turn[OF product_test])
    have recover: "(\<lambda>z. \<i> * ?H z) = ?F"
    proof (rule ext)
      fix z :: slp_point
      show "\<i> * ?H z = ?F z"
        using covariance[of z] by (simp add: algebra_simps)
    qed
    have i_measurable:
        "(\<lambda>_::slp_point. \<i>) \<in> borel_measurable lborel"
      by measurable
    have i_bound:
        "\<And>x::slp_point. norm_class.norm (\<i>::complex) \<le> 1"
      by simp
    note recovered_data = slp_complex_lp_bounded_multiplier[
      OF s_positive i_measurable i_bound zero_le_one
        pullback_data[THEN conjunct1]]
    have F_lp: "aim_complex_lp_on_plane s ?F"
      using recovered_data(1)
      by (simp only: recover)
    have F_norm_le:
        "aim_complex_lp_norm s ?F \<le> aim_complex_lp_norm s ?H"
      using recovered_data(2)
      by (simp only: recover mult.left_neutral)
    have H_bound:
        "aim_complex_lp_norm s ?H \<le> K * inverse (sqrt tau)"
      using pullback_data rotated_dbar_bound by simp
    have F_bound:
        "aim_complex_lp_norm s ?F \<le> K * inverse (sqrt tau)"
      by (rule order_trans[OF F_norm_le H_bound])
    show
      "aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        aim_complex_lp_norm s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau)"
      using F_lp F_bound
      by (simp only: slp_right_recursive_branch.simps)
  qed
  show ?thesis
  proof (rule exI[where x=K], rule exI[where x=R])
    show
      "0 < K \<and> 0 < R \<and>
        (\<forall>c\<in>Z. \<forall>y.
          cutoff y * terminal_value y \<noteq> 0
          \<longrightarrow> norm_class.norm (y - c) \<le> R) \<and>
        (\<forall>tau c.
          2 \<le> tau \<and> c \<in> Z
          \<longrightarrow>
          aim_complex_lp_on_plane s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value) \<and>
          aim_complex_lp_norm s
              (slp_right_recursive_branch 0 tau c cutoff potential
                terminal_value)
            \<le> K * inverse (sqrt tau))"
      using K_positive R_positive original_support terminal by blast
  qed
qed

end

end
