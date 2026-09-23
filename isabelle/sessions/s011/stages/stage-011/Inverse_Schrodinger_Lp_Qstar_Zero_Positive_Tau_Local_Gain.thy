theory Inverse_Schrodinger_Lp_Qstar_Zero_Positive_Tau_Local_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Qstar_Zero_Positive_Tau_Gain"
begin

section \<open>Restricted-output positive zero-branch terminal gain\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_zero_branches_positive_tau_local_compact_center_gain:
  fixes s :: real
    and cutoff terminal_value potential :: slp_scalar_field
    and X Z :: "slp_point set"
  assumes s_lower: "2 < s"
    and product_test:
      "slp_test_function_on UNIV (\<lambda>x. cutoff x * terminal_value x)"
    and X_measurable: "X \<in> sets lborel"
    and Z_compact: "compact Z"
  shows
    "\<exists>K R::real. 0 < K \<and> 0 < R \<and>
      (\<forall>c\<in>Z. \<forall>y.
        cutoff y * terminal_value y \<noteq> 0
        \<longrightarrow> norm_class.norm (y - c) \<le> R) \<and>
      (\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        slp_complex_lp_on s X
          (slp_left_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        slp_complex_lp_on s X
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        slp_complex_lp_norm_on s X
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau) \<and>
        slp_complex_lp_norm_on s X
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau))"
proof -
  obtain K R::real where K_positive: "0 < K"
    and R_positive: "0 < R"
    and support:
      "\<forall>c\<in>Z. \<forall>y.
        cutoff y * terminal_value y \<noteq> 0
        \<longrightarrow> norm_class.norm (y - c) \<le> R"
    and global_terminal:
      "\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        aim_complex_lp_on_plane s
          (slp_left_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        aim_complex_lp_norm s
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau)"
    using slp_qstar_zero_branches_positive_tau_compact_center_gain[
      OF s_lower product_test Z_compact] by blast
  have s_positive: "0 < s"
    using s_lower by linarith
  have local_terminal:
      "\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        slp_complex_lp_on s X
          (slp_left_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        slp_complex_lp_on s X
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        slp_complex_lp_norm_on s X
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau) \<and>
        slp_complex_lp_norm_on s X
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau)"
  proof (intro allI impI)
    fix tau :: real and c :: slp_point
    assume hypotheses: "2 \<le> tau \<and> c \<in> Z"
    have global_data:
        "aim_complex_lp_on_plane s
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value) \<and>
          aim_complex_lp_on_plane s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value) \<and>
          aim_complex_lp_norm s
              (slp_left_recursive_branch 0 tau c cutoff potential
                terminal_value)
            \<le> K * inverse (sqrt tau) \<and>
          aim_complex_lp_norm s
              (slp_right_recursive_branch 0 tau c cutoff potential
                terminal_value)
            \<le> K * inverse (sqrt tau)"
      using global_terminal hypotheses by blast
    have left_lp:
        "aim_complex_lp_on_plane s
          (slp_left_recursive_branch 0 tau c cutoff potential
            terminal_value)"
      by (rule global_data[THEN conjunct1])
    have right_lp:
        "aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value)"
      by (rule global_data[THEN conjunct2, THEN conjunct1])
    have left_local:
        "slp_complex_lp_on s X
          (slp_left_recursive_branch 0 tau c cutoff potential
            terminal_value)"
      by (rule aim_complex_lp_on_plane_restrict[
            OF s_positive X_measurable left_lp])
    have right_local:
        "slp_complex_lp_on s X
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value)"
      by (rule aim_complex_lp_on_plane_restrict[
            OF s_positive X_measurable right_lp])
    have left_local_le:
        "slp_complex_lp_norm_on s X
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> aim_complex_lp_norm s
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value)"
      by (rule slp_complex_lp_norm_on_le[
            OF s_positive X_measurable left_lp])
    have right_local_le:
        "slp_complex_lp_norm_on s X
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> aim_complex_lp_norm s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)"
      by (rule slp_complex_lp_norm_on_le[
            OF s_positive X_measurable right_lp])
    have left_bound:
        "slp_complex_lp_norm_on s X
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau)"
      by (rule order_trans[OF left_local_le
            global_data[THEN conjunct2, THEN conjunct2, THEN conjunct1]])
    have right_bound:
        "slp_complex_lp_norm_on s X
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau)"
      by (rule order_trans[OF right_local_le
            global_data[THEN conjunct2, THEN conjunct2, THEN conjunct2]])
    show
      "slp_complex_lp_on s X
          (slp_left_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        slp_complex_lp_on s X
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        slp_complex_lp_norm_on s X
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau) \<and>
        slp_complex_lp_norm_on s X
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> K * inverse (sqrt tau)"
      using left_local right_local left_bound right_bound by blast
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
          slp_complex_lp_on s X
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value) \<and>
          slp_complex_lp_on s X
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value) \<and>
          slp_complex_lp_norm_on s X
              (slp_left_recursive_branch 0 tau c cutoff potential
                terminal_value)
            \<le> K * inverse (sqrt tau) \<and>
          slp_complex_lp_norm_on s X
              (slp_right_recursive_branch 0 tau c cutoff potential
                terminal_value)
            \<le> K * inverse (sqrt tau))"
      using K_positive R_positive support local_terminal by blast
  qed
qed

end

end
