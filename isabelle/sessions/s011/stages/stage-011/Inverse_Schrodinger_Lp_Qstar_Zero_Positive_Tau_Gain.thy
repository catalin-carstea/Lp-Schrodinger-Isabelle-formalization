theory Inverse_Schrodinger_Lp_Qstar_Zero_Positive_Tau_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Qstar_Right_Zero_Positive_Tau_Gain"
begin

section \<open>Common positive-parameter zero-branch terminal gain\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_zero_branches_positive_tau_compact_center_gain:
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
          \<le> K * inverse (sqrt tau))"
proof -
  obtain KL RL::real where KL_positive: "0 < KL"
    and RL_positive: "0 < RL"
    and left_support:
      "\<forall>c\<in>Z. \<forall>y.
        cutoff y * terminal_value y \<noteq> 0
        \<longrightarrow> norm_class.norm (y - c) \<le> RL"
    and left_terminal:
      "\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        aim_complex_lp_on_plane s
          (slp_left_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 (- tau) c cutoff potential
            terminal_value) \<and>
        aim_complex_lp_norm s
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> KL * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s
            (slp_right_recursive_branch 0 (- tau) c cutoff potential
              terminal_value)
          \<le> KL * inverse (sqrt tau)"
    using slp_qstar_zero_branches_checked_sign_compact_center_gain[
      OF s_lower product_test Z_compact] by blast
  obtain KR RR::real where KR_positive: "0 < KR"
    and RR_positive: "0 < RR"
    and right_support:
      "\<forall>c\<in>Z. \<forall>y.
        cutoff y * terminal_value y \<noteq> 0
        \<longrightarrow> norm_class.norm (y - c) \<le> RR"
    and right_terminal:
      "\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        aim_complex_lp_norm s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> KR * inverse (sqrt tau)"
    using slp_qstar_right_zero_positive_tau_compact_center_gain[
      OF s_lower product_test Z_compact] by blast
  let ?K = "max KL KR"
  let ?R = "max RL RR"
  have KL_le: "KL \<le> ?K"
    by (rule max.cobounded1)
  have KR_le: "KR \<le> ?K"
    by (rule max.cobounded2)
  have RL_le: "RL \<le> ?R"
    by (rule max.cobounded1)
  have K_positive: "0 < ?K"
    using KL_positive KL_le by linarith
  have R_positive: "0 < ?R"
    using RL_positive RL_le by linarith
  have support:
      "\<forall>c\<in>Z. \<forall>y.
        cutoff y * terminal_value y \<noteq> 0
        \<longrightarrow> norm_class.norm (y - c) \<le> ?R"
  proof (intro ballI allI impI)
    fix c y
    assume c_in: "c \<in> Z"
      and product_nonzero: "cutoff y * terminal_value y \<noteq> 0"
    have base: "norm_class.norm (y - c) \<le> RL"
      using left_support c_in product_nonzero by blast
    show "norm_class.norm (y - c) \<le> ?R"
      by (rule order_trans[OF base RL_le])
  qed
  have terminal:
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
          \<le> ?K * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> ?K * inverse (sqrt tau)"
  proof (intro allI impI)
    fix tau :: real and c :: slp_point
    assume hypotheses: "2 \<le> tau \<and> c \<in> Z"
    have tau_positive: "0 < tau"
      using hypotheses by linarith
    have inverse_sqrt_nonnegative: "0 \<le> inverse (sqrt tau)"
      using tau_positive by simp
    have left_data:
        "aim_complex_lp_on_plane s
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value) \<and>
          aim_complex_lp_norm s
              (slp_left_recursive_branch 0 tau c cutoff potential
                terminal_value)
            \<le> KL * inverse (sqrt tau)"
      using left_terminal hypotheses by blast
    have right_data:
        "aim_complex_lp_on_plane s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value) \<and>
          aim_complex_lp_norm s
              (slp_right_recursive_branch 0 tau c cutoff potential
                terminal_value)
            \<le> KR * inverse (sqrt tau)"
      using right_terminal hypotheses by blast
    have left_scaled:
        "KL * inverse (sqrt tau) \<le> ?K * inverse (sqrt tau)"
      by (rule mult_right_mono[OF KL_le inverse_sqrt_nonnegative])
    have right_scaled:
        "KR * inverse (sqrt tau) \<le> ?K * inverse (sqrt tau)"
      by (rule mult_right_mono[OF KR_le inverse_sqrt_nonnegative])
    show
      "aim_complex_lp_on_plane s
          (slp_left_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value) \<and>
        aim_complex_lp_norm s
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> ?K * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> ?K * inverse (sqrt tau)"
    proof (intro conjI)
      show
        "aim_complex_lp_on_plane s
          (slp_left_recursive_branch 0 tau c cutoff potential
            terminal_value)"
        by (rule left_data[THEN conjunct1])
      show
        "aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 tau c cutoff potential
            terminal_value)"
        by (rule right_data[THEN conjunct1])
      show
        "aim_complex_lp_norm s
            (slp_left_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> ?K * inverse (sqrt tau)"
        by (rule order_trans[OF left_data[THEN conjunct2] left_scaled])
      show
        "aim_complex_lp_norm s
            (slp_right_recursive_branch 0 tau c cutoff potential
              terminal_value)
          \<le> ?K * inverse (sqrt tau)"
        by (rule order_trans[OF right_data[THEN conjunct2] right_scaled])
    qed
  qed
  show ?thesis
  proof (rule exI[where x="?K"], rule exI[where x="?R"])
    show
      "0 < ?K \<and> 0 < ?R \<and>
        (\<forall>c\<in>Z. \<forall>y.
          cutoff y * terminal_value y \<noteq> 0
          \<longrightarrow> norm_class.norm (y - c) \<le> ?R) \<and>
        (\<forall>tau c.
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
            \<le> ?K * inverse (sqrt tau) \<and>
          aim_complex_lp_norm s
              (slp_right_recursive_branch 0 tau c cutoff potential
                terminal_value)
            \<le> ?K * inverse (sqrt tau))"
      using K_positive R_positive support terminal by blast
  qed
qed

end

end
