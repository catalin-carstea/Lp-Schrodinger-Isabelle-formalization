theory Inverse_Schrodinger_Lp_Qstar_Zero_Branch_Checked_Sign_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Smooth_Compact_Center_Gain"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Recursive_Branch"
begin

section \<open>Zero-branch terminal gain for the checked sign pair\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_zero_branches_checked_sign_compact_center_gain:
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
        \<longrightarrow> norm (y - c) \<le> R) \<and>
      (\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        aim_complex_lp_on_plane s
          (slp_left_recursive_branch 0 tau c cutoff potential terminal_value) \<and>
        aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 (- tau) c cutoff potential terminal_value) \<and>
        aim_complex_lp_norm s
            (slp_left_recursive_branch 0 tau c cutoff potential terminal_value)
          \<le> K * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s
            (slp_right_recursive_branch 0 (- tau) c cutoff potential terminal_value)
          \<le> K * inverse (sqrt tau))"
proof -
  let ?g = "\<lambda>x. cutoff x * terminal_value x"
  obtain K R::real where K_positive: "0 < K"
    and R_positive: "0 < R"
    and support:
      "\<forall>c\<in>Z. \<forall>y. ?g y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R"
    and terminal:
      "\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c ?g) \<and>
        aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c ?g) \<and>
        aim_complex_lp_norm s (slp_partial_psi_inverse tau c ?g)
          \<le> K * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s (slp_dbar_psi_inverse tau c ?g)
          \<le> K * inverse (sqrt tau)"
    using slp_qstar_smooth_fixed_terminal_gain_on_compact_centers[
      OF s_lower product_test Z_compact] by blast
  have branch_terminal:
      "\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        aim_complex_lp_on_plane s
          (slp_left_recursive_branch 0 tau c cutoff potential terminal_value) \<and>
        aim_complex_lp_on_plane s
          (slp_right_recursive_branch 0 (- tau) c cutoff potential terminal_value) \<and>
        aim_complex_lp_norm s
            (slp_left_recursive_branch 0 tau c cutoff potential terminal_value)
          \<le> K * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s
            (slp_right_recursive_branch 0 (- tau) c cutoff potential terminal_value)
          \<le> K * inverse (sqrt tau)"
    using terminal
    by (simp only: slp_left_recursive_branch.simps
          slp_right_recursive_branch.simps minus_minus)
  show ?thesis
  proof (rule exI[where x=K], rule exI[where x=R])
    show
      "0 < K \<and> 0 < R \<and>
        (\<forall>c\<in>Z. \<forall>y.
          cutoff y * terminal_value y \<noteq> 0
          \<longrightarrow> norm (y - c) \<le> R) \<and>
        (\<forall>tau c.
          2 \<le> tau \<and> c \<in> Z
          \<longrightarrow>
          aim_complex_lp_on_plane s
            (slp_left_recursive_branch 0 tau c cutoff potential terminal_value) \<and>
          aim_complex_lp_on_plane s
            (slp_right_recursive_branch 0 (- tau) c cutoff potential terminal_value) \<and>
          aim_complex_lp_norm s
              (slp_left_recursive_branch 0 tau c cutoff potential terminal_value)
            \<le> K * inverse (sqrt tau) \<and>
          aim_complex_lp_norm s
              (slp_right_recursive_branch 0 (- tau) c cutoff potential terminal_value)
            \<le> K * inverse (sqrt tau))"
      using K_positive R_positive support branch_terminal by blast
  qed
qed

end

end
