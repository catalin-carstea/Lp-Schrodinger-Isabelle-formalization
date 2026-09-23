theory Inverse_Schrodinger_Lp_Qstar_Smooth_Compact_Center_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Smooth_Fixed_Terminal_Gain"
begin

section \<open>Compact-center uniformity for the fixed smooth terminal gain\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_smooth_fixed_terminal_gain_on_compact_centers:
  fixes s :: real and f :: slp_scalar_field and Z :: "slp_point set"
  assumes s_lower: "2 < s"
    and f_test: "slp_test_function_on UNIV f"
    and Z_compact: "compact Z"
  shows
    "\<exists>K R::real. 0 < K \<and> 0 < R \<and>
      (\<forall>c\<in>Z. \<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R) \<and>
      (\<forall>tau c.
        2 \<le> tau \<and> c \<in> Z
        \<longrightarrow>
        aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
        aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
        aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
          \<le> K * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
          \<le> K * inverse (sqrt tau))"
proof -
  let ?F = "closure {x. f x \<noteq> 0}"
  have F_compact: "compact ?F"
    using f_test unfolding slp_test_function_on_def by blast
  have F_bounded: "bounded ?F"
    by (rule compact_imp_bounded[OF F_compact])
  then obtain A where A_bound:
      "\<And>x. x \<in> ?F \<Longrightarrow> norm x \<le> A"
    unfolding bounded_iff by blast
  have Z_bounded: "bounded Z"
    by (rule compact_imp_bounded[OF Z_compact])
  then obtain B where B_bound:
      "\<And>x. x \<in> Z \<Longrightarrow> norm x \<le> B"
    unfolding bounded_iff by blast
  let ?R = "max 1 (max 0 A + max 0 B)"
  have R_positive: "0 < ?R"
    by simp
  have common_support:
      "\<And>c y. c \<in> Z \<Longrightarrow> f y \<noteq> 0 \<Longrightarrow>
        norm (y - c) \<le> ?R"
  proof -
    fix c y
    assume c_in: "c \<in> Z"
      and y_nonzero: "f y \<noteq> 0"
    have y_in: "y \<in> ?F"
      by (rule subsetD[OF closure_subset]) (use y_nonzero in simp)
    have y_bound: "norm y \<le> max 0 A"
      using A_bound[OF y_in] by linarith
    have c_bound: "norm c \<le> max 0 B"
      using B_bound[OF c_in] by linarith
    have distance_bound: "norm (y - c) \<le> norm y + norm c"
      by (rule norm_triangle_ineq4)
    show "norm (y - c) \<le> ?R"
      using distance_bound y_bound c_bound by linarith
  qed
  obtain K::real where K_positive: "0 < K"
    and terminal:
      "\<And>tau R c.
        2 \<le> tau \<and> 1 \<le> R * sqrt tau \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R)
        \<Longrightarrow>
        aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
        aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
        aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
          \<le> K * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
          \<le> K * inverse (sqrt tau)"
    using slp_qstar_smooth_fixed_terminal_gain[OF s_lower f_test] by blast
  show ?thesis
  proof (rule exI[where x=K], rule exI[where x="?R"])
    show
      "0 < K \<and> 0 < ?R \<and>
        (\<forall>c\<in>Z. \<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> ?R) \<and>
        (\<forall>tau c.
          2 \<le> tau \<and> c \<in> Z
          \<longrightarrow>
          aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
          aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
          aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
            \<le> K * inverse (sqrt tau) \<and>
          aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
            \<le> K * inverse (sqrt tau))"
    proof (rule conjI)
      show "0 < K"
        by (rule K_positive)
      show
        "0 < ?R \<and>
          (\<forall>c\<in>Z. \<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> ?R) \<and>
          (\<forall>tau c.
            2 \<le> tau \<and> c \<in> Z
            \<longrightarrow>
            aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
            aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
            aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
              \<le> K * inverse (sqrt tau) \<and>
            aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
              \<le> K * inverse (sqrt tau))"
      proof (rule conjI)
        show "0 < ?R"
          by (rule R_positive)
        show
          "(\<forall>c\<in>Z. \<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> ?R) \<and>
            (\<forall>tau c.
              2 \<le> tau \<and> c \<in> Z
              \<longrightarrow>
              aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
              aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
              aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
                \<le> K * inverse (sqrt tau) \<and>
              aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
                \<le> K * inverse (sqrt tau))"
        proof (rule conjI)
          show
            "\<forall>c\<in>Z. \<forall>y. f y \<noteq> 0 \<longrightarrow>
              norm (y - c) \<le> ?R"
            using common_support by blast
          show
            "\<forall>tau c.
              2 \<le> tau \<and> c \<in> Z
              \<longrightarrow>
              aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
              aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
              aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
                \<le> K * inverse (sqrt tau) \<and>
              aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
                \<le> K * inverse (sqrt tau)"
          proof (intro allI impI)
            fix tau :: real and c :: slp_point
            assume hypotheses: "2 \<le> tau \<and> c \<in> Z"
            then have tau_lower: "2 \<le> tau"
              and c_in: "c \<in> Z"
              by blast+
            have sqrt_lower: "1 \<le> sqrt tau"
              using tau_lower by simp
            have R_lower: "1 \<le> ?R"
              by simp
            have R_nonnegative: "0 \<le> ?R"
              using R_lower by linarith
            have normalized_lower: "1 \<le> ?R * sqrt tau"
            proof -
              have R_growth: "?R \<le> ?R * sqrt tau"
              proof -
                have "?R * 1 \<le> ?R * sqrt tau"
                  by (rule mult_left_mono[OF sqrt_lower R_nonnegative])
                then show ?thesis by simp
              qed
              show ?thesis
                by (rule order_trans[OF R_lower R_growth])
            qed
            show
              "aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
                aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
                aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
                  \<le> K * inverse (sqrt tau) \<and>
                aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
                  \<le> K * inverse (sqrt tau)"
              by (rule terminal[OF conjI[OF tau_lower
                    conjI[OF normalized_lower]]])
                (use common_support[OF c_in] in blast)
          qed
        qed
      qed
    qed
  qed
qed

end

end
