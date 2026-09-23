theory Inverse_Schrodinger_Lp_Cauchy_Measurable_Below_Two
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Cutoff_Terminal_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_HLS_Both"
begin

section \<open>Measurability of both Cauchy orientations below two\<close>

context aim_planar_hls_cauchy
begin

theorem slp_cauchy_transform_measurable_below_two:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and potential_lp: "aim_complex_lp_on_plane p potential"
  shows
    "slp_cauchy_transform orientation potential \<in>
      borel_measurable lborel"
proof -
  obtain C :: real where C_positive: "0 < C"
    and both:
      "\<forall>p f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
        \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_dbar_inverse f) \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_partial_inverse f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_dbar_inverse f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_partial_inverse f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_both_cauchy_hls by blast
  have hypotheses:
      "1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p potential"
    using p_lower p_upper potential_lp by blast
  show ?thesis
  proof (cases orientation)
    case SLP_Partial_Inverse
    have mapped:
        "aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_inverse potential)"
      using both hypotheses by blast
    show ?thesis
      using mapped SLP_Partial_Inverse
      unfolding aim_complex_lp_on_plane_def by simp
  next
    case SLP_Dbar_Inverse
    have mapped:
        "aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_dbar_inverse potential)"
      using both hypotheses by blast
    show ?thesis
      using mapped SLP_Dbar_Inverse
      unfolding aim_complex_lp_on_plane_def by simp
  qed
qed

end

end
