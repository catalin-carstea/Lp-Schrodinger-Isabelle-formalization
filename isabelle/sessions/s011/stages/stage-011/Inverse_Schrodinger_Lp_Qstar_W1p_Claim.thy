theory Inverse_Schrodinger_Lp_Qstar_W1p_Claim
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Rough_Partial_Psi_Gain"
begin

section \<open>The reviewed rough qstar estimate on the manuscript domain\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_w1p_claim_proved:
  "slp_qstar_w1p_claim a X Z"
  unfolding slp_qstar_w1p_claim_def
proof (rule impI)
  assume geometry:
    "1 < a \<and> a < 2 \<and> open X \<and> X \<noteq> {} \<and>
      bounded X \<and> compact Z"
  have a_lower: "1 < a" and a_upper: "a < 2"
    and X_open: "open X" and X_bounded: "bounded X"
    using geometry by blast+
  have X_measurable: "X \<in> sets lborel"
    using borel_open[OF X_open] by simp
  have target_positive: "0 < aim_hls_target_exponent a"
    using slp_qstar_exponent_relations(1)[OF a_lower a_upper] by linarith
  obtain C::real where C_positive: "0 < C"
    and global_gain:
      "\<And>tau c f Df.
        2 \<le> tau \<Longrightarrow> slp_w1p_zero_pair_on a X f Df \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c (slp_restrict_field X f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c (slp_restrict_field X f))
          \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
    using slp_w1p_zero_pair_partial_psi_gain[
      OF a_lower a_upper X_bounded] by blast
  have local_gain:
      "slp_complex_lp_on (aim_hls_target_exponent a) X
        (slp_partial_psi_inverse tau c (slp_restrict_field X f)) \<and>
      slp_complex_lp_norm_on (aim_hls_target_exponent a) X
        (slp_partial_psi_inverse tau c (slp_restrict_field X f))
        \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
    if tau_lower: "2 \<le> tau"
      and zero_pair: "slp_w1p_zero_pair_on a X f Df"
    for tau c f Df
  proof -
    let ?T = "slp_partial_psi_inverse tau c (slp_restrict_field X f)"
    note global_data = global_gain[OF tau_lower zero_pair]
    have global_lp: "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?T"
      by (rule conjunct1[OF global_data])
    have local_lp: "slp_complex_lp_on (aim_hls_target_exponent a) X ?T"
      by (rule aim_complex_lp_on_plane_restrict[
            OF target_positive X_measurable global_lp])
    have local_norm_le:
        "slp_complex_lp_norm_on (aim_hls_target_exponent a) X ?T \<le>
          aim_complex_lp_norm (aim_hls_target_exponent a) ?T"
      by (rule slp_complex_lp_norm_on_le[
            OF target_positive X_measurable global_lp])
    have local_bound:
        "slp_complex_lp_norm_on (aim_hls_target_exponent a) X ?T \<le>
          C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
      by (rule order_trans[OF local_norm_le conjunct2[OF global_data]])
    show ?thesis by (rule conjI[OF local_lp local_bound])
  qed
  show "\<exists>C::real. 0 < C \<and>
    (\<forall>tau z0 f Df.
      2 \<le> tau \<and> z0 \<in> Z \<and> slp_w1p_zero_pair_on a X f Df
      \<longrightarrow>
      slp_complex_lp_on (aim_hls_target_exponent a) X
        (slp_partial_psi_inverse tau z0 (slp_restrict_field X f)) \<and>
      slp_complex_lp_norm_on (aim_hls_target_exponent a) X
        (slp_partial_psi_inverse tau z0 (slp_restrict_field X f))
        \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df)"
    by (rule exI[of _ C], rule conjI[OF C_positive])
      (use local_gain in blast)
qed

end

end
