theory Inverse_Schrodinger_Lp_Outer_Conjugated_Source_Local_W1pstar
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Cutoff_Conjugated_Source_Lpstar"
begin

section \<open>Local above-two Sobolev data for the exact outer fields\<close>

context slp_cauchy_outer_fixed_point
begin

theorem slp_both_outer_conjugated_fields_local_w1pstar:
  fixes p M tau :: real
    and c :: slp_point
    and X Omega :: "slp_point set"
    and cutoff coefficient W :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and W_admissible: "slp_ae_bounded_measurable lborel M W"
    and Omega_measurable: "Omega \<in> sets (lborel :: slp_point measure)"
    and Omega_bounded: "bounded Omega"
  shows
    "slp_local_w1s_certificate (aim_hls_target_exponent p) Omega
        (slp_left_outer_conjugated_field tau c cutoff coefficient W)
        (slp_left_outer_conjugated_gradient tau c cutoff coefficient W)
      \<and>
      slp_local_w1s_certificate (aim_hls_target_exponent p) Omega
        (slp_right_outer_conjugated_field tau c cutoff coefficient W)
        (slp_right_outer_conjugated_gradient tau c cutoff coefficient W)"
proof -
  let ?qstar = "aim_hls_target_exponent p"
  let ?left_source =
    "\<lambda>x. cutoff x *
      slp_left_conjugated_cauchy_source tau c coefficient
        (\<lambda>y. coefficient y * W y) x"
  let ?right_source =
    "\<lambda>x. cutoff x *
      slp_right_conjugated_cauchy_source tau c coefficient
        (\<lambda>y. coefficient y * W y) x"
  let ?left_modulated = "slp_oscillatory_modulation tau c ?left_source"
  let ?right_modulated = "slp_oscillatory_modulation tau c ?right_source"

  have qstar_lower: "1 < ?qstar"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  note source_data = slp_both_cutoff_conjugated_sources_lpstar_support[OF
    exponent_lower exponent_upper X_open X_bounded cutoff_test coefficient_lp
    coefficient_support W_admissible]
  have left_source_lp: "aim_complex_lp_on_plane ?qstar ?left_source"
    using source_data by blast
  have left_source_support: "bounded {x. ?left_source x \<noteq> 0}"
    using source_data by blast
  have right_source_lp: "aim_complex_lp_on_plane ?qstar ?right_source"
    using source_data by blast
  have right_source_support: "bounded {x. ?right_source x \<noteq> 0}"
    using source_data by blast

  have left_modulated_lp:
      "aim_complex_lp_on_plane ?qstar ?left_modulated"
    using left_source_lp by simp
  have left_modulated_support:
      "bounded {x. ?left_modulated x \<noteq> 0}"
    using left_source_support by simp
  note left_certificates = slp_both_cauchy_local_w1s_certificates[OF
    qstar_lower left_modulated_lp left_modulated_support Omega_measurable
    Omega_bounded]
  have left_certificate:
      "slp_local_w1s_certificate ?qstar Omega
        (slp_partial_inverse ?left_modulated)
        (slp_partial_inverse_gradient ?left_modulated)"
    using left_certificates by blast

  have right_modulated_lp:
      "aim_complex_lp_on_plane ?qstar ?right_modulated"
    using right_source_lp by simp
  have right_modulated_support:
      "bounded {x. ?right_modulated x \<noteq> 0}"
    using right_source_support by simp
  note right_certificates = slp_both_cauchy_local_w1s_certificates[OF
    qstar_lower right_modulated_lp right_modulated_support Omega_measurable
    Omega_bounded]
  have right_certificate:
      "slp_local_w1s_certificate ?qstar Omega
        (slp_dbar_inverse ?right_modulated)
        (slp_dbar_inverse_gradient ?right_modulated)"
    using right_certificates by blast

  show ?thesis
    using left_certificate right_certificate
    unfolding slp_left_outer_conjugated_field_def
      slp_left_outer_conjugated_gradient_def
      slp_right_outer_conjugated_field_def
      slp_right_outer_conjugated_gradient_def
      slp_partial_psi_inverse_def slp_dbar_psi_inverse_def
    by simp
qed

end

end
