theory Inverse_Schrodinger_Lp_Inner_Cauchy_Cutoff_Zero_Pairs
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Local_W1s_Cutoff_Zero_Pair"
begin

section \<open>The two compactly cut off inner Cauchy fields\<close>

context slp_cauchy_local_w1s
begin

theorem slp_both_inner_cauchy_mult_test_w1p_zero_pairs:
  fixes s tau :: real
    and X :: "slp_point set"
    and c :: slp_point
    and source cutoff :: slp_scalar_field
  assumes evans_density: "evans_compact_support_w1p_zero_density_claim"
    and exponent_lower: "1 < s"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and source_lp: "aim_complex_lp_on_plane s source"
    and source_support: "bounded {x. source x \<noteq> 0}"
    and cutoff_test: "slp_test_function_on X cutoff"
  shows
    "slp_w1p_zero_pair_on s X
        (\<lambda>x. cutoff x * slp_dbar_psi_inverse tau c source x)
        (\<lambda>x. \<chi> i.
          cutoff x *
            slp_dbar_inverse_gradient
              (slp_oscillatory_modulation (- tau) c source) x $ i +
          slp_dbar_psi_inverse tau c source x *
            slp_complex_partial_derivative cutoff i x)
      \<and>
      slp_w1p_zero_pair_on s X
        (\<lambda>x. cutoff x * slp_partial_psi_inverse (- tau) c source x)
        (\<lambda>x. \<chi> i.
          cutoff x *
            slp_partial_inverse_gradient
              (slp_oscillatory_modulation (- tau) c source) x $ i +
          slp_partial_psi_inverse (- tau) c source x *
            slp_complex_partial_derivative cutoff i x)"
proof -
  let ?g = "slp_oscillatory_modulation (- tau) c source"
  have evans_instance: "evans_compact_support_w1p_zero_density"
    by unfold_locales (rule evans_density)
  have exponent_one_le: "1 \<le> s"
    using exponent_lower by linarith
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have modulated_lp: "aim_complex_lp_on_plane s ?g"
    using source_lp by simp
  have modulated_support: "bounded {x. ?g x \<noteq> 0}"
    using source_support by simp
  have certificates:
      "slp_local_w1s_certificate s X
          (slp_dbar_inverse ?g) (slp_dbar_inverse_gradient ?g) \<and>
        slp_local_w1s_certificate s X
          (slp_partial_inverse ?g) (slp_partial_inverse_gradient ?g)"
    by (rule slp_both_cauchy_local_w1s_certificates[OF
          exponent_lower modulated_lp modulated_support
          X_measurable X_bounded])
  have dbar_certificate:
      "slp_local_w1s_certificate s X
        (slp_dbar_inverse ?g) (slp_dbar_inverse_gradient ?g)"
    by (rule conjunct1[OF certificates])
  have partial_certificate:
      "slp_local_w1s_certificate s X
        (slp_partial_inverse ?g) (slp_partial_inverse_gradient ?g)"
    by (rule conjunct2[OF certificates])
  have dbar_zero_pair:
      "slp_w1p_zero_pair_on s X
        (\<lambda>x. cutoff x * slp_dbar_inverse ?g x)
        (\<lambda>x. \<chi> i.
          cutoff x * slp_dbar_inverse_gradient ?g x $ i +
          slp_dbar_inverse ?g x *
            slp_complex_partial_derivative cutoff i x)"
    by (rule evans_compact_support_w1p_zero_density.slp_local_w1s_certificate_mult_test_w1p_zero_pair[OF
          evans_instance exponent_one_le X_open X_bounded
          dbar_certificate cutoff_test])
  have partial_zero_pair:
      "slp_w1p_zero_pair_on s X
        (\<lambda>x. cutoff x * slp_partial_inverse ?g x)
        (\<lambda>x. \<chi> i.
          cutoff x * slp_partial_inverse_gradient ?g x $ i +
          slp_partial_inverse ?g x *
            slp_complex_partial_derivative cutoff i x)"
    by (rule evans_compact_support_w1p_zero_density.slp_local_w1s_certificate_mult_test_w1p_zero_pair[OF
          evans_instance exponent_one_le X_open X_bounded
          partial_certificate cutoff_test])
  show ?thesis
    using dbar_zero_pair partial_zero_pair
    unfolding slp_dbar_psi_inverse_def slp_partial_psi_inverse_def
    by blast
qed

end

end
