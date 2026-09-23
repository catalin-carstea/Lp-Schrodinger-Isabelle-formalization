theory Inverse_Schrodinger_Lp_Inner_Cauchy_Cutoff_Norm_Bounds
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Inner_Cauchy_Cutoff_Zero_Pairs"
begin

section \<open>Relative cutoff bounds for the two inner Cauchy fields\<close>

context slp_cauchy_local_w1s
begin

theorem slp_both_inner_cauchy_mult_test_w1p_norm_bounds:
  fixes s tau A B0 B1 :: real
    and X :: "slp_point set"
    and c :: slp_point
    and source cutoff :: slp_scalar_field
  assumes exponent_lower: "1 < s"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and source_lp: "aim_complex_lp_on_plane s source"
    and source_support: "bounded {x. source x \<noteq> 0}"
    and cutoff_test: "slp_test_function_on X cutoff"
    and cutoff_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (cutoff x) \<le> A"
    and cutoff_derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 0 x) \<le> B0"
    and cutoff_derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 1 x) \<le> B1"
    and A_nonnegative: "0 \<le> A"
    and B0_nonnegative: "0 \<le> B0"
    and B1_nonnegative: "0 \<le> B1"
  shows
    "slp_w1p_norm_on s X
        (\<lambda>x. cutoff x * slp_dbar_psi_inverse tau c source x)
        (\<lambda>x. \<chi> i.
          cutoff x *
            slp_dbar_inverse_gradient
              (slp_oscillatory_modulation (- tau) c source) x $ i +
          slp_dbar_psi_inverse tau c source x *
            slp_complex_partial_derivative cutoff i x)
      \<le>
        4 * (9 * A + 4 * B0 + 4 * B1) *
          slp_w1p_norm_on s X
            (slp_dbar_psi_inverse tau c source)
            (slp_dbar_inverse_gradient
              (slp_oscillatory_modulation (- tau) c source))
      \<and>
      slp_w1p_norm_on s X
        (\<lambda>x. cutoff x * slp_partial_psi_inverse (- tau) c source x)
        (\<lambda>x. \<chi> i.
          cutoff x *
            slp_partial_inverse_gradient
              (slp_oscillatory_modulation (- tau) c source) x $ i +
          slp_partial_psi_inverse (- tau) c source x *
            slp_complex_partial_derivative cutoff i x)
      \<le>
        4 * (9 * A + 4 * B0 + 4 * B1) *
          slp_w1p_norm_on s X
            (slp_partial_psi_inverse (- tau) c source)
            (slp_partial_inverse_gradient
              (slp_oscillatory_modulation (- tau) c source))"
proof -
  let ?g = "slp_oscillatory_modulation (- tau) c source"
  have exponent_one_le: "1 \<le> s"
    using exponent_lower by linarith
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have cutoff_smooth: "smooth_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by blast
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
  have dbar_pair:
      "slp_w1p_pair_on s X
        (slp_dbar_inverse ?g) (slp_dbar_inverse_gradient ?g)"
    by (rule slp_local_w1s_certificate_w1p_pair_on)
       (rule conjunct1[OF certificates])
  have partial_pair:
      "slp_w1p_pair_on s X
        (slp_partial_inverse ?g) (slp_partial_inverse_gradient ?g)"
    by (rule slp_local_w1s_certificate_w1p_pair_on)
       (rule conjunct2[OF certificates])
  have dbar_bound:
      "slp_w1p_norm_on s X
          (\<lambda>x. cutoff x * slp_dbar_inverse ?g x)
          (\<lambda>x. \<chi> i.
            cutoff x * slp_dbar_inverse_gradient ?g x $ i +
            slp_dbar_inverse ?g x *
              slp_complex_partial_derivative cutoff i x)
        \<le>
          4 * (9 * A + 4 * B0 + 4 * B1) *
            slp_w1p_norm_on s X
              (slp_dbar_inverse ?g) (slp_dbar_inverse_gradient ?g)"
    by (rule slp_w1p_norm_on_mult_smooth_bounded[OF
          exponent_one_le X_measurable X_bounded dbar_pair cutoff_smooth
          cutoff_bound cutoff_derivative_zero_bound
          cutoff_derivative_one_bound A_nonnegative B0_nonnegative
          B1_nonnegative])
  have partial_bound:
      "slp_w1p_norm_on s X
          (\<lambda>x. cutoff x * slp_partial_inverse ?g x)
          (\<lambda>x. \<chi> i.
            cutoff x * slp_partial_inverse_gradient ?g x $ i +
            slp_partial_inverse ?g x *
              slp_complex_partial_derivative cutoff i x)
        \<le>
          4 * (9 * A + 4 * B0 + 4 * B1) *
            slp_w1p_norm_on s X
              (slp_partial_inverse ?g) (slp_partial_inverse_gradient ?g)"
    by (rule slp_w1p_norm_on_mult_smooth_bounded[OF
          exponent_one_le X_measurable X_bounded partial_pair cutoff_smooth
          cutoff_bound cutoff_derivative_zero_bound
          cutoff_derivative_one_bound A_nonnegative B0_nonnegative
          B1_nonnegative])
  show ?thesis
    unfolding slp_dbar_psi_inverse_def slp_partial_psi_inverse_def
    by (rule conjI[OF dbar_bound partial_bound])
qed

end

end
