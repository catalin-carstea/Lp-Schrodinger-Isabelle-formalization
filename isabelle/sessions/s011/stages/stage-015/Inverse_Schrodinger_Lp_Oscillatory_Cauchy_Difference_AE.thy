theory Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Difference_AE
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Difference_Low_Esssup"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Scalar_Extraction"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Localized_Cauchy_Riesz"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Almost-everywhere linearity of the oscillatory Cauchy operators\<close>

context aim_planar_riesz_hls
begin

theorem slp_cauchy_integrable_at_AE:
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and source_lp: "aim_complex_lp_on_plane p f"
  shows "AE z in (lborel :: slp_point measure).
    slp_cauchy_integrable_at orientation f z"
proof -
  obtain C :: real where C_positive: "0 < C"
    and C_all:
      "\<And>p f. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p f \<Longrightarrow>
        (AE z in (lborel :: slp_point measure).
          integrable lborel (aim_planar_riesz_integrand f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (aim_planar_riesz_potential f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (aim_planar_riesz_potential f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using aim_planar_riesz_hls
    unfolding aim_planar_riesz_hls_claim_def by blast
  have source_measurable: "f \<in> borel_measurable lborel"
    using source_lp unfolding aim_complex_lp_on_plane_def by blast
  have majorant_integrable:
      "AE z in (lborel :: slp_point measure).
        integrable lborel (aim_planar_riesz_integrand f z)"
    using C_all[OF exponent_lower exponent_upper source_lp] by blast
  show ?thesis
    using majorant_integrable
  proof eventually_elim
    fix z :: slp_point
    assume majorant:
      "integrable lborel (aim_planar_riesz_integrand f z)"
    have majorant_eq:
        "(\<lambda>y. norm (f y) *
          norm (slp_cauchy_kernel orientation z y)) =
          aim_planar_riesz_integrand f z"
    proof (rule ext)
      fix y :: slp_point
      have complex_difference:
          "slp_point_as_complex z - slp_point_as_complex y =
            slp_point_as_complex (z - y)"
        by (rule sym, rule slp_point_as_complex_diff)
      show "norm (f y) * norm (slp_cauchy_kernel orientation z y) =
          aim_planar_riesz_integrand f z y"
        unfolding aim_planar_riesz_integrand_def
        by (simp only: aim_point_as_complex_eq_slp
              complex_difference slp_point_as_complex_norm
              slp_cauchy_kernel_norm slp_radial_inverse_def)
    qed
    show "slp_cauchy_integrable_at orientation f z"
      by (rule slp_cauchy_integrable_at_of_norm_majorant[
            OF source_measurable])
        (use majorant in \<open>simp only: majorant_eq\<close>)
  qed
qed

theorem slp_both_oscillatory_cauchy_difference_AE:
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and first_lp: "aim_complex_lp_on_plane p f"
    and second_lp: "aim_complex_lp_on_plane p g"
  shows
    "(AE z in (lborel :: slp_point measure).
      slp_dbar_psi_inverse tau c (\<lambda>y. f y - g y) z =
        slp_dbar_psi_inverse tau c f z -
          slp_dbar_psi_inverse tau c g z) \<and>
    (AE z in (lborel :: slp_point measure).
      slp_partial_psi_inverse (- tau) c (\<lambda>y. f y - g y) z =
        slp_partial_psi_inverse (- tau) c f z -
          slp_partial_psi_inverse (- tau) c g z)"
proof -
  have first_modulated_lp:
      "aim_complex_lp_on_plane p
        (slp_oscillatory_modulation (- tau) c f)"
    using first_lp by simp
  have second_modulated_lp:
      "aim_complex_lp_on_plane p
        (slp_oscillatory_modulation (- tau) c g)"
    using second_lp by simp
  have generic:
      "\<And>orientation. AE z in (lborel :: slp_point measure).
        slp_cauchy_transform orientation
            (slp_oscillatory_modulation (- tau) c
              (\<lambda>y. f y - g y)) z =
          slp_cauchy_transform orientation
              (slp_oscillatory_modulation (- tau) c f) z -
            slp_cauchy_transform orientation
              (slp_oscillatory_modulation (- tau) c g) z"
  proof -
    fix orientation :: slp_cauchy_orientation
    have first_integrable:
        "AE z in (lborel :: slp_point measure).
          slp_cauchy_integrable_at orientation
            (slp_oscillatory_modulation (- tau) c f) z"
      by (rule slp_cauchy_integrable_at_AE[
            OF exponent_lower exponent_upper first_modulated_lp])
    have second_integrable:
        "AE z in (lborel :: slp_point measure).
          slp_cauchy_integrable_at orientation
            (slp_oscillatory_modulation (- tau) c g) z"
      by (rule slp_cauchy_integrable_at_AE[
            OF exponent_lower exponent_upper second_modulated_lp])
    show "AE z in (lborel :: slp_point measure).
        slp_cauchy_transform orientation
            (slp_oscillatory_modulation (- tau) c
              (\<lambda>y. f y - g y)) z =
          slp_cauchy_transform orientation
              (slp_oscillatory_modulation (- tau) c f) z -
            slp_cauchy_transform orientation
              (slp_oscillatory_modulation (- tau) c g) z"
      using first_integrable second_integrable
    proof eventually_elim
      fix z :: slp_point
      assume first_at:
          "slp_cauchy_integrable_at orientation
            (slp_oscillatory_modulation (- tau) c f) z"
        and second_at:
          "slp_cauchy_integrable_at orientation
            (slp_oscillatory_modulation (- tau) c g) z"
      have negative_second_at:
          "slp_cauchy_integrable_at orientation
            (\<lambda>y. (- 1) *
              slp_oscillatory_modulation (- tau) c g y) z"
        by (rule slp_cauchy_integrable_at_mult_left[OF second_at])
      have transform_add:
          "slp_cauchy_transform orientation
              (\<lambda>y. slp_oscillatory_modulation (- tau) c f y +
                (- 1) * slp_oscillatory_modulation (- tau) c g y) z =
            slp_cauchy_transform orientation
                (slp_oscillatory_modulation (- tau) c f) z +
              slp_cauchy_transform orientation
                (\<lambda>y. (- 1) *
                  slp_oscillatory_modulation (- tau) c g y) z"
        by (rule slp_cauchy_transform_add[
              OF first_at negative_second_at])
      have transform_negative:
          "slp_cauchy_transform orientation
              (\<lambda>y. (- 1) *
                slp_oscillatory_modulation (- tau) c g y) z =
            (- 1) * slp_cauchy_transform orientation
              (slp_oscillatory_modulation (- tau) c g) z"
        by (rule slp_cauchy_transform_mult_left[OF second_at])
      have source_eq:
          "(\<lambda>y. slp_oscillatory_modulation (- tau) c f y +
              (- 1) * slp_oscillatory_modulation (- tau) c g y) =
            slp_oscillatory_modulation (- tau) c
              (\<lambda>y. f y - g y)"
        by (rule ext)
          (simp add: slp_oscillatory_modulation_def algebra_simps)
      show "slp_cauchy_transform orientation
            (slp_oscillatory_modulation (- tau) c
              (\<lambda>y. f y - g y)) z =
          slp_cauchy_transform orientation
              (slp_oscillatory_modulation (- tau) c f) z -
            slp_cauchy_transform orientation
              (slp_oscillatory_modulation (- tau) c g) z"
        using transform_add transform_negative
        unfolding source_eq by simp
    qed
  qed
  note dbar = generic[where orientation=SLP_Dbar_Inverse]
  note partial = generic[where orientation=SLP_Partial_Inverse]
  show ?thesis
    using dbar partial
    unfolding slp_dbar_psi_inverse_def slp_partial_psi_inverse_def
    by blast
qed

end

end
