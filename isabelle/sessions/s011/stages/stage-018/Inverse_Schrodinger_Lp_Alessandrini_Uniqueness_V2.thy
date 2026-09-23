theory Inverse_Schrodinger_Lp_Alessandrini_Uniqueness_V2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Subquadratic_Uniqueness"
begin

section \<open>Exact frozen all-exponent conditional uniqueness theorem\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_alessandrini_uniqueness_claim_v2:
  fixes p :: real and Omega :: "slp_point set"
    and V V_tilde :: slp_scalar_field
  assumes stationary:
      "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and fourier_plancherel:
      "hormander_euclidean_l2_fourier_plancherel_claim"
    and riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
    and compact_smooth_density:
      "evans_compact_smooth_lp_density_claim TYPE(2)"
  shows "slp_alessandrini_uniqueness_claim p Omega V V_tilde"
proof -
  have implication:
    "(1 < p \<and>
      slp_bounded_smooth_domain Omega \<and>
      Inverse_Schrodinger_Lp_Setup.slp_complex_lp_on p Omega V \<and>
      Inverse_Schrodinger_Lp_Setup.slp_complex_lp_on p Omega V_tilde \<and>
      slp_alessandrini_orthogonality Omega V V_tilde) \<Longrightarrow>
      slp_potential_ae_equal Omega V V_tilde"
  proof -
    assume antecedent:
      "1 < p \<and>
       slp_bounded_smooth_domain Omega \<and>
       Inverse_Schrodinger_Lp_Setup.slp_complex_lp_on p Omega V \<and>
       Inverse_Schrodinger_Lp_Setup.slp_complex_lp_on p Omega V_tilde \<and>
       slp_alessandrini_orthogonality Omega V V_tilde"
    then have exponent_lower: "1 < p"
      and domain: "slp_bounded_smooth_domain Omega"
      and V_lp:
        "Inverse_Schrodinger_Lp_Setup.slp_complex_lp_on p Omega V"
      and V_tilde_lp:
        "Inverse_Schrodinger_Lp_Setup.slp_complex_lp_on p Omega V_tilde"
      and orthogonality:
        "slp_alessandrini_orthogonality Omega V V_tilde"
      by blast+
    have exponent_positive: "0 < p"
      using exponent_lower by linarith
    have Omega_measurable: "Omega \<in> sets lborel"
      using slp_bounded_smooth_domain_lborel_carrier[OF domain] by blast
    have internal_lp:
      "\<And>f. Inverse_Schrodinger_Lp_Setup.slp_complex_lp_on p Omega f
        \<Longrightarrow> slp_complex_lp_on p Omega f"
    proof -
      fix f
      assume f_lp:
        "Inverse_Schrodinger_Lp_Setup.slp_complex_lp_on p Omega f"
      have f_measurable:
          "f \<in> borel_measurable (restrict_space lborel Omega)"
        using f_lp
        unfolding Inverse_Schrodinger_Lp_Setup.slp_complex_lp_on_def
        by blast
      have indicator_restriction:
          "(\<lambda>x. indicator Omega x *\<^sub>R f x) =
            slp_restrict_field Omega f"
        by (rule ext)
           (auto simp: indicator_def slp_restrict_field_def)
      have restrict_measurable:
          "slp_restrict_field Omega f \<in> borel_measurable lborel"
      proof -
        have indicator_measurable:
            "(\<lambda>x. indicator Omega x *\<^sub>R f x) \<in>
              borel_measurable lborel"
          using f_measurable
          apply (subst (asm) borel_measurable_restrict_space_iff)
           apply (use Omega_measurable in simp)
          .
        show ?thesis
          using indicator_measurable
          by (simp only: indicator_restriction)
      qed
      have f_power_integrable:
          "set_integrable lborel Omega
            (\<lambda>x. Real_Vector_Spaces.norm (f x) powr p)"
        using f_lp
        unfolding Inverse_Schrodinger_Lp_Setup.slp_complex_lp_on_def
        by blast
      have indicator_power:
          "(\<lambda>x. indicator Omega x *\<^sub>R
              (Real_Vector_Spaces.norm (f x) powr p)) =
            (\<lambda>x. Real_Vector_Spaces.norm
              (slp_restrict_field Omega f x) powr p)"
        by (rule ext)
           (auto simp: indicator_def slp_restrict_field_def
             exponent_positive)
      have restrict_power_integrable:
          "integrable lborel
            (\<lambda>x. Real_Vector_Spaces.norm
              (slp_restrict_field Omega f x) powr p)"
        using f_power_integrable
        unfolding set_integrable_def indicator_power .
      show "slp_complex_lp_on p Omega f"
        unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
        using restrict_measurable restrict_power_integrable by blast
    qed
    have V_internal_lp: "slp_complex_lp_on p Omega V"
      by (rule internal_lp[OF V_lp])
    have V_tilde_internal_lp: "slp_complex_lp_on p Omega V_tilde"
      by (rule internal_lp[OF V_tilde_lp])
    have subquadratic_case:
        "p < 2 \<Longrightarrow> slp_potential_ae_equal Omega V V_tilde"
    proof -
      assume exponent_upper: "p < 2"
      show ?thesis
        by (rule slp_alessandrini_subquadratic_uniqueness[
          OF stationary density fourier_plancherel riesz_hls
            cauchy_test_left_inverse evans_density compact_smooth_density
            exponent_lower exponent_upper domain V_internal_lp
            V_tilde_internal_lp
            orthogonality])
    qed
    have complementary_case:
        "\<not> p < 2 \<Longrightarrow> slp_potential_ae_equal Omega V V_tilde"
    proof -
      assume exponent_not_upper: "\<not> p < 2"
      have target_lower: "1 < (3 / 2 :: real)"
        by linarith
      have target_upper: "(3 / 2 :: real) < 2"
        by linarith
      have target_positive: "0 < (3 / 2 :: real)"
        by linarith
      have exponent_order: "(3 / 2 :: real) \<le> p"
        using exponent_not_upper by linarith
      have Omega_bounded: "bounded Omega"
        using domain unfolding slp_bounded_smooth_domain_def by blast
      have V_target_lp: "slp_complex_lp_on (3 / 2) Omega V"
        by (rule slp_complex_lp_on_mono_exponent_bounded[
          OF target_positive exponent_order Omega_measurable Omega_bounded
            V_internal_lp])
      have V_tilde_target_lp:
          "slp_complex_lp_on (3 / 2) Omega V_tilde"
        by (rule slp_complex_lp_on_mono_exponent_bounded[
          OF target_positive exponent_order Omega_measurable Omega_bounded
            V_tilde_internal_lp])
      show ?thesis
        by (rule slp_alessandrini_subquadratic_uniqueness[
          OF stationary density fourier_plancherel riesz_hls
            cauchy_test_left_inverse evans_density compact_smooth_density
            target_lower target_upper domain V_target_lp V_tilde_target_lp
            orthogonality])
    qed
    from subquadratic_case complementary_case show
        "slp_potential_ae_equal Omega V V_tilde"
      by blast
  qed
  show ?thesis
    unfolding slp_alessandrini_uniqueness_claim_def
    by (intro impI; rule implication)
qed

end

end
