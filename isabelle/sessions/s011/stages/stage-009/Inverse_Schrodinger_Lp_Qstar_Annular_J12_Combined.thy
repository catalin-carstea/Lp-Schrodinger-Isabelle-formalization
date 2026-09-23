theory Inverse_Schrodinger_Lp_Qstar_Annular_J12_Combined
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_J2_Riesz_HLS"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The combined square-denominator annular potential\<close>

definition slp_qstar_annular_J12_potential ::
  "real \<Rightarrow> real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_qstar_annular_J12_potential delta R f z =
    slp_qstar_annular_J1_potential delta R f z +
    slp_qstar_annular_J2_potential delta R f z"

lemma slp_qstar_annular_J2_potential_nonnegative_full:
  "0 \<le> slp_qstar_annular_J2_potential delta R f z"
  unfolding slp_qstar_annular_J2_potential_def
  by (rule integral_nonneg_AE)
    (simp add: slp_qstar_annular_J2_weighted_integrand_nonnegative)

context aim_planar_riesz_hls
begin

theorem slp_qstar_annular_J12_combined:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a delta R f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      0 \<le> slp_qstar_annular_J12_potential delta R f z \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_J12_potential delta R f) \<and>
      aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_J12_potential delta R f) \<le>
        4 *
          ((1 / delta) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f +
           C / ((a - 1) * (2 - a)) * (1 / delta) *
              slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f))"
proof -
  obtain C::real where C_positive: "0 < C"
    and J2_all:
      "\<forall>a delta R f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
        \<longrightarrow>
        (AE z in lborel. integrable lborel
          (slp_qstar_annular_J2_weighted_integrand delta R f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent a)
          (slp_qstar_annular_J2_potential delta R f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent a)
            (slp_qstar_annular_J2_potential delta R f)
          \<le> C / ((a - 1) * (2 - a)) * (1 / delta) *
            slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f"
    using slp_qstar_annular_J2_riesz_hls by blast
  have all_combined:
    "\<forall>a delta R f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      0 \<le> slp_qstar_annular_J12_potential delta R f z \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_J12_potential delta R f) \<and>
      aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_J12_potential delta R f) \<le>
        4 *
          ((1 / delta) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f +
           C / ((a - 1) * (2 - a)) * (1 / delta) *
              slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
  proof (intro allI impI)
    fix a delta R :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    have exponent_lower: "1 < a" and exponent_upper: "a < 2"
      and delta_positive: "0 < delta" and radius_lower: "delta \<le> R"
      using hypotheses by blast+
    have amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      using hypotheses by blast
    let ?q = "aim_hls_target_exponent a"
    let ?J1 = "slp_qstar_annular_J1_potential delta R f"
    let ?J2 = "slp_qstar_annular_J2_potential delta R f"
    let ?J = "slp_qstar_annular_J12_potential delta R f"
    let ?U = "(1 / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
      aim_complex_lp_norm ?q f"
    let ?V = "C / ((a - 1) * (2 - a)) * (1 / delta) *
      slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
      aim_complex_lp_norm ?q f"
    have q_above_two: "2 < ?q"
      by (rule slp_qstar_exponent_relations(1)[OF exponent_lower
            exponent_upper])
    have q_positive: "0 < ?q" and q_above_one: "1 < ?q"
      using q_above_two by linarith+
    have J1_nonnegative: "0 \<le> ?J1 x" for x
      by (rule slp_qstar_annular_J1_envelope(2)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have J2_nonnegative: "0 \<le> ?J2 x" for x
      by (rule slp_qstar_annular_J2_potential_nonnegative_full)
    have combined_nonnegative: "0 \<le> ?J z"
      unfolding slp_qstar_annular_J12_potential_def
      using J1_nonnegative[of z] J2_nonnegative[of z] by linarith
    have J1_lp: "aim_real_lp_on_plane ?q ?J1"
      by (rule slp_qstar_annular_J1_Lp_bound(1)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have J1_norm: "aim_real_lp_norm ?q ?J1 \<le> ?U"
      by (rule slp_qstar_annular_J1_Lp_bound(2)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have J2_data:
        "aim_real_lp_on_plane ?q ?J2 \<and> aim_real_lp_norm ?q ?J2 \<le> ?V"
      using J2_all exponent_lower exponent_upper delta_positive radius_lower
        amplitude_lp by blast
    have J2_lp: "aim_real_lp_on_plane ?q ?J2"
      using J2_data by blast
    have J2_norm: "aim_real_lp_norm ?q ?J2 \<le> ?V"
      using J2_data by blast
    have sum_data:
        "aim_real_lp_on_plane ?q (\<lambda>x. ?J1 x + ?J2 x) \<and>
        integral\<^sup>L lborel (\<lambda>x. abs (?J1 x + ?J2 x) powr ?q) \<le>
          2 powr ?q *
            (integral\<^sup>L lborel (\<lambda>x. abs (?J1 x) powr ?q) +
             integral\<^sup>L lborel (\<lambda>x. abs (?J2 x) powr ?q))"
      using slp_aim_real_lp_on_plane_add_power_bound[OF q_positive
          J1_lp J2_lp] by blast
    have combined_function: "?J = (\<lambda>x. ?J1 x + ?J2 x)"
      unfolding slp_qstar_annular_J12_potential_def by (rule refl)
    have combined_lp: "aim_real_lp_on_plane ?q ?J"
      unfolding combined_function using sum_data by blast
    let ?A = "integral\<^sup>L lborel (\<lambda>x. abs (?J1 x) powr ?q)"
    let ?B = "integral\<^sup>L lborel (\<lambda>x. abs (?J2 x) powr ?q)"
    have combined_power_bound:
        "integral\<^sup>L lborel (\<lambda>x. abs (?J x) powr ?q) \<le>
          2 powr ?q * (?A + ?B)"
      unfolding combined_function using sum_data by blast
    have combined_mass_nonnegative:
        "0 \<le> integral\<^sup>L lborel (\<lambda>x. abs (?J x) powr ?q)"
      by (rule integral_nonneg_AE) simp
    have inverse_q_nonnegative: "0 \<le> 1 / ?q"
      using q_positive by simp
    have combined_to_two_mass:
        "aim_real_lp_norm ?q ?J \<le>
          (2 powr ?q * (?A + ?B)) powr (1 / ?q)"
      unfolding aim_real_lp_norm_def
      by (rule powr_mono2[OF inverse_q_nonnegative
            combined_mass_nonnegative combined_power_bound])
    have A_nonnegative: "0 \<le> ?A" and B_nonnegative: "0 \<le> ?B"
      by (rule integral_nonneg_AE, simp)+
    have A_root: "?A powr (1 / ?q) \<le> ?U"
      using J1_norm unfolding aim_real_lp_norm_def by simp
    have B_root: "?B powr (1 / ?q) \<le> ?V"
      using J2_norm unfolding aim_real_lp_norm_def by simp
    have two_mass:
        "(2 powr ?q * (?A + ?B)) powr (1 / ?q) \<le>
          4 * (?U + ?V)"
      by (rule slp_two_power_root_bound[OF q_above_one A_nonnegative
            B_nonnegative A_root B_root])
    have combined_norm: "aim_real_lp_norm ?q ?J \<le> 4 * (?U + ?V)"
      by (rule order_trans[OF combined_to_two_mass two_mass])
    show "0 \<le> ?J z \<and> aim_real_lp_on_plane ?q ?J \<and>
        aim_real_lp_norm ?q ?J \<le> 4 * (?U + ?V)"
      using combined_nonnegative combined_lp combined_norm by blast
  qed
  show ?thesis
    using C_positive all_combined by blast
qed

end

end
