theory Inverse_Schrodinger_Lp_Qstar_Annular_Combined_Constant
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_Combined_Lp"
begin

hide_const (open) Commutative_Ring.norm

section \<open>A delta-independent constant for the combined annular terms\<close>

lemma slp_two_power_root_bound:
  fixes p A B U V :: real
  assumes exponent_above_one: "1 < p"
    and left_mass_nonnegative: "0 \<le> A"
    and right_mass_nonnegative: "0 \<le> B"
    and left_root_bound: "A powr (1 / p) \<le> U"
    and right_root_bound: "B powr (1 / p) \<le> V"
  shows
    "(2 powr p * (A + B)) powr (1 / p) \<le> 4 * (U + V)"
proof -
  have exponent_positive: "0 < p"
    using exponent_above_one by linarith
  have exponent_nonzero: "p \<noteq> 0"
    using exponent_positive by simp
  have exponent_nonnegative: "0 \<le> p"
    using exponent_positive by linarith
  have inverse_exponent_nonnegative: "0 \<le> 1 / p"
    using exponent_positive by simp
  have left_root_nonnegative: "0 \<le> A powr (1 / p)"
    by simp
  have right_root_nonnegative: "0 \<le> B powr (1 / p)"
    by simp
  have U_nonnegative: "0 \<le> U"
    using left_root_nonnegative left_root_bound by linarith
  have V_nonnegative: "0 \<le> V"
    using right_root_nonnegative right_root_bound by linarith
  have sum_nonnegative: "0 \<le> U + V"
    using U_nonnegative V_nonnegative by linarith
  have left_reconstruct: "(A powr (1 / p)) powr p = A"
    using exponent_nonzero left_mass_nonnegative
    by (simp add: powr_powr)
  have right_reconstruct: "(B powr (1 / p)) powr p = B"
    using exponent_nonzero right_mass_nonnegative
    by (simp add: powr_powr)
  have left_root_to_sum: "A powr (1 / p) \<le> U + V"
    using left_root_bound V_nonnegative by linarith
  have right_root_to_sum: "B powr (1 / p) \<le> U + V"
    using right_root_bound U_nonnegative by linarith
  have left_to_sum_power: "A \<le> (U + V) powr p"
  proof -
    have "(A powr (1 / p)) powr p \<le> (U + V) powr p"
      by (rule powr_mono2[OF exponent_nonnegative left_root_nonnegative
            left_root_to_sum])
    then show ?thesis
      using left_reconstruct by simp
  qed
  have right_to_sum_power: "B \<le> (U + V) powr p"
  proof -
    have "(B powr (1 / p)) powr p \<le> (U + V) powr p"
      by (rule powr_mono2[OF exponent_nonnegative right_root_nonnegative
            right_root_to_sum])
    then show ?thesis
      using right_reconstruct by simp
  qed
  have mass_sum_bound:
      "A + B \<le> 2 * ((U + V) powr p)"
    using left_to_sum_power right_to_sum_power by linarith
  have two_power_lower: "2 \<le> 2 powr p"
  proof -
    have "2 powr (1::real) \<le> 2 powr p"
      by (rule powr_mono) (use exponent_above_one in simp_all)
    then show ?thesis by simp
  qed
  have sum_power_nonnegative: "0 \<le> (U + V) powr p"
    by simp
  have doubled_sum_power:
      "2 * ((U + V) powr p) \<le>
        2 powr p * ((U + V) powr p)"
    by (rule mult_right_mono[OF two_power_lower sum_power_nonnegative])
  have mass_to_power:
      "A + B \<le> 2 powr p * ((U + V) powr p)"
    by (rule order_trans[OF mass_sum_bound doubled_sum_power])
  have two_power_nonnegative: "0 \<le> 2 powr p"
    by simp
  have majorant_bound:
      "2 powr p * (A + B) \<le>
        2 powr p * (2 powr p * ((U + V) powr p))"
    by (rule mult_left_mono[OF mass_to_power two_power_nonnegative])
  have four_sum_power:
      "(4 * (U + V)) powr p =
        2 powr p * (2 powr p * ((U + V) powr p))"
  proof -
    have base_identity: "4 * (U + V) = 2 * (2 * (U + V))"
      by ring
    show ?thesis
      unfolding base_identity
      by (simp only: powr_mult mult.assoc)
  qed
  have majorant_to_four:
      "2 powr p * (A + B) \<le> (4 * (U + V)) powr p"
    using majorant_bound four_sum_power by simp
  have majorant_nonnegative: "0 \<le> 2 powr p * (A + B)"
    using left_mass_nonnegative right_mass_nonnegative
    by (intro mult_nonneg_nonneg) auto
  have root_bound:
      "(2 powr p * (A + B)) powr (1 / p) \<le>
        ((4 * (U + V)) powr p) powr (1 / p)"
    by (rule powr_mono2[OF inverse_exponent_nonnegative
          majorant_nonnegative majorant_to_four])
  have normalized:
      "((4 * (U + V)) powr p) powr (1 / p) = 4 * (U + V)"
    using exponent_nonzero sum_nonnegative
    by (simp add: powr_powr)
  show ?thesis
    using root_bound normalized by simp
qed

lemma slp_qstar_annular_I1_real_norm_bound:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows lp_membership:
      "aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_I1_potential delta f)"
    and norm_bound:
      "aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_I1_potential delta f) \<le>
        (9 * pi) powr (1 / aim_hls_target_exponent a) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
              slp_qstar_holder_exponent a))
            powr (1 / slp_qstar_holder_exponent a) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
proof -
  let ?q = "aim_hls_target_exponent a"
  have potential_nonnegative:
      "0 \<le> slp_qstar_annular_I1_potential delta f z" for z
    by (rule slp_qstar_annular_I1_envelope(3)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have potential_measurable:
      "slp_qstar_annular_I1_potential delta f
        \<in> borel_measurable lborel"
    by (rule slp_qstar_annular_I1_output_power(2)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have power_integrable:
      "integrable lborel
        (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q)"
    by (rule slp_qstar_annular_I1_output_power(3)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have absolute_power:
      "(\<lambda>z. abs (slp_qstar_annular_I1_potential delta f z) powr ?q) =
        (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q)"
    by (rule ext) (simp add: potential_nonnegative)
  show "aim_real_lp_on_plane ?q
      (slp_qstar_annular_I1_potential delta f)"
    unfolding aim_real_lp_on_plane_def absolute_power
    using potential_measurable power_integrable by blast
  have source_root_bound:
      "(integral\<^sup>L lborel
          (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q))
          powr (1 / ?q) \<le>
        (9 * pi) powr (1 / ?q) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
              slp_qstar_holder_exponent a))
            powr (1 / slp_qstar_holder_exponent a) *
          (integral\<^sup>L lborel
            (\<lambda>y. norm (f y) powr ?q)) powr (1 / ?q)"
    by (rule slp_qstar_annular_I1_Lp_bound(2)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  show "aim_real_lp_norm ?q
        (slp_qstar_annular_I1_potential delta f) \<le>
      (9 * pi) powr (1 / ?q) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
            slp_qstar_holder_exponent a))
          powr (1 / slp_qstar_holder_exponent a) *
        aim_complex_lp_norm ?q f"
    unfolding aim_real_lp_norm_def aim_complex_lp_norm_def absolute_power
    by (rule source_root_bound)
qed

context aim_planar_riesz_hls
begin

theorem slp_qstar_annular_combined_delta_independent:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a delta f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      0 \<le> slp_qstar_annular_combined_potential delta f z \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_combined_potential delta f) \<and>
      aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_combined_potential delta f) \<le>
        4 *
          ((9 * pi) powr (1 / aim_hls_target_exponent a) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
                slp_qstar_holder_exponent a))
              powr (1 / slp_qstar_holder_exponent a) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f +
           C / ((a - 1) * (2 - a)) *
            (integral\<^sup>L lborel
              (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f))"
proof -
  obtain C::real where C_positive: "0 < C"
    and I2_all:
      "\<forall>a delta f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
        \<longrightarrow>
        (AE z in lborel. integrable lborel
          (slp_qstar_annular_I2_weighted_integrand delta f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent a)
          (slp_qstar_annular_I2_potential delta f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent a)
            (slp_qstar_annular_I2_potential delta f)
          \<le> C / ((a - 1) * (2 - a)) *
            (integral\<^sup>L lborel
              (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f"
    using slp_qstar_annular_I2_riesz_hls by blast
  have all_combined:
      "\<forall>a delta f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      0 \<le> slp_qstar_annular_combined_potential delta f z \<and>
      aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_combined_potential delta f) \<and>
      aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_combined_potential delta f) \<le>
        4 *
          ((9 * pi) powr (1 / aim_hls_target_exponent a) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
                slp_qstar_holder_exponent a))
              powr (1 / slp_qstar_holder_exponent a) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f +
           C / ((a - 1) * (2 - a)) *
            (integral\<^sup>L lborel
              (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f)"
  proof (intro allI impI)
    fix a delta :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    have exponent_lower: "1 < a" and exponent_upper: "a < 2"
      and delta_positive: "0 < delta"
      and amplitude_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      using hypotheses by blast+
    let ?q = "aim_hls_target_exponent a"
    let ?I1 = "slp_qstar_annular_I1_potential delta f"
    let ?I2 = "slp_qstar_annular_I2_potential delta f"
    let ?combined = "slp_qstar_annular_combined_potential delta f"
    let ?U =
      "(9 * pi) powr (1 / ?q) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
            slp_qstar_holder_exponent a))
          powr (1 / slp_qstar_holder_exponent a) *
        aim_complex_lp_norm ?q f"
    let ?V =
      "C / ((a - 1) * (2 - a)) *
        (integral\<^sup>L lborel
          (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
        aim_complex_lp_norm ?q f"
    let ?A =
      "integral\<^sup>L lborel (\<lambda>x. abs (?I1 x) powr ?q)"
    let ?B =
      "integral\<^sup>L lborel (\<lambda>x. abs (?I2 x) powr ?q)"
    have q_above_one: "1 < ?q"
      using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
      by linarith
    have combined_nonnegative: "0 \<le> ?combined z"
      by (rule slp_qstar_annular_combined_Lp(1)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have combined_lp: "aim_real_lp_on_plane ?q ?combined"
      by (rule slp_qstar_annular_combined_Lp(2)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have combined_root_bound:
        "aim_real_lp_norm ?q ?combined \<le>
          (2 powr ?q * (?A + ?B)) powr (1 / ?q)"
      by (rule slp_qstar_annular_combined_Lp(3)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have I1_bound: "aim_real_lp_norm ?q ?I1 \<le> ?U"
      by (rule slp_qstar_annular_I1_real_norm_bound(2)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have I2_bound: "aim_real_lp_norm ?q ?I2 \<le> ?V"
      using I2_all hypotheses by blast
    have A_nonnegative: "0 \<le> ?A"
      by (rule integral_nonneg_AE) simp
    have B_nonnegative: "0 \<le> ?B"
      by (rule integral_nonneg_AE) simp
    have normalized_component_bound:
        "(2 powr ?q * (?A + ?B)) powr (1 / ?q) \<le>
          4 * (?U + ?V)"
      by (rule slp_two_power_root_bound[OF q_above_one A_nonnegative
            B_nonnegative])
        (use I1_bound I2_bound in
          \<open>simp_all add: aim_real_lp_norm_def\<close>)
    have final_bound:
        "aim_real_lp_norm ?q ?combined \<le> 4 * (?U + ?V)"
      using combined_root_bound normalized_component_bound by linarith
    show "0 \<le> ?combined z \<and>
        aim_real_lp_on_plane ?q ?combined \<and>
        aim_real_lp_norm ?q ?combined \<le> 4 * (?U + ?V)"
      using combined_nonnegative combined_lp final_bound by blast
  qed
  show ?thesis
    using C_positive all_combined by blast
qed

end

end
