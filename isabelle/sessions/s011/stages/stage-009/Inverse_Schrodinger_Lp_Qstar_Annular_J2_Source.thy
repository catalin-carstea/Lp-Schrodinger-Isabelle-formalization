theory Inverse_Schrodinger_Lp_Qstar_Annular_J2_Source
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_J1_Lp_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Squared_Radial_Annulus_Power_Geometric"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Quantitative_Complex_Holder"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The full-annulus inverse-square source for the far-output term\<close>

definition slp_qstar_annular_J2_coefficient ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_qstar_annular_J2_coefficient delta R y =
    (if delta \<le> norm y \<and> norm y \<le> R then
      of_real (slp_radial_inverse_square y)
    else 0)"

definition slp_qstar_annular_J2_source ::
  "real \<Rightarrow> real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_qstar_annular_J2_source delta R f y =
    slp_qstar_annular_J2_coefficient delta R y * f y"

definition slp_qstar_annular_J2_unit_coefficient_mass :: real
where
  "slp_qstar_annular_J2_unit_coefficient_mass =
    inverse (1 - (2::real) powr (-2)) *
      integral\<^sup>L lborel
        (slp_squared_radial_annulus_power 2 1 2)"

lemma slp_qstar_annular_J2_coefficient_measurable[measurable]:
  "slp_qstar_annular_J2_coefficient delta R
    \<in> borel_measurable lborel"
  unfolding slp_qstar_annular_J2_coefficient_def by measurable

lemma slp_qstar_annular_J2_coefficient_norm_square:
  "norm_class.norm (slp_qstar_annular_J2_coefficient delta R y) powr 2 =
    slp_squared_radial_annulus_power 2 delta R y"
  unfolding slp_qstar_annular_J2_coefficient_def
    slp_squared_radial_annulus_power_def
    slp_squared_radial_annulus_def
  by (simp add: powr_realpow power2_eq_square)

lemma slp_qstar_annular_J2_unit_coefficient_mass_nonnegative:
  "0 \<le> slp_qstar_annular_J2_unit_coefficient_mass"
proof -
  have ratio_less: "(2::real) powr (-2) < 1"
    using slp_squared_radial_annulus_power_ratio_bounds(2)[of 2]
    by simp
  have inverse_nonnegative:
      "0 \<le> inverse (1 - (2::real) powr (-2))"
    using ratio_less by simp
  have unit_mass_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (slp_squared_radial_annulus_power 2 1 2)"
    by (rule Bochner_Integration.integral_nonneg) simp
  show ?thesis
    unfolding slp_qstar_annular_J2_unit_coefficient_mass_def
    by (rule mult_nonneg_nonneg[OF inverse_nonnegative
          unit_mass_nonnegative])
qed

theorem slp_qstar_annular_J2_source_bound:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and radius_lower: "delta \<le> R"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows coefficient_lp:
      "aim_complex_lp_on_plane 2
        (slp_qstar_annular_J2_coefficient delta R)"
    and coefficient_mass_bound:
      "integral\<^sup>L lborel
          (\<lambda>y. norm_class.norm
            (slp_qstar_annular_J2_coefficient delta R y) powr 2) \<le>
        delta powr (-2) * slp_qstar_annular_J2_unit_coefficient_mass"
    and coefficient_norm_bound:
      "aim_complex_lp_norm 2
          (slp_qstar_annular_J2_coefficient delta R) \<le>
        (1 / delta) *
          slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2)"
    and source_lp:
      "aim_complex_lp_on_plane a
        (slp_qstar_annular_J2_source delta R f)"
    and source_power_bound:
      "integral\<^sup>L lborel
          (\<lambda>y. norm_class.norm
            (slp_qstar_annular_J2_source delta R f y) powr a) \<le>
        (integral\<^sup>L lborel
          (\<lambda>y. norm_class.norm
            (slp_qstar_annular_J2_coefficient delta R y) powr 2))
            powr (a / 2) *
        (integral\<^sup>L lborel
          (\<lambda>y. norm_class.norm (f y) powr
            aim_hls_target_exponent a)) powr
              (a / aim_hls_target_exponent a)"
    and source_norm_bound:
      "aim_complex_lp_norm a
          (slp_qstar_annular_J2_source delta R f) \<le>
        (1 / delta) *
          slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?coefficient = "slp_qstar_annular_J2_coefficient delta R"
  let ?source = "slp_qstar_annular_J2_source delta R f"
  let ?K = "slp_qstar_annular_J2_unit_coefficient_mass"
  let ?C = "integral\<^sup>L lborel
    (\<lambda>y. norm_class.norm (?coefficient y) powr 2)"
  let ?F = "integral\<^sup>L lborel
    (\<lambda>y. norm_class.norm (f y) powr ?q)"
  have a_positive: "0 < a" and a_nonzero: "a \<noteq> 0"
    using exponent_lower by linarith+
  have delta_nonzero: "delta \<noteq> 0"
    using delta_positive by simp
  have q_above_two: "2 < ?q"
    by (rule slp_qstar_exponent_relations(1)[OF exponent_lower
          exponent_upper])
  have q_positive: "0 < ?q" and q_nonzero: "?q \<noteq> 0"
    using q_above_two by linarith+
  have first_scale_lower: "1 < 2 / a"
    using exponent_upper a_positive
    by (simp add: less_divide_eq)
  have second_scale_lower: "1 < ?q / a"
    using q_above_two exponent_upper a_positive
    by (simp add: less_divide_eq)
  have reciprocal_target:
      "1 / ?q = 1 / a - 1 / 2"
    by (rule slp_hls_target_exponent_reciprocal[OF exponent_lower
          exponent_upper])
  have conjugate_scales:
      "1 / (2 / a) + 1 / (?q / a) = 1"
  proof -
    have reciprocal_sum: "1 / 2 + 1 / ?q = 1 / a"
      using reciprocal_target by linarith
    have divide_scales:
        "1 / (2 / a) + 1 / (?q / a) = a / 2 + a / ?q"
      using a_nonzero q_nonzero by simp
    have factor_scale:
        "a / 2 + a / ?q = a * (1 / 2 + 1 / ?q)"
      by (simp add: algebra_simps)
    have final_scale: "a * (1 / 2 + 1 / ?q) = 1"
      by (simp add: reciprocal_sum a_nonzero)
    show ?thesis
      using divide_scales factor_scale final_scale by simp
  qed

  have coefficient_power_eq:
      "(\<lambda>y. norm_class.norm (?coefficient y) powr 2) =
        slp_squared_radial_annulus_power 2 delta R"
    by (rule ext, rule slp_qstar_annular_J2_coefficient_norm_square)
  have coefficient_power_integrable:
      "integrable lborel
        (\<lambda>y. norm_class.norm (?coefficient y) powr 2)"
    unfolding coefficient_power_eq
    by (rule slp_squared_radial_annulus_power_integrable[OF
          delta_positive]) simp
  have coefficient_measurable:
      "?coefficient \<in> borel_measurable lborel"
    by measurable
  have coefficient_membership:
      "aim_complex_lp_on_plane 2 ?coefficient"
    unfolding aim_complex_lp_on_plane_def
    using coefficient_measurable coefficient_power_integrable by blast
  show coefficient_lp:
      "aim_complex_lp_on_plane 2 ?coefficient"
    by (rule coefficient_membership)

  have coefficient_mass_upper:
      "?C \<le> delta powr (-2) * ?K"
  proof -
    note geometric =
      slp_squared_radial_annulus_power_rescaled_geometric_majorant[
        OF delta_positive radius_lower, of 2]
    show ?thesis
      unfolding coefficient_power_eq
        slp_qstar_annular_J2_unit_coefficient_mass_def
      using geometric by simp
  qed
  show coefficient_mass_bound:
      "?C \<le> delta powr (-2) * ?K"
    by (rule coefficient_mass_upper)

  have coefficient_mass_nonnegative: "0 \<le> ?C"
    by (rule integral_nonneg_AE) simp
  have coefficient_root_upper:
      "?C powr (1 / 2) \<le> (1 / delta) * ?K powr (1 / 2)"
  proof -
    have lifted:
        "?C powr (1 / 2) \<le>
          (delta powr (-2) * ?K) powr (1 / 2)"
      by (rule powr_mono2[OF _ coefficient_mass_nonnegative
            coefficient_mass_upper]) simp
    have scaled_root:
        "(delta powr (-2) * ?K) powr (1 / 2) =
          (1 / delta) * ?K powr (1 / 2)"
    proof -
      have product_root:
          "(delta powr (-2) * ?K) powr (1 / 2) =
            (delta powr (-2)) powr (1 / 2) *
              ?K powr (1 / 2)"
        by (rule powr_mult)
      have exponent_identity: "(-2::real) * (1 / 2) = -1"
        by simp
      have scale_root:
          "(delta powr (-2)) powr (1 / 2) = delta powr (-1)"
        by (simp only: powr_powr exponent_identity)
      have inverse_scale: "delta powr (-1) = 1 / delta"
      proof -
        have "delta powr (-1) = inverse (delta powr 1)"
          by (simp only: powr_minus)
        also have "... = inverse delta"
          using delta_positive by simp
        also have "... = 1 / delta"
          by (simp add: divide_inverse)
        finally show ?thesis .
      qed
      show ?thesis
        by (simp only: product_root scale_root inverse_scale)
    qed
    show ?thesis
      using lifted scaled_root by simp
  qed
  show coefficient_norm_bound:
      "aim_complex_lp_norm 2 ?coefficient \<le>
        (1 / delta) * ?K powr (1 / 2)"
    unfolding aim_complex_lp_norm_def
    by (rule coefficient_root_upper)

  have amplitude_measurable: "f \<in> borel_measurable lborel"
    and amplitude_power_integrable:
      "integrable lborel
        (\<lambda>y. norm_class.norm (f y) powr ?q)"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast+
  have source_measurable:
      "?source \<in> borel_measurable lborel"
    unfolding slp_qstar_annular_J2_source_def
    using coefficient_measurable amplitude_measurable by measurable
  let ?kpower = "\<lambda>y. norm_class.norm (?coefficient y) powr a"
  let ?fpower = "\<lambda>y. norm_class.norm (f y) powr a"
  have kpower_measurable: "?kpower \<in> borel_measurable lborel"
    using coefficient_measurable by measurable
  have fpower_measurable: "?fpower \<in> borel_measurable lborel"
    using amplitude_measurable by measurable
  have kpower_nonnegative: "0 \<le> ?kpower y" for y by simp
  have fpower_nonnegative: "0 \<le> ?fpower y" for y by simp
  have kpower_scaled_eq:
      "(\<lambda>y. ?kpower y powr (2 / a)) =
        (\<lambda>y. norm_class.norm (?coefficient y) powr 2)"
  proof (rule ext)
    fix y :: slp_point
    show "?kpower y powr (2 / a) =
        norm_class.norm (?coefficient y) powr 2"
      using a_nonzero by (simp add: powr_powr)
  qed
  have fpower_scaled_eq:
      "(\<lambda>y. ?fpower y powr (?q / a)) =
        (\<lambda>y. norm_class.norm (f y) powr ?q)"
  proof (rule ext)
    fix y :: slp_point
    show "?fpower y powr (?q / a) =
        norm_class.norm (f y) powr ?q"
      using a_nonzero by (simp add: powr_powr)
  qed
  have kpower_scaled_integrable:
      "integrable lborel (\<lambda>y. ?kpower y powr (2 / a))"
    unfolding kpower_scaled_eq
    by (rule coefficient_power_integrable)
  have fpower_scaled_integrable:
      "integrable lborel (\<lambda>y. ?fpower y powr (?q / a))"
    unfolding fpower_scaled_eq
    by (rule amplitude_power_integrable)
  note holder = slp_nonnegative_holder_integral[OF first_scale_lower
      second_scale_lower conjugate_scales kpower_measurable
      fpower_measurable kpower_nonnegative fpower_nonnegative
      kpower_scaled_integrable fpower_scaled_integrable]
  have source_power_eq:
      "(\<lambda>y. norm_class.norm (?source y) powr a) =
        (\<lambda>y. ?kpower y * ?fpower y)"
    unfolding slp_qstar_annular_J2_source_def
    by (rule ext) (simp add: norm_mult powr_mult)
  have source_power_integrable_fact:
      "integrable lborel
        (\<lambda>y. norm_class.norm (?source y) powr a)"
    unfolding source_power_eq by (rule holder(1))
  have source_membership:
      "aim_complex_lp_on_plane a ?source"
    unfolding aim_complex_lp_on_plane_def
    using source_measurable source_power_integrable_fact by blast
  show source_lp:
      "aim_complex_lp_on_plane a ?source"
    by (rule source_membership)
  have holder_bound:
      "integral\<^sup>L lborel
          (\<lambda>y. norm_class.norm (?source y) powr a) \<le>
        ?C powr (a / 2) * ?F powr (a / ?q)"
  proof -
    note raw = holder(2)
    show ?thesis
      using raw a_nonzero q_nonzero
      unfolding source_power_eq kpower_scaled_eq fpower_scaled_eq
      by simp
  qed
  show source_power_bound:
      "integral\<^sup>L lborel
          (\<lambda>y. norm_class.norm (?source y) powr a) \<le>
        ?C powr (a / 2) * ?F powr (a / ?q)"
    by (rule holder_bound)

  have F_nonnegative: "0 \<le> ?F"
    by (rule integral_nonneg_AE) simp
  have source_mass_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (\<lambda>y. norm_class.norm (?source y) powr a)"
    by (rule integral_nonneg_AE) simp
  have raised_bound:
      "(integral\<^sup>L lborel
          (\<lambda>y. norm_class.norm (?source y) powr a)) powr (1 / a) \<le>
        (?C powr (a / 2) * ?F powr (a / ?q)) powr (1 / a)"
    by (rule powr_mono2[OF _ source_mass_nonnegative holder_bound])
      (use a_positive in simp)
  have root_identity:
      "(?C powr (a / 2) * ?F powr (a / ?q)) powr (1 / a) =
        ?C powr (1 / 2) * ?F powr (1 / ?q)"
    using coefficient_mass_nonnegative F_nonnegative a_nonzero q_nonzero
    by (simp add: powr_mult powr_powr)
  have source_root_bound:
      "aim_complex_lp_norm a ?source \<le>
        ?C powr (1 / 2) * aim_complex_lp_norm ?q f"
    using raised_bound
    unfolding aim_complex_lp_norm_def
    by (simp only: root_identity)
  have amplitude_norm_nonnegative:
      "0 \<le> aim_complex_lp_norm ?q f"
    unfolding aim_complex_lp_norm_def by simp
  have scaled_product:
      "?C powr (1 / 2) * aim_complex_lp_norm ?q f \<le>
        ((1 / delta) * ?K powr (1 / 2)) *
          aim_complex_lp_norm ?q f"
    by (rule mult_right_mono[OF coefficient_root_upper
          amplitude_norm_nonnegative])
  show source_norm_bound:
      "aim_complex_lp_norm a ?source \<le>
        (1 / delta) * ?K powr (1 / 2) *
          aim_complex_lp_norm ?q f"
    by (rule order_trans[OF source_root_bound])
      (use scaled_product in simp)
qed

end
