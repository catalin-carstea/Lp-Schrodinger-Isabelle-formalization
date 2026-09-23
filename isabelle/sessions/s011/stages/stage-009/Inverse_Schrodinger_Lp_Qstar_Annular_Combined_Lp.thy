theory Inverse_Schrodinger_Lp_Qstar_Annular_Combined_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_I2_Riesz_HLS"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Quantitative real Lp addition for the annular terms\<close>

lemma slp_aim_real_lp_on_plane_add_power_bound:
  assumes exponent_positive: "0 < p"
    and left_lp: "aim_real_lp_on_plane p u"
    and right_lp: "aim_real_lp_on_plane p v"
  shows sum_lp:
      "aim_real_lp_on_plane p (\<lambda>x. u x + v x)"
    and power_bound:
      "integral\<^sup>L lborel (\<lambda>x. abs (u x + v x) powr p) \<le>
        2 powr p *
          (integral\<^sup>L lborel (\<lambda>x. abs (u x) powr p) +
           integral\<^sup>L lborel (\<lambda>x. abs (v x) powr p))"
proof -
  have left_measurable: "u \<in> borel_measurable lborel"
    and left_power_integrable:
      "integrable lborel (\<lambda>x. abs (u x) powr p)"
    using left_lp unfolding aim_real_lp_on_plane_def by blast+
  have right_measurable: "v \<in> borel_measurable lborel"
    and right_power_integrable:
      "integrable lborel (\<lambda>x. abs (v x) powr p)"
    using right_lp unfolding aim_real_lp_on_plane_def by blast+
  have sum_measurable:
      "(\<lambda>x. u x + v x) \<in> borel_measurable lborel"
    using left_measurable right_measurable by measurable
  have sum_power_measurable:
      "(\<lambda>x. abs (u x + v x) powr p) \<in> borel_measurable lborel"
    using sum_measurable by measurable
  let ?majorant =
    "\<lambda>x. 2 powr p *
      (abs (u x) powr p + abs (v x) powr p)"
  have majorant_integrable: "integrable lborel ?majorant"
  proof (rule integrable_mult_right)
    assume "2 powr p \<noteq> 0"
    show "integrable lborel
        (\<lambda>x. abs (u x) powr p + abs (v x) powr p)"
      by (rule Bochner_Integration.integrable_add[OF
            left_power_integrable right_power_integrable])
  qed
  have pointwise_bound:
      "abs (u x + v x) powr p \<le> ?majorant x" for x
  proof -
    have raw:
      "norm_class.norm (u x + v x) powr p \<le>
        2 powr p *
          (norm_class.norm (u x) powr p +
           norm_class.norm (v x) powr p)"
      by (rule slp_norm_add_powr_bound)
        (use exponent_positive in simp)
    show ?thesis
      using raw by (simp only: real_norm_def)
  qed
  have sum_power_integrable:
      "integrable lborel (\<lambda>x. abs (u x + v x) powr p)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        sum_power_measurable])
    show "AE x in lborel.
        norm_class.norm (abs (u x + v x) powr p) \<le>
          norm_class.norm (?majorant x)"
    proof (rule AE_I2)
      fix x :: slp_point
      have left_nonnegative: "0 \<le> abs (u x + v x) powr p"
        by simp
      have right_nonnegative: "0 \<le> ?majorant x"
        by (intro mult_nonneg_nonneg) simp_all
      show "norm_class.norm (abs (u x + v x) powr p) \<le>
          norm_class.norm (?majorant x)"
        using pointwise_bound[of x] left_nonnegative right_nonnegative
        by (simp only: real_norm_def abs_of_nonneg)
    qed
  qed
  show "aim_real_lp_on_plane p (\<lambda>x. u x + v x)"
    unfolding aim_real_lp_on_plane_def
    using sum_measurable sum_power_integrable by blast
  have integral_bound:
      "integral\<^sup>L lborel (\<lambda>x. abs (u x + v x) powr p) \<le>
        integral\<^sup>L lborel ?majorant"
    by (rule integral_mono[OF sum_power_integrable majorant_integrable])
      (use pointwise_bound in auto)
  have majorant_integral:
      "integral\<^sup>L lborel ?majorant =
        2 powr p *
          (integral\<^sup>L lborel (\<lambda>x. abs (u x) powr p) +
           integral\<^sup>L lborel (\<lambda>x. abs (v x) powr p))"
    using left_power_integrable right_power_integrable by simp
  show "integral\<^sup>L lborel (\<lambda>x. abs (u x + v x) powr p) \<le>
      2 powr p *
        (integral\<^sup>L lborel (\<lambda>x. abs (u x) powr p) +
         integral\<^sup>L lborel (\<lambda>x. abs (v x) powr p))"
    using integral_bound majorant_integral by linarith
qed

definition slp_qstar_annular_combined_potential ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_qstar_annular_combined_potential delta f z =
    slp_qstar_annular_I1_potential delta f z +
    slp_qstar_annular_I2_potential delta f z"

lemma slp_qstar_annular_I2_potential_nonnegative:
  "0 \<le> slp_qstar_annular_I2_potential delta f z"
  unfolding slp_qstar_annular_I2_potential_def
  by (rule integral_nonneg_AE)
    (simp add: slp_qstar_annular_I2_weighted_integrand_nonnegative)

context aim_planar_riesz_hls
begin

theorem slp_qstar_annular_combined_Lp:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows combined_nonnegative:
      "0 \<le> slp_qstar_annular_combined_potential delta f z"
    and combined_lp:
      "aim_real_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_annular_combined_potential delta f)"
    and combined_norm_bound:
      "aim_real_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_annular_combined_potential delta f) \<le>
        (2 powr aim_hls_target_exponent a *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_qstar_annular_I1_potential delta f x)
              powr aim_hls_target_exponent a) +
           integral\<^sup>L lborel
            (\<lambda>x. abs (slp_qstar_annular_I2_potential delta f x)
              powr aim_hls_target_exponent a)))
          powr (1 / aim_hls_target_exponent a)"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?I1 = "slp_qstar_annular_I1_potential delta f"
  let ?I2 = "slp_qstar_annular_I2_potential delta f"
  let ?combined = "slp_qstar_annular_combined_potential delta f"
  have q_above_two:
      "2 < ?q"
    by (rule slp_qstar_exponent_relations(1)[OF exponent_lower
          exponent_upper])
  have q_positive: "0 < ?q"
    using q_above_two by linarith
  have I1_nonnegative: "0 \<le> ?I1 x" for x
    by (rule slp_qstar_annular_I1_envelope(3)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have I2_nonnegative: "0 \<le> ?I2 x" for x
    by (rule slp_qstar_annular_I2_potential_nonnegative)
  show "0 \<le> ?combined z"
    unfolding slp_qstar_annular_combined_potential_def
    using I1_nonnegative[of z] I2_nonnegative[of z] by linarith
  have I1_measurable: "?I1 \<in> borel_measurable lborel"
    by (rule slp_qstar_annular_I1_output_power(2)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have I1_power_integrable:
      "integrable lborel (\<lambda>x. ?I1 x powr ?q)"
    by (rule slp_qstar_annular_I1_output_power(3)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have I1_abs_power:
      "(\<lambda>x. abs (?I1 x) powr ?q) = (\<lambda>x. ?I1 x powr ?q)"
    by (rule ext) (simp add: I1_nonnegative)
  have I1_lp: "aim_real_lp_on_plane ?q ?I1"
    unfolding aim_real_lp_on_plane_def I1_abs_power
    using I1_measurable I1_power_integrable by blast
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
  have I2_lp: "aim_real_lp_on_plane ?q ?I2"
    using I2_all exponent_lower exponent_upper delta_positive amplitude_lp
    by blast
  have sum_data:
      "aim_real_lp_on_plane ?q (\<lambda>x. ?I1 x + ?I2 x) \<and>
       integral\<^sup>L lborel (\<lambda>x. abs (?I1 x + ?I2 x) powr ?q) \<le>
         2 powr ?q *
          (integral\<^sup>L lborel (\<lambda>x. abs (?I1 x) powr ?q) +
           integral\<^sup>L lborel (\<lambda>x. abs (?I2 x) powr ?q))"
    using slp_aim_real_lp_on_plane_add_power_bound[OF q_positive I1_lp I2_lp]
    by blast
  have combined_function:
      "?combined = (\<lambda>x. ?I1 x + ?I2 x)"
    unfolding slp_qstar_annular_combined_potential_def by (rule refl)
  have combined_membership: "aim_real_lp_on_plane ?q ?combined"
    unfolding combined_function using sum_data by blast
  show "aim_real_lp_on_plane ?q ?combined"
    by (rule combined_membership)
  have combined_power_bound:
      "integral\<^sup>L lborel (\<lambda>x. abs (?combined x) powr ?q) \<le>
        2 powr ?q *
          (integral\<^sup>L lborel (\<lambda>x. abs (?I1 x) powr ?q) +
           integral\<^sup>L lborel (\<lambda>x. abs (?I2 x) powr ?q))"
    unfolding combined_function using sum_data by blast
  have combined_mass_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (\<lambda>x. abs (?combined x) powr ?q)"
    by (rule integral_nonneg_AE) simp
  have inverse_q_nonnegative: "0 \<le> 1 / ?q"
    using q_positive by simp
  have root_bound:
      "(integral\<^sup>L lborel
          (\<lambda>x. abs (?combined x) powr ?q)) powr (1 / ?q) \<le>
        (2 powr ?q *
          (integral\<^sup>L lborel (\<lambda>x. abs (?I1 x) powr ?q) +
           integral\<^sup>L lborel (\<lambda>x. abs (?I2 x) powr ?q)))
          powr (1 / ?q)"
    by (rule powr_mono2[OF inverse_q_nonnegative
          combined_mass_nonnegative combined_power_bound])
  show "aim_real_lp_norm ?q ?combined \<le>
      (2 powr ?q *
        (integral\<^sup>L lborel (\<lambda>x. abs (?I1 x) powr ?q) +
         integral\<^sup>L lborel (\<lambda>x. abs (?I2 x) powr ?q)))
        powr (1 / ?q)"
    unfolding aim_real_lp_norm_def by (rule root_bound)
qed

end

end
