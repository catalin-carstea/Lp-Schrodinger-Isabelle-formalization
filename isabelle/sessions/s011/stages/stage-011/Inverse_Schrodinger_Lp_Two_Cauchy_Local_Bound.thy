theory Inverse_Schrodinger_Lp_Two_Cauchy_Local_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Localized_Holder"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Complex_Lp_Bounded_Multiplier"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Near_Center_Operator_Bridge"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Quantitative local bounds for cutoff Cauchy compositions\<close>

theorem slp_cauchy_local_target_holder:
  fixes f :: slp_scalar_field and z :: slp_point
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and radius_positive: "0 < R"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    and support_radius: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R"
  shows integrable: "slp_cauchy_integrable_at orientation f z"
    and bound:
      "norm (slp_cauchy_transform orientation f z) \<le>
        R powr (2 / slp_qstar_holder_exponent a - 1) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
              slp_qstar_holder_exponent a))
            powr (1 / slp_qstar_holder_exponent a) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
proof -
  have f_measurable: "f \<in> borel_measurable lborel"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
  have localized_integrable:
      "integrable lborel (slp_localized_riesz_integrand R f z)"
    by (rule slp_qstar_localized_riesz_holder(1)[OF exponent_lower
          exponent_upper radius_positive amplitude_lp])
  have integrand_norm:
      "(\<lambda>y. norm (slp_cauchy_integrand orientation f z y)) =
        slp_localized_riesz_integrand R f z"
  proof (rule ext)
    fix y :: slp_point
    show "norm (slp_cauchy_integrand orientation f z y) =
        slp_localized_riesz_integrand R f z y"
    proof (cases "f y = 0")
      case True
      then show ?thesis
        by (simp add: slp_cauchy_integrand_def
            slp_localized_riesz_integrand_def)
    next
      case False
      have kernel:
          "slp_localized_cauchy_kernel R (z - y) =
            slp_radial_inverse (z - y)"
        using slp_localized_cauchy_kernel_inside[
            OF support_radius[OF False]]
        by (simp only: slp_radial_inverse_def)
      show ?thesis
        unfolding slp_cauchy_integrand_def
          slp_localized_riesz_integrand_def kernel
        by (simp only: norm_mult slp_cauchy_kernel_norm mult.commute)
    qed
  qed
  have cauchy_integrable:
      "integrable lborel (slp_cauchy_integrand orientation f z)"
  proof (rule Bochner_Integration.integrable_bound[OF localized_integrable])
    show "slp_cauchy_integrand orientation f z \<in> borel_measurable lborel"
      by (rule slp_cauchy_integrand_borel_measurable[OF f_measurable])
    show "AE y in lborel.
        norm (slp_cauchy_integrand orientation f z y) \<le>
          norm (slp_localized_riesz_integrand R f z y)"
      using fun_cong[OF integrand_norm] by simp
  qed
  show "slp_cauchy_integrable_at orientation f z"
    unfolding slp_cauchy_integrable_at_def by (rule cauchy_integrable)
  have coefficient_le:
      "norm (inverse (of_real pi :: complex)) \<le> 1"
    using pi_ge_two
    by (simp add: norm_inverse norm_of_real inverse_le_1_iff)
  have localized_nonnegative:
      "0 \<le> integral\<^sup>L lborel (slp_localized_riesz_integrand R f z)"
    by (rule Bochner_Integration.integral_nonneg)
      (rule slp_localized_riesz_integrand_nonnegative)
  have transform_bound:
      "norm (slp_cauchy_transform orientation f z) \<le>
        integral\<^sup>L lborel (slp_localized_riesz_integrand R f z)"
  proof -
    have initial:
        "norm (slp_cauchy_transform orientation f z) \<le>
          norm (inverse (of_real pi :: complex)) *
            integral\<^sup>L lborel (slp_localized_riesz_integrand R f z)"
      using slp_cauchy_transform_norm_bound[of orientation f z]
      unfolding integrand_norm .
    have coefficient:
        "norm (inverse (of_real pi :: complex)) *
            integral\<^sup>L lborel (slp_localized_riesz_integrand R f z) \<le>
          1 * integral\<^sup>L lborel (slp_localized_riesz_integrand R f z)"
      by (rule mult_right_mono[OF coefficient_le localized_nonnegative])
    show ?thesis using initial coefficient by simp
  qed
  have holder_bound:
      "integral\<^sup>L lborel (slp_localized_riesz_integrand R f z) \<le>
        R powr (2 / slp_qstar_holder_exponent a - 1) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
              slp_qstar_holder_exponent a))
            powr (1 / slp_qstar_holder_exponent a) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
    using slp_qstar_localized_riesz_holder(2)[OF exponent_lower
        exponent_upper radius_positive amplitude_lp]
    unfolding aim_complex_lp_norm_def .
  show "norm (slp_cauchy_transform orientation f z) \<le>
      R powr (2 / slp_qstar_holder_exponent a - 1) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
            slp_qstar_holder_exponent a))
          powr (1 / slp_qstar_holder_exponent a) *
        aim_complex_lp_norm (aim_hls_target_exponent a) f"
    by (rule order_trans[OF transform_bound holder_bound])
qed

context aim_planar_hls_cauchy
begin

theorem slp_oscillatory_cauchy_hls_all_orientations:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau c f orientation.
      1 < a \<and> a < 2 \<and> aim_complex_lp_on_plane a f \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation tau c f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation tau c f)) \<le>
        C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a f)"
proof -
  obtain C :: real where positive: "0 < C"
    and base:
      "\<And>a f. 1 < a \<Longrightarrow> a < 2 \<Longrightarrow>
        aim_complex_lp_on_plane a f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_dbar_inverse f) \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_inverse f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_dbar_inverse f) \<le>
          C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a f \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_inverse f) \<le>
          C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a f"
    using slp_both_cauchy_hls by blast
  have all:
      "\<forall>a tau c f orientation.
        1 < a \<and> a < 2 \<and> aim_complex_lp_on_plane a f \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation tau c f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation tau c f)) \<le>
          C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a f"
  proof (intro allI impI)
    fix a tau c f orientation
    assume hypotheses: "1 < a \<and> a < 2 \<and> aim_complex_lp_on_plane a f"
    have lower: "1 < a" and upper: "a < 2"
      and source: "aim_complex_lp_on_plane a f"
      using hypotheses by blast+
    have modulated: "aim_complex_lp_on_plane a
        (slp_oscillatory_modulation tau c f)"
      using source by simp
    note both = base[OF lower upper modulated]
    show "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation tau c f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation tau c f)) \<le>
        C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a f"
      using both by (cases orientation) auto
  qed
  show ?thesis using positive all by blast
qed

theorem slp_two_oscillatory_cauchy_cutoff_local_bound:
  fixes cutoff :: slp_scalar_field and Y :: "slp_point set"
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and radius_positive: "0 < R"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>y. norm (cutoff y) \<le> M"
    and bound_nonnegative: "0 \<le> M"
    and support_radius:
      "\<And>z y. z \<in> Y \<Longrightarrow> cutoff y \<noteq> 0 \<Longrightarrow>
        norm (z - y) \<le> R"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau1 tau2 c1 c2 f outer inner.
      aim_complex_lp_on_plane a f \<longrightarrow>
      (\<forall>z\<in>Y.
        slp_cauchy_integrable_at outer
          (slp_oscillatory_modulation tau1 c1
            (\<lambda>y. cutoff y * slp_cauchy_transform inner
              (slp_oscillatory_modulation tau2 c2 f) y)) z \<and>
        norm (slp_cauchy_transform outer
          (slp_oscillatory_modulation tau1 c1
            (\<lambda>y. cutoff y * slp_cauchy_transform inner
              (slp_oscillatory_modulation tau2 c2 f) y)) z) \<le>
          C * aim_complex_lp_norm a f))"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?A = "R powr (2 / slp_qstar_holder_exponent a - 1) *
    (integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
        slp_qstar_holder_exponent a))
      powr (1 / slp_qstar_holder_exponent a)"
  have q_positive: "0 < ?q"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  have A_nonnegative: "0 \<le> ?A"
    by (intro mult_nonneg_nonneg powr_ge_zero)
  obtain H :: real where H_positive: "0 < H"
    and H_bound:
      "\<And>a tau c f orientation.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow>
        aim_complex_lp_on_plane a f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation tau c f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation tau c f)) \<le>
          H / ((a - 1) * (2 - a)) * aim_complex_lp_norm a f"
    using slp_oscillatory_cauchy_hls_all_orientations by blast
  let ?B = "?A * M * (H / ((a - 1) * (2 - a)))"
  let ?C = "max 1 ?B"
  have C_positive: "0 < ?C" by simp
  have all:
      "\<forall>tau1 tau2 c1 c2 f outer inner.
        aim_complex_lp_on_plane a f \<longrightarrow>
        (\<forall>z\<in>Y.
          slp_cauchy_integrable_at outer
            (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 f) y)) z \<and>
          norm (slp_cauchy_transform outer
            (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 f) y)) z) \<le>
            ?C * aim_complex_lp_norm a f)"
  proof (intro allI impI ballI)
    fix tau1 tau2 c1 c2 f outer inner z
    assume f_lp: "aim_complex_lp_on_plane a f"
      and z_in: "z \<in> Y"
    let ?u = "slp_cauchy_transform inner
      (slp_oscillatory_modulation tau2 c2 f)"
    let ?v = "\<lambda>y. cutoff y * ?u y"
    let ?w = "slp_oscillatory_modulation tau1 c1 ?v"
    have u_lp: "aim_complex_lp_on_plane ?q ?u"
      and u_bound: "aim_complex_lp_norm ?q ?u \<le>
        H / ((a - 1) * (2 - a)) * aim_complex_lp_norm a f"
      using H_bound[OF exponent_lower exponent_upper f_lp,
          where tau=tau2 and c=c2 and orientation=inner] by blast+
    have v_lp: "aim_complex_lp_on_plane ?q ?v"
      by (rule slp_complex_lp_bounded_multiplier(1)[OF q_positive
            cutoff_measurable cutoff_bound bound_nonnegative u_lp])
    have v_bound: "aim_complex_lp_norm ?q ?v \<le>
        M * aim_complex_lp_norm ?q ?u"
      by (rule slp_complex_lp_bounded_multiplier(2)[OF q_positive
            cutoff_measurable cutoff_bound bound_nonnegative u_lp])
    have w_lp: "aim_complex_lp_on_plane ?q ?w"
      using v_lp by simp
    have w_radius: "norm (z - y) \<le> R" if "?w y \<noteq> 0" for y
    proof -
      have "cutoff y \<noteq> 0"
        using that unfolding slp_oscillatory_modulation_def by auto
      then show ?thesis by (rule support_radius[OF z_in])
    qed
    have output_integrable: "slp_cauchy_integrable_at outer ?w z"
      by (rule slp_cauchy_local_target_holder(1)[OF exponent_lower
            exponent_upper radius_positive w_lp w_radius])
    have output_bound: "norm (slp_cauchy_transform outer ?w z) \<le>
        ?A * aim_complex_lp_norm ?q ?w"
      by (rule slp_cauchy_local_target_holder(2)[OF exponent_lower
            exponent_upper radius_positive w_lp w_radius])
    have first_scale:
        "?A * aim_complex_lp_norm ?q ?w \<le>
          ?A * (M * aim_complex_lp_norm ?q ?u)"
      using mult_left_mono[OF v_bound A_nonnegative] by simp
    have second_scale:
        "?A * (M * aim_complex_lp_norm ?q ?u) \<le>
          ?A * (M * (H / ((a - 1) * (2 - a)) *
            aim_complex_lp_norm a f))"
      by (rule mult_left_mono[OF
            mult_left_mono[OF u_bound bound_nonnegative] A_nonnegative])
    have raw_bound: "norm (slp_cauchy_transform outer ?w z) \<le>
        ?B * aim_complex_lp_norm a f"
      using order_trans[OF output_bound
          order_trans[OF first_scale second_scale]]
      by (simp only: mult.assoc)
    have norm_nonnegative: "0 \<le> aim_complex_lp_norm a f"
      unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
    have positive_constant_bound:
        "?B * aim_complex_lp_norm a f \<le>
          ?C * aim_complex_lp_norm a f"
      by (rule mult_right_mono[OF max.cobounded2 norm_nonnegative])
    show "slp_cauchy_integrable_at outer ?w z \<and>
        norm (slp_cauchy_transform outer ?w z) \<le>
          ?C * aim_complex_lp_norm a f"
      using output_integrable
        order_trans[OF raw_bound positive_constant_bound] by blast
  qed
  show ?thesis using C_positive all by blast
qed

end

end
