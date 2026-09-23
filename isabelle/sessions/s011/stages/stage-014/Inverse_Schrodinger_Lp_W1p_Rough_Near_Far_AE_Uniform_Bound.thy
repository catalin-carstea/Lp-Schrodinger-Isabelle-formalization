theory Inverse_Schrodinger_Lp_W1p_Rough_Near_Far_AE_Uniform_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Complete_Derivative_Uniform"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Near_Far_Split"
begin

section \<open>Almost-everywhere arbitrary-output near/far control\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_partial_psi_inverse_rough_AE_uniform_bound:
  fixes b A R delta tau :: real
    and X :: "slp_point set"
    and u :: slp_scalar_field
    and Du :: slp_gradient_field
    and c :: slp_point
  assumes tau_positive: "0 < tau"
    and exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and relative_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
    and X_measurable: "X \<in> sets lborel"
    and delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows total_integrable:
      "\<And>z :: slp_point. z \<in> X \<Longrightarrow>
        slp_cauchy_integrable_at SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c
            (slp_restrict_field X u)) z"
    and uniform_bound:
      "(let
          P = Real_Vector_Spaces.norm
            (inverse (of_real pi :: complex));
          K = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q);
          W = slp_w1p_norm_on b X u Du;
          M = K * (192 * W);
          C = 6 * integral\<^sup>L lborel
              (slp_localized_cauchy_kernel 1) +
            2 * unit_ball_vol 2;
          N = P * M * delta * C;
          B = (2 / delta) * M;
          DB = K * ((2 / delta) * (4 * W));
          CB = ((P * slp_global_cutoff_L / delta) * M) * C;
          SB = P * M *
            ((1 / delta) *
                integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
              (1 / delta) * (1 + log 2 (R / delta)) *
                integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2))
        in
          AE z in lborel. z \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm
              (slp_partial_psi_inverse tau c
                (slp_restrict_field X u) z) \<le>
            N + (1 / tau) * (B + (DB + (CB + SB))))"
proof -
  let ?f = "slp_restrict_field X u"
  let ?near =
    "slp_global_cutoff.slp_near_cutoff_amplitude delta c ?f"
  let ?far = "slp_global_far_cutoff_amplitude delta c ?f"
  let ?a = "slp_global_far_coefficient delta c"
  let ?v = "\<lambda>x. ?a x * u x"
  let ?Dv = "\<lambda>x. \<chi> i.
    ?a x * Du x $ i +
    u x * slp_complex_partial_derivative ?a i x"
  let ?F =
    "slp_restrict_field X
      (slp_gradient_wirtinger_partial ?Dv)"
  let ?P =
    "Real_Vector_Spaces.norm (inverse (of_real pi :: complex))"
  let ?K =
    "?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)"
  let ?W = "slp_w1p_norm_on b X u Du"
  let ?M = "?K * (192 * ?W)"
  let ?C =
    "6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
      2 * unit_ball_vol 2"
  let ?N = "?P * ?M * delta * ?C"
  let ?B = "(2 / delta) * ?M"
  let ?DB = "?K * ((2 / delta) * (4 * ?W))"
  let ?CB = "((?P * slp_global_cutoff_L / delta) * ?M) * ?C"
  let ?SB =
    "?P * ?M *
      ((1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        (1 / delta) * (1 + log 2 (R / delta)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"

  have X_bounded: "bounded X"
    unfolding bounded_iff
  proof (rule exI[of _ A], intro ballI)
    fix y :: slp_point
    assume y_in: "y \<in> X"
    show "Real_Vector_Spaces.norm y \<le> A"
      by (rule set_radius[OF y_in])
  qed
  have pair: "slp_w1p_pair_on b X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have restricted_lp: "aim_complex_lp_on_plane b ?f"
    using pair
    unfolding slp_w1p_pair_on_def slp_complex_lp_on_def by blast
  have f_measurable: "?f \<in> borel_measurable lborel"
    using restricted_lp unfolding aim_complex_lp_on_plane_def by blast
  have M_nonnegative: "0 \<le> ?M"
  proof (rule mult_nonneg_nonneg)
    show "0 \<le> ?K" by simp
    show "0 \<le> 192 * ?W"
      unfolding slp_w1p_norm_on_def by simp
  qed
  have f_bound:
      "AE z in (lborel :: slp_point measure).
        Real_Vector_Spaces.norm (?f z) \<le> ?M"
    unfolding q_def
    by (rule slp_w1p_zero_pair_AE_pointwise_bound_on_bounded_set[
          OF exponent_above_two radius_nonnegative set_radius zero_pair])
  note near = slp_global_near_partial_psi_inverse_AE_uniform_bound[
    OF delta_positive f_measurable M_nonnegative f_bound,
      where tau=tau and c=c]

  have exponent_one_le: "1 \<le> b"
    using exponent_above_two by linarith
  have product_zero_pair: "slp_w1p_zero_pair_on b X ?v ?Dv"
    by (rule slp_w1p_zero_pair_on_global_far_coefficient[
          OF exponent_one_le X_measurable X_bounded delta_positive zero_pair])
  have product_pair: "slp_w1p_pair_on b X ?v ?Dv"
    using product_zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have doubled_radius_nonnegative: "0 \<le> 2 * A"
    using radius_nonnegative by simp

  have far_integrable_at:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c ?far) z"
    if z_in: "z \<in> X" for z :: slp_point
  proof -
    have support_radius:
        "Real_Vector_Spaces.norm (z - y) \<le> 2 * A"
      if y_in: "y \<in> X" for y :: slp_point
    proof -
      have z_bound: "Real_Vector_Spaces.norm z \<le> A"
        by (rule set_radius[OF z_in])
      have y_bound: "Real_Vector_Spaces.norm y \<le> A"
        by (rule set_radius[OF y_in])
      have triangle:
          "Real_Vector_Spaces.norm (z - y) \<le>
            Real_Vector_Spaces.norm z + Real_Vector_Spaces.norm y"
        by (rule norm_triangle_ineq4)
      show ?thesis using triangle z_bound y_bound by linarith
    qed
    have source_integrable:
        "slp_cauchy_integrable_at SLP_Partial_Inverse
          (\<lambda>x. (slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * slp_restrict_field X ?v x) z"
      by (rule slp_w1p_rough_far_target_cauchy_integrable(1)[
            OF exponent_above_two doubled_radius_nonnegative product_pair
              support_radius])
    have source_eq:
        "(\<lambda>x. (slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * slp_restrict_field X ?v x) =
          slp_oscillatory_modulation tau c ?far"
      by (rule slp_w1p_global_far_modulated_source_eq[OF delta_positive])
    show ?thesis using source_integrable unfolding source_eq .
  qed

  have amplitude_split: "?f = (\<lambda>y. ?near y + ?far y)"
  proof (rule ext)
    fix y :: slp_point
    show "?f y = ?near y + ?far y"
      unfolding slp_global_cutoff.slp_near_cutoff_amplitude_def
        slp_global_far_cutoff_amplitude_def slp_global_scaled_cutoff_def
      by (simp add: algebra_simps)
  qed
  have modulated_split:
      "slp_oscillatory_modulation tau c ?f =
        (\<lambda>y. slp_oscillatory_modulation tau c ?near y +
          slp_oscillatory_modulation tau c ?far y)"
  proof (rule ext)
    fix y :: slp_point
    have pointwise_split: "?f y = ?near y + ?far y"
      using fun_cong[OF amplitude_split, of y] .
    show "slp_oscillatory_modulation tau c ?f y =
        slp_oscillatory_modulation tau c ?near y +
          slp_oscillatory_modulation tau c ?far y"
      unfolding slp_oscillatory_modulation_def
      apply (subst pointwise_split)
      by (rule distrib_left)
  qed

  have total_integrable_at:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c ?f) z"
    if z_in: "z \<in> X" for z :: slp_point
  proof -
    have sum_integrable:
        "slp_cauchy_integrable_at SLP_Partial_Inverse
          (\<lambda>y. slp_oscillatory_modulation tau c ?near y +
            slp_oscillatory_modulation tau c ?far y) z"
      by (rule slp_cauchy_integrable_at_add[
            OF near(1) far_integrable_at[OF z_in]])
    show ?thesis unfolding modulated_split by (rule sum_integrable)
  qed
  show "\<And>z :: slp_point. z \<in> X \<Longrightarrow>
      slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c ?f) z"
    by (rule total_integrable_at)

  have operator_split_at:
      "slp_partial_psi_inverse tau c ?f z =
        slp_partial_psi_inverse tau c ?near z +
          slp_partial_psi_inverse tau c ?far z"
    if z_in: "z \<in> X" for z :: slp_point
  proof -
    have far_integrable:
        "slp_cauchy_integrable_at SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c ?far) z"
      by (rule far_integrable_at[OF z_in])
    have transform_split:
        "slp_cauchy_transform SLP_Partial_Inverse
            (\<lambda>y. slp_oscillatory_modulation tau c ?near y +
              slp_oscillatory_modulation tau c ?far y) z =
          slp_cauchy_transform SLP_Partial_Inverse
              (slp_oscillatory_modulation tau c ?near) z +
            slp_cauchy_transform SLP_Partial_Inverse
              (slp_oscillatory_modulation tau c ?far) z"
      by (rule slp_cauchy_transform_add[OF near(1) far_integrable])
    show ?thesis
      apply (subst slp_partial_psi_inverse_eq)
      apply (subst slp_partial_psi_inverse_eq)
      apply (subst slp_partial_psi_inverse_eq)
      apply (subst modulated_split)
      by (rule transform_split)
  qed

  note far_AE =
    slp_w1p_zero_pair_partial_psi_inverse_rough_global_far_AE[
      OF tau_positive exponent_above_two X_measurable X_bounded
        delta_positive zero_pair,
      where c=c]
  show "(let
      P = Real_Vector_Spaces.norm
        (inverse (of_real pi :: complex));
      K = P *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
            powr (1 / q);
      W = slp_w1p_norm_on b X u Du;
      M = K * (192 * W);
      C = 6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        2 * unit_ball_vol 2;
      N = P * M * delta * C;
      B = (2 / delta) * M;
      DB = K * ((2 / delta) * (4 * W));
      CB = ((P * slp_global_cutoff_L / delta) * M) * C;
      SB = P * M *
        ((1 / delta) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
          (1 / delta) * (1 + log 2 (R / delta)) *
            integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))
    in
      AE z in lborel. z \<in> X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c (slp_restrict_field X u) z) \<le>
        N + (1 / tau) * (B + (DB + (CB + SB))))"
    unfolding Let_def
  proof (use far_AE f_bound in eventually_elim)
    fix z :: slp_point
    assume far_identity:
        "slp_partial_psi_inverse tau c ?far z =
          (1 / (\<i> * of_real tau)) *
            (slp_center_kernel tau c z *
                slp_restrict_field X ?v z -
              slp_partial_psi_inverse tau c ?F z)"
      and pointwise_bound:
        "Real_Vector_Spaces.norm (?f z) \<le> ?M"
    have pointwise_conclusion:
        "Real_Vector_Spaces.norm
            (slp_partial_psi_inverse tau c ?f z) \<le>
          ?N + (1 / tau) * (?B + (?DB + (?CB + ?SB)))"
      if z_in: "z \<in> X"
    proof -
      have near_bound:
          "Real_Vector_Spaces.norm
              (slp_partial_psi_inverse tau c ?near z) \<le> ?N"
        by (rule near(2))
      note complete =
        slp_w1p_global_far_complete_derivative_uniform_bound[
          OF exponent_above_two radius_nonnegative set_radius
            relative_radius z_in delta_positive normalized_lower zero_pair,
          folded q_def, where tau=tau]
      have derivative_bound:
          "Real_Vector_Spaces.norm
              (slp_partial_psi_inverse tau c ?F z) \<le>
            ?DB + (?CB + ?SB)"
        by (rule complete(2))
      have restrict_product_at:
          "slp_restrict_field X ?v z = ?a z * ?f z"
        by (simp add: slp_restrict_field_def)
      have coefficient_bound:
          "Real_Vector_Spaces.norm (?a z) \<le> 2 / delta"
        by (rule slp_global_far_coefficient_norm_bound[OF delta_positive])
      have two_over_delta_nonnegative: "0 \<le> 2 / delta"
        using delta_positive by simp
      have boundary_norm:
          "Real_Vector_Spaces.norm
              (slp_center_kernel tau c z *
                slp_restrict_field X ?v z) =
            Real_Vector_Spaces.norm (?a z) *
              Real_Vector_Spaces.norm (?f z)"
        by (simp add: restrict_product_at norm_mult)
      have boundary_bound:
          "Real_Vector_Spaces.norm
              (slp_center_kernel tau c z *
                slp_restrict_field X ?v z) \<le> ?B"
        unfolding boundary_norm
        by (rule mult_mono[OF coefficient_bound pointwise_bound])
          (use two_over_delta_nonnegative in simp_all)
      have bracket_triangle:
          "Real_Vector_Spaces.norm
              (slp_center_kernel tau c z *
                  slp_restrict_field X ?v z -
                slp_partial_psi_inverse tau c ?F z) \<le>
            Real_Vector_Spaces.norm
                (slp_center_kernel tau c z *
                  slp_restrict_field X ?v z) +
              Real_Vector_Spaces.norm
                (slp_partial_psi_inverse tau c ?F z)"
        by (rule norm_triangle_ineq4)
      have bracket_bound:
          "Real_Vector_Spaces.norm
              (slp_center_kernel tau c z *
                  slp_restrict_field X ?v z -
                slp_partial_psi_inverse tau c ?F z) \<le>
            ?B + (?DB + (?CB + ?SB))"
        by (rule order_trans[OF bracket_triangle
              add_mono[OF boundary_bound derivative_bound]])
      have scalar_norm:
          "Real_Vector_Spaces.norm
              (1 / (\<i> * of_real tau) :: complex) = 1 / tau"
        using tau_positive
        by (simp only: norm_divide norm_one norm_mult norm_ii
              norm_of_real abs_of_pos)
      have far_bound:
          "Real_Vector_Spaces.norm
              (slp_partial_psi_inverse tau c ?far z) \<le>
            (1 / tau) * (?B + (?DB + (?CB + ?SB)))"
        unfolding far_identity norm_mult scalar_norm
        by (rule mult_left_mono[OF bracket_bound])
          (use tau_positive in simp)
      have full_triangle:
          "Real_Vector_Spaces.norm
              (slp_partial_psi_inverse tau c ?f z) \<le>
            Real_Vector_Spaces.norm
                (slp_partial_psi_inverse tau c ?near z) +
              Real_Vector_Spaces.norm
                (slp_partial_psi_inverse tau c ?far z)"
        unfolding operator_split_at[OF z_in]
        by (rule norm_triangle_ineq)
      have summed_bound:
          "Real_Vector_Spaces.norm
                (slp_partial_psi_inverse tau c ?near z) +
              Real_Vector_Spaces.norm
                (slp_partial_psi_inverse tau c ?far z) \<le>
            ?N + (1 / tau) * (?B + (?DB + (?CB + ?SB)))"
        by (rule add_mono[OF near_bound far_bound])
      show "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?f z) \<le>
          ?N + (1 / tau) * (?B + (?DB + (?CB + ?SB)))"
        by (rule order_trans[OF full_triangle summed_bound])
    qed
    show "z \<in> X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?f z) \<le>
        ?N + (1 / tau) * (?B + (?DB + (?CB + ?SB)))"
      by (intro impI, rule pointwise_conclusion)
  qed
qed

end

end
