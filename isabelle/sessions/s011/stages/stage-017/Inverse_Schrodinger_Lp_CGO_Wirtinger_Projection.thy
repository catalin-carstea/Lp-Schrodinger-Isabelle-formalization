theory Inverse_Schrodinger_Lp_CGO_Wirtinger_Projection
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Field_H1"
begin

section \<open>Exact first Wirtinger projections of the literal CGO gradients\<close>

context slp_cauchy_outer_fixed_point
begin

theorem slp_left_cgo_gradient_wirtinger_partial:
  fixes p M tau :: real
    and c :: slp_point
    and X :: "slp_point set"
    and cutoff coefficient W :: slp_scalar_field
  assumes exponent_lower: "1 < (p::real)"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and W_admissible: "slp_ae_bounded_measurable lborel M W"
  shows
    "slp_gradient_wirtinger_partial
        (slp_left_cgo_gradient tau c W
          (slp_left_outer_conjugated_gradient
            tau c cutoff coefficient W)) =
      (\<lambda>z. slp_holomorphic_quadratic_phase_multiplier tau c z *
        (\<i> * of_real tau * slp_point_as_complex (z - c) +
          cutoff z *
            slp_left_conjugated_cauchy_source tau c coefficient
              (\<lambda>y. coefficient y * W y) z))"
proof -
  note source_data = slp_both_cutoff_conjugated_sources_lp_support[OF
    exponent_lower X_open X_bounded cutoff_test coefficient_lp
    coefficient_support W_admissible]
  note outer_data = slp_both_outer_conjugated_sources_weak_wirtinger[OF
    exponent_lower]
  have outer_projection:
      "slp_gradient_wirtinger_partial
          (slp_left_outer_conjugated_gradient
            tau c cutoff coefficient W) =
        slp_oscillatory_modulation tau c
          (\<lambda>x. cutoff x *
            slp_left_conjugated_cauchy_source tau c coefficient
              (\<lambda>y. coefficient y * W y) x)"
    using outer_data source_data by blast
  show ?thesis
  proof (rule ext)
    fix z
    have outer_at:
        "slp_gradient_wirtinger_partial
            (slp_left_outer_conjugated_gradient
              tau c cutoff coefficient W) z =
          slp_center_kernel tau c z *
            (cutoff z *
              slp_left_conjugated_cauchy_source tau c coefficient
                (\<lambda>y. coefficient y * W y) z)"
      using fun_cong[OF outer_projection, of z]
      unfolding slp_oscillatory_modulation_def .
    have anti_cancel:
        "slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z *
            slp_antiholomorphic_quadratic_phase_multiplier tau c z = 1"
    proof -
      have negative_exponent:
          "\<i> * of_real ((- tau) / 2) *
              cnj ((slp_point_as_complex (z - c)) ^ 2) =
            - (\<i> * of_real (tau / 2) *
              cnj ((slp_point_as_complex (z - c)) ^ 2))"
        by (simp only: minus_divide_left[symmetric] of_real_minus
              mult_minus_right minus_mult_left)
      have exponent_cancel:
          "\<i> * of_real ((- tau) / 2) *
              cnj ((slp_point_as_complex (z - c)) ^ 2) +
            \<i> * of_real (tau / 2) *
              cnj ((slp_point_as_complex (z - c)) ^ 2) = 0"
        by (simp only: negative_exponent add.left_inverse)
      show ?thesis
        unfolding slp_antiholomorphic_quadratic_phase_multiplier_def
        by (simp only: exp_add[symmetric] exponent_cancel exp_zero)
    qed
    have phase:
        "slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z *
            slp_center_kernel tau c z =
          slp_holomorphic_quadratic_phase_multiplier tau c z"
    proof -
      have kernel:
          "slp_center_kernel tau c z =
            slp_holomorphic_quadratic_phase_multiplier tau c z *
              slp_antiholomorphic_quadratic_phase_multiplier tau c z"
        by (rule sym, rule slp_quadratic_phase_multipliers_product)
      have rearrange:
          "slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z *
              (slp_holomorphic_quadratic_phase_multiplier tau c z *
                slp_antiholomorphic_quadratic_phase_multiplier tau c z) =
            (slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z *
                slp_antiholomorphic_quadratic_phase_multiplier tau c z) *
              slp_holomorphic_quadratic_phase_multiplier tau c z"
        by (simp only: ac_simps)
      show ?thesis
        by (simp only: kernel rearrange anti_cancel mult.left_neutral)
    qed
    have axis_zero:
        "slp_point_as_complex (axis (0 :: 2) (1 :: real)) = 1"
      unfolding slp_point_as_complex_def
      by (rule complex_eqI; simp)
    have axis_one:
        "slp_point_as_complex (axis (1 :: 2) (1 :: real)) = \<i>"
      unfolding slp_point_as_complex_def
      by (rule complex_eqI; simp)
    let ?H = "slp_holomorphic_quadratic_phase_multiplier tau c z"
    let ?A =
      "slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z"
    let ?Z = "slp_point_as_complex (z - c)"
    let ?D =
      "slp_left_outer_conjugated_gradient tau c cutoff coefficient W z"
    let ?h = "?H * (\<i> * of_real tau * ?Z)"
    let ?r =
      "W z * (?A *
        (\<i> * of_real (- tau) * cnj ?Z))"
    have component_zero:
        "slp_left_cgo_gradient tau c W
            (slp_left_outer_conjugated_gradient
              tau c cutoff coefficient W) z $ 0 =
          ?h + (?A * (?D $ 0) + ?r)"
      unfolding slp_left_cgo_gradient_def
      by (simp only: vector_add_component vec_lambda_beta axis_zero
            complex_cnj_one mult.right_neutral)
    have component_one:
        "slp_left_cgo_gradient tau c W
            (slp_left_outer_conjugated_gradient
              tau c cutoff coefficient W) z $ 1 =
          ?h * \<i> + (?A * (?D $ 1) + ?r * (- \<i>))"
      unfolding slp_left_cgo_gradient_def
      by (simp only: vector_add_component vec_lambda_beta axis_one
            complex_cnj_i mult.assoc)
    have partial_algebra:
        "\<And>h a d0 d1 r :: complex.
          ((h + (a * d0 + r)) -
              \<i> * (h * \<i> + (a * d1 + r * (- \<i>)))) / 2 =
            h + a * ((d0 - \<i> * d1) / 2)"
    proof -
      fix h a d0 d1 r :: complex
      have numerator:
          "(h + (a * d0 + r)) -
              \<i> * (h * \<i> + (a * d1 + r * (- \<i>))) =
            h * 2 + a * (d0 - \<i> * d1)"
        by (simp add: algebra_simps)
      have two_nonzero: "(2 :: complex) \<noteq> 0" by simp
      show
          "((h + (a * d0 + r)) -
              \<i> * (h * \<i> + (a * d1 + r * (- \<i>)))) / 2 =
            h + a * ((d0 - \<i> * d1) / 2)"
        by (simp only: numerator times_divide_eq_right
              add_divide_eq_iff[OF two_nonzero])
    qed
    have raw_projection:
        "slp_gradient_wirtinger_partial
            (slp_left_cgo_gradient tau c W
              (slp_left_outer_conjugated_gradient
                tau c cutoff coefficient W)) z =
          slp_holomorphic_quadratic_phase_multiplier tau c z *
              (\<i> * of_real tau * slp_point_as_complex (z - c)) +
            slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z *
              slp_gradient_wirtinger_partial
                (slp_left_outer_conjugated_gradient
                  tau c cutoff coefficient W) z"
      unfolding slp_gradient_wirtinger_partial_def
      by (simp only: component_zero component_one partial_algebra)
    have phase_source:
        "slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z *
            (slp_center_kernel tau c z *
              (cutoff z *
                slp_left_conjugated_cauchy_source tau c coefficient
                  (\<lambda>y. coefficient y * W y) z)) =
          slp_holomorphic_quadratic_phase_multiplier tau c z *
            (cutoff z *
              slp_left_conjugated_cauchy_source tau c coefficient
                (\<lambda>y. coefficient y * W y) z)"
      by (simp only: mult.assoc[symmetric] phase)
    show
        "slp_gradient_wirtinger_partial
            (slp_left_cgo_gradient tau c W
              (slp_left_outer_conjugated_gradient
                tau c cutoff coefficient W)) z =
          slp_holomorphic_quadratic_phase_multiplier tau c z *
            (\<i> * of_real tau * slp_point_as_complex (z - c) +
              cutoff z *
                slp_left_conjugated_cauchy_source tau c coefficient
                  (\<lambda>y. coefficient y * W y) z)"
      by (simp only: raw_projection outer_at phase_source distrib_left)
  qed
qed

theorem slp_right_cgo_gradient_wirtinger_dbar:
  fixes p M tau :: real
    and c :: slp_point
    and X :: "slp_point set"
    and cutoff coefficient W :: slp_scalar_field
  assumes exponent_lower: "1 < (p::real)"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and W_admissible: "slp_ae_bounded_measurable lborel M W"
  shows
    "slp_gradient_wirtinger_dbar
        (slp_right_cgo_gradient tau c W
          (slp_right_outer_conjugated_gradient
            tau c cutoff coefficient W)) =
      (\<lambda>z. slp_antiholomorphic_quadratic_phase_multiplier tau c z *
        (\<i> * of_real tau * cnj (slp_point_as_complex (z - c)) +
          cutoff z *
            slp_right_conjugated_cauchy_source tau c coefficient
              (\<lambda>y. coefficient y * W y) z))"
proof -
  note source_data = slp_both_cutoff_conjugated_sources_lp_support[OF
    exponent_lower X_open X_bounded cutoff_test coefficient_lp
    coefficient_support W_admissible]
  note outer_data = slp_both_outer_conjugated_sources_weak_wirtinger[OF
    exponent_lower]
  have outer_projection:
      "slp_gradient_wirtinger_dbar
          (slp_right_outer_conjugated_gradient
            tau c cutoff coefficient W) =
        slp_oscillatory_modulation tau c
          (\<lambda>x. cutoff x *
            slp_right_conjugated_cauchy_source tau c coefficient
              (\<lambda>y. coefficient y * W y) x)"
    using outer_data source_data by blast
  show ?thesis
  proof (rule ext)
    fix z
    have outer_at:
        "slp_gradient_wirtinger_dbar
            (slp_right_outer_conjugated_gradient
              tau c cutoff coefficient W) z =
          slp_center_kernel tau c z *
            (cutoff z *
              slp_right_conjugated_cauchy_source tau c coefficient
                (\<lambda>y. coefficient y * W y) z)"
      using fun_cong[OF outer_projection, of z]
      unfolding slp_oscillatory_modulation_def .
    have holo_cancel:
        "slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
            slp_holomorphic_quadratic_phase_multiplier tau c z = 1"
    proof -
      have negative_exponent:
          "\<i> * of_real ((- tau) / 2) *
              (slp_point_as_complex (z - c)) ^ 2 =
            - (\<i> * of_real (tau / 2) *
              (slp_point_as_complex (z - c)) ^ 2)"
        by (simp only: minus_divide_left[symmetric] of_real_minus
              mult_minus_right minus_mult_left)
      have exponent_cancel:
          "\<i> * of_real ((- tau) / 2) *
              (slp_point_as_complex (z - c)) ^ 2 +
            \<i> * of_real (tau / 2) *
              (slp_point_as_complex (z - c)) ^ 2 = 0"
        by (simp only: negative_exponent add.left_inverse)
      show ?thesis
        unfolding slp_holomorphic_quadratic_phase_multiplier_def
        by (simp only: exp_add[symmetric] exponent_cancel exp_zero)
    qed
    have phase:
        "slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
            slp_center_kernel tau c z =
          slp_antiholomorphic_quadratic_phase_multiplier tau c z"
    proof -
      have kernel:
          "slp_center_kernel tau c z =
            slp_holomorphic_quadratic_phase_multiplier tau c z *
              slp_antiholomorphic_quadratic_phase_multiplier tau c z"
        by (rule sym, rule slp_quadratic_phase_multipliers_product)
      have rearrange:
          "slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
              (slp_holomorphic_quadratic_phase_multiplier tau c z *
                slp_antiholomorphic_quadratic_phase_multiplier tau c z) =
            (slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
                slp_holomorphic_quadratic_phase_multiplier tau c z) *
              slp_antiholomorphic_quadratic_phase_multiplier tau c z"
        by (simp only: ac_simps)
      show ?thesis
        by (simp only: kernel rearrange holo_cancel mult.left_neutral)
    qed
    have axis_zero:
        "slp_point_as_complex (axis (0 :: 2) (1 :: real)) = 1"
      unfolding slp_point_as_complex_def
      by (rule complex_eqI; simp)
    have axis_one:
        "slp_point_as_complex (axis (1 :: 2) (1 :: real)) = \<i>"
      unfolding slp_point_as_complex_def
      by (rule complex_eqI; simp)
    let ?H = "slp_antiholomorphic_quadratic_phase_multiplier tau c z"
    let ?A = "slp_holomorphic_quadratic_phase_multiplier (- tau) c z"
    let ?Z = "slp_point_as_complex (z - c)"
    let ?D =
      "slp_right_outer_conjugated_gradient tau c cutoff coefficient W z"
    let ?h = "?H * (\<i> * of_real tau * cnj ?Z)"
    let ?r =
      "W z * (?A *
        (\<i> * of_real (- tau) * ?Z))"
    have component_zero:
        "slp_right_cgo_gradient tau c W
            (slp_right_outer_conjugated_gradient
              tau c cutoff coefficient W) z $ 0 =
          ?h + (?A * (?D $ 0) + ?r)"
      unfolding slp_right_cgo_gradient_def
      by (simp only: vector_add_component vec_lambda_beta axis_zero
            complex_cnj_one mult.right_neutral)
    have component_one:
        "slp_right_cgo_gradient tau c W
            (slp_right_outer_conjugated_gradient
              tau c cutoff coefficient W) z $ 1 =
          ?h * (- \<i>) + (?A * (?D $ 1) + ?r * \<i>)"
      unfolding slp_right_cgo_gradient_def
      by (simp only: vector_add_component vec_lambda_beta axis_one
            complex_cnj_i mult.assoc)
    have dbar_algebra:
        "\<And>h a d0 d1 r :: complex.
          ((h + (a * d0 + r)) +
              \<i> * (h * (- \<i>) + (a * d1 + r * \<i>))) / 2 =
            h + a * ((d0 + \<i> * d1) / 2)"
    proof -
      fix h a d0 d1 r :: complex
      have numerator:
          "(h + (a * d0 + r)) +
              \<i> * (h * (- \<i>) + (a * d1 + r * \<i>)) =
            h * 2 + a * (d0 + \<i> * d1)"
        by (simp add: algebra_simps)
      have two_nonzero: "(2 :: complex) \<noteq> 0" by simp
      show
          "((h + (a * d0 + r)) +
              \<i> * (h * (- \<i>) + (a * d1 + r * \<i>))) / 2 =
            h + a * ((d0 + \<i> * d1) / 2)"
        by (simp only: numerator times_divide_eq_right
              add_divide_eq_iff[OF two_nonzero])
    qed
    have raw_projection:
        "slp_gradient_wirtinger_dbar
            (slp_right_cgo_gradient tau c W
              (slp_right_outer_conjugated_gradient
                tau c cutoff coefficient W)) z =
          slp_antiholomorphic_quadratic_phase_multiplier tau c z *
              (\<i> * of_real tau * cnj (slp_point_as_complex (z - c))) +
            slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
              slp_gradient_wirtinger_dbar
                (slp_right_outer_conjugated_gradient
                  tau c cutoff coefficient W) z"
      unfolding slp_gradient_wirtinger_dbar_def
      by (simp only: component_zero component_one dbar_algebra)
    have phase_source:
        "slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
            (slp_center_kernel tau c z *
              (cutoff z *
                slp_right_conjugated_cauchy_source tau c coefficient
                  (\<lambda>y. coefficient y * W y) z)) =
          slp_antiholomorphic_quadratic_phase_multiplier tau c z *
            (cutoff z *
              slp_right_conjugated_cauchy_source tau c coefficient
                (\<lambda>y. coefficient y * W y) z)"
      by (simp only: mult.assoc[symmetric] phase)
    show
        "slp_gradient_wirtinger_dbar
            (slp_right_cgo_gradient tau c W
              (slp_right_outer_conjugated_gradient
                tau c cutoff coefficient W)) z =
          slp_antiholomorphic_quadratic_phase_multiplier tau c z *
            (\<i> * of_real tau * cnj (slp_point_as_complex (z - c)) +
              cutoff z *
                slp_right_conjugated_cauchy_source tau c coefficient
                  (\<lambda>y. coefficient y * W y) z)"
      by (simp only: raw_projection outer_at phase_source distrib_left)
  qed
qed

end

end
