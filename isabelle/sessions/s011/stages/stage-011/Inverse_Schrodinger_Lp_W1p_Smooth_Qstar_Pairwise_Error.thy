theory Inverse_Schrodinger_Lp_W1p_Smooth_Qstar_Pairwise_Error
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Zero_Pair_Partial_Psi_Pointwise_Limit"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Smooth_Terminal_Exponent_HLS"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Guarded subtraction for the literal partial-qstar operator\<close>

lemma slp_partial_psi_inverse_diff_test_function:
  assumes f_test: "slp_test_function_on UNIV f"
    and g_test: "slp_test_function_on UNIV g"
  shows "(\<lambda>z. slp_partial_psi_inverse tau c f z -
      slp_partial_psi_inverse tau c g z) =
    slp_partial_psi_inverse tau c (\<lambda>x. f x - g x)"
proof (rule ext)
  fix z :: slp_point
  have f_modulated_test:
      "slp_test_function_on UNIV (slp_oscillatory_modulation tau c f)"
    unfolding slp_oscillatory_modulation_def
    by (rule slp_test_function_on_mult_left[OF
          slp_center_kernel_smooth f_test])
  have g_modulated_test:
      "slp_test_function_on UNIV (slp_oscillatory_modulation tau c g)"
    unfolding slp_oscillatory_modulation_def
    by (rule slp_test_function_on_mult_left[OF
          slp_center_kernel_smooth g_test])
  have f_integrable:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c f) z)"
    using slp_test_function_cauchy_integrable_at[OF
      f_modulated_test, of SLP_Partial_Inverse z]
    unfolding slp_cauchy_integrable_at_def .
  have g_integrable:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c g) z)"
    using slp_test_function_cauchy_integrable_at[OF
      g_modulated_test, of SLP_Partial_Inverse z]
    unfolding slp_cauchy_integrable_at_def .
  have integrand_diff:
      "slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c (\<lambda>x. f x - g x)) z =
        (\<lambda>y. slp_cauchy_integrand SLP_Partial_Inverse
              (slp_oscillatory_modulation tau c f) z y -
            slp_cauchy_integrand SLP_Partial_Inverse
              (slp_oscillatory_modulation tau c g) z y)"
    by (rule ext)
      (simp add: slp_cauchy_integrand_def
        slp_oscillatory_modulation_def algebra_simps)
  have integral_diff:
      "integral\<^sup>L lborel
          (slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c (\<lambda>x. f x - g x)) z) =
        integral\<^sup>L lborel
          (slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c f) z) -
        integral\<^sup>L lborel
          (slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c g) z)"
    unfolding integrand_diff
    by (rule Bochner_Integration.integral_diff[OF f_integrable g_integrable])
  show "slp_partial_psi_inverse tau c f z -
      slp_partial_psi_inverse tau c g z =
    slp_partial_psi_inverse tau c (\<lambda>x. f x - g x) z"
  proof -
    have scaled_difference:
        "inverse (of_real pi) *
              integral\<^sup>L lborel
                (slp_cauchy_integrand SLP_Partial_Inverse
                  (slp_oscillatory_modulation tau c f) z) -
            inverse (of_real pi) *
              integral\<^sup>L lborel
                (slp_cauchy_integrand SLP_Partial_Inverse
                  (slp_oscillatory_modulation tau c g) z) =
          inverse (of_real pi) *
            (integral\<^sup>L lborel
                (slp_cauchy_integrand SLP_Partial_Inverse
                  (slp_oscillatory_modulation tau c f) z) -
              integral\<^sup>L lborel
                (slp_cauchy_integrand SLP_Partial_Inverse
                  (slp_oscillatory_modulation tau c g) z))"
      by (simp add: algebra_simps)
    have integral_presentation:
        "integral\<^sup>L lborel
              (slp_cauchy_integrand SLP_Partial_Inverse
                (slp_oscillatory_modulation tau c f) z) -
            integral\<^sup>L lborel
              (slp_cauchy_integrand SLP_Partial_Inverse
                (slp_oscillatory_modulation tau c g) z) =
          integral\<^sup>L lborel
            (slp_cauchy_integrand SLP_Partial_Inverse
              (slp_oscillatory_modulation tau c (\<lambda>x. f x - g x)) z)"
      by (rule sym[OF integral_diff])
    show ?thesis
      unfolding slp_partial_psi_inverse_def slp_cauchy_transform_def
      using scaled_difference integral_presentation by simp
  qed
qed

section \<open>Pairwise smooth qstar control by Sobolev approximation errors\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_test_function_pairwise_error_partial_psi_gain:
  fixes a :: real and X :: "slp_point set"
    and u :: slp_scalar_field and Du :: slp_gradient_field
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and rough_pair: "slp_w1p_pair_on a X u Du"
  shows "\<exists>B::real. 0 < B \<and>
    (\<forall>tau R c f g.
      2 \<le> tau \<and> 1 \<le> R * sqrt tau \<and>
        slp_test_function_on X f \<and>
        slp_w1p_pair_on a X f (slp_classical_gradient f) \<and>
        slp_test_function_on X g \<and>
        slp_w1p_pair_on a X g (slp_classical_gradient g) \<and>
        (\<forall>y. f y - g y \<noteq> 0 \<longrightarrow>
          norm_class.norm (y - c) \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (\<lambda>z. slp_partial_psi_inverse tau c f z -
          slp_partial_psi_inverse tau c g z) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>z. slp_partial_psi_inverse tau c f z -
            slp_partial_psi_inverse tau c g z)
        \<le> B * inverse (sqrt tau) *
          (slp_w1p_norm_on a X
              (\<lambda>x. f x - u x)
              (\<lambda>x. slp_classical_gradient f x - Du x) +
            slp_w1p_norm_on a X
              (\<lambda>x. g x - u x)
              (\<lambda>x. slp_classical_gradient g x - Du x)))"
proof -
  obtain C::real where C_positive: "0 < C"
    and terminal:
      "\<And>s tau R c h.
        2 < s \<Longrightarrow> 2 \<le> tau \<Longrightarrow>
        1 \<le> R * sqrt tau \<Longrightarrow>
        slp_test_function_on UNIV h \<Longrightarrow>
        aim_complex_lp_on_plane s h \<Longrightarrow>
        aim_complex_lp_on_plane (slp_hls_source_exponent s)
          (slp_classical_wirtinger_partial h) \<Longrightarrow>
        aim_complex_lp_on_plane (slp_hls_source_exponent s)
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (h x))) \<Longrightarrow>
        (\<And>y. h y \<noteq> 0 \<Longrightarrow>
          norm_class.norm (y - c) \<le> R) \<Longrightarrow>
        aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c h) \<and>
        aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c h) \<and>
        aim_complex_lp_norm s (slp_partial_psi_inverse tau c h)
          \<le> C /
              ((slp_hls_source_exponent s - 1) *
                (2 - slp_hls_source_exponent s)) *
              inverse (sqrt tau) *
            (2 * aim_complex_lp_norm s h +
              aim_complex_lp_norm (slp_hls_source_exponent s)
                (slp_classical_wirtinger_partial h)) \<and>
        aim_complex_lp_norm s (slp_dbar_psi_inverse tau c h)
          \<le> C /
              ((slp_hls_source_exponent s - 1) *
                (2 - slp_hls_source_exponent s)) *
              inverse (sqrt tau) *
            (2 * aim_complex_lp_norm s h +
              aim_complex_lp_norm (slp_hls_source_exponent s)
                (slp_classical_wirtinger_partial (\<lambda>x. cnj (h x))))"
    using slp_qstar_smooth_terminal_exponent_inverse_sqrt_hls by blast
  obtain K::real where K_positive: "0 < K"
    and target_error:
      "\<And>a X u Du f g.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow>
        slp_w1p_pair_on a X u Du \<Longrightarrow>
        slp_test_function_on X f \<Longrightarrow>
        slp_w1p_pair_on a X f (slp_classical_gradient f) \<Longrightarrow>
        slp_test_function_on X g \<Longrightarrow>
        slp_w1p_pair_on a X g (slp_classical_gradient g) \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (\<lambda>x. f x - g x) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (\<lambda>x. f x - g x)
          \<le> K / ((a - 1) * (2 - a)) * 48 *
            (slp_w1p_norm_on a X
                (\<lambda>x. f x - u x)
                (\<lambda>x. slp_classical_gradient f x - Du x) +
              slp_w1p_norm_on a X
                (\<lambda>x. g x - u x)
                (\<lambda>x. slp_classical_gradient g x - Du x))"
    using slp_test_function_pairwise_error_sobolev_hls by blast
  let ?d = "(a - 1) * (2 - a)"
  let ?B = "C / ?d * (2 * (K / ?d * 48) + 4 * 48)"
  have denominator_positive: "0 < ?d"
    by (rule mult_pos_pos) (use a_lower a_upper in linarith)+
  have C_div_positive: "0 < C / ?d"
    by (rule divide_pos_pos[OF C_positive denominator_positive])
  have K_div_positive: "0 < K / ?d"
    by (rule divide_pos_pos[OF K_positive denominator_positive])
  have inner_coefficient_positive:
      "0 < 2 * (K / ?d * 48) + 4 * 48"
    using K_div_positive by linarith
  have B_positive: "0 < ?B"
    by (rule mult_pos_pos[OF C_div_positive inner_coefficient_positive])
  show ?thesis
  proof (intro exI[of _ ?B] conjI allI impI)
    show "0 < ?B"
      by (rule B_positive)
    fix tau R c f g
    assume hypotheses:
      "2 \<le> tau \<and> 1 \<le> R * sqrt tau \<and>
        slp_test_function_on X f \<and>
        slp_w1p_pair_on a X f (slp_classical_gradient f) \<and>
        slp_test_function_on X g \<and>
        slp_w1p_pair_on a X g (slp_classical_gradient g) \<and>
        (\<forall>y. f y - g y \<noteq> 0 \<longrightarrow>
          norm_class.norm (y - c) \<le> R)"
    from hypotheses have tau_lower: "2 \<le> tau"
      and normalized_lower: "1 \<le> R * sqrt tau"
      and f_test: "slp_test_function_on X f"
      and f_pair: "slp_w1p_pair_on a X f (slp_classical_gradient f)"
      and g_test: "slp_test_function_on X g"
      and g_pair: "slp_w1p_pair_on a X g (slp_classical_gradient g)"
      and support: "\<And>y. f y - g y \<noteq> 0 \<Longrightarrow>
        norm_class.norm (y - c) \<le> R"
      by blast+
    let ?h = "\<lambda>x. f x - g x"
    let ?E =
      "slp_w1p_norm_on a X
          (\<lambda>x. f x - u x)
          (\<lambda>x. slp_classical_gradient f x - Du x) +
        slp_w1p_norm_on a X
          (\<lambda>x. g x - u x)
          (\<lambda>x. slp_classical_gradient g x - Du x)"
    have a_positive: "0 < a"
      using a_lower by linarith
    have a_one_le: "1 \<le> a"
      using a_lower by linarith
    have h_test: "slp_test_function_on X ?h"
      by (rule slp_test_function_on_diff[OF f_test g_test])
    have h_test_UNIV: "slp_test_function_on UNIV ?h"
      using h_test unfolding slp_test_function_on_def by blast
    have gradient_difference:
        "slp_classical_gradient ?h =
          (\<lambda>x. slp_classical_gradient f x -
            slp_classical_gradient g x)"
      by (rule slp_classical_gradient_diff[OF f_test g_test])
    have h_pair_raw:
        "slp_w1p_pair_on a X ?h
          (\<lambda>x. slp_classical_gradient f x -
            slp_classical_gradient g x)"
      by (rule slp_w1p_pair_on_diff[OF a_one_le f_pair g_pair])
    have h_pair:
        "slp_w1p_pair_on a X ?h (slp_classical_gradient ?h)"
      using h_pair_raw unfolding gradient_difference .
    have f_error_pair:
        "slp_w1p_pair_on a X
          (\<lambda>x. f x - u x)
          (\<lambda>x. slp_classical_gradient f x - Du x)"
      by (rule slp_w1p_pair_on_diff[OF a_one_le f_pair rough_pair])
    have g_error_pair:
        "slp_w1p_pair_on a X
          (\<lambda>x. g x - u x)
          (\<lambda>x. slp_classical_gradient g x - Du x)"
      by (rule slp_w1p_pair_on_diff[OF a_one_le g_pair rough_pair])
    have h_w1p_bound_raw:
        "slp_w1p_norm_on a X
            (\<lambda>x. (f x - u x) - (g x - u x))
            (\<lambda>x. (slp_classical_gradient f x - Du x) -
              (slp_classical_gradient g x - Du x))
          \<le> 48 * ?E"
      by (rule slp_w1p_norm_on_diff_coarse_triangle[OF a_one_le
            f_error_pair g_error_pair])
    have h_w1p_bound:
        "slp_w1p_norm_on a X ?h (slp_classical_gradient ?h)
          \<le> 48 * ?E"
      using h_w1p_bound_raw unfolding gradient_difference by simp
    have target_data:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?h \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a) ?h
            \<le> K / ?d * 48 * ?E"
      by (rule target_error[OF a_lower a_upper rough_pair f_test f_pair
            g_test g_pair])
    have gradient_zero:
        "(\<lambda>x. slp_classical_gradient ?h x $ 0) =
          slp_complex_partial_derivative ?h 0"
      by (rule ext) (simp add: slp_classical_gradient_def)
    have gradient_one:
        "(\<lambda>x. slp_classical_gradient ?h x $ 1) =
          slp_complex_partial_derivative ?h 1"
      by (rule ext) (simp add: slp_classical_gradient_def)
    have derivative_zero_restriction:
        "slp_restrict_field X
            (\<lambda>x. slp_classical_gradient ?h x $ 0) =
          slp_complex_partial_derivative ?h 0"
      unfolding gradient_zero
      by (rule slp_test_function_partial_restrict_field_eq[OF h_test])
    have derivative_one_restriction:
        "slp_restrict_field X
            (\<lambda>x. slp_classical_gradient ?h x $ 1) =
          slp_complex_partial_derivative ?h 1"
      unfolding gradient_one
      by (rule slp_test_function_partial_restrict_field_eq[OF h_test])
    note components = slp_w1p_norm_on_component_bounds[OF a_positive h_pair]
    have derivative_zero_lp:
        "aim_complex_lp_on_plane a (slp_complex_partial_derivative ?h 0)"
      using components(2) unfolding derivative_zero_restriction by blast
    have derivative_one_lp:
        "aim_complex_lp_on_plane a (slp_complex_partial_derivative ?h 1)"
      using components(3) unfolding derivative_one_restriction by blast
    have derivative_zero_bound:
        "aim_complex_lp_norm a (slp_complex_partial_derivative ?h 0)
          \<le> slp_w1p_norm_on a X ?h (slp_classical_gradient ?h)"
      using components(2) unfolding derivative_zero_restriction by blast
    have derivative_one_bound:
        "aim_complex_lp_norm a (slp_complex_partial_derivative ?h 1)
          \<le> slp_w1p_norm_on a X ?h (slp_classical_gradient ?h)"
      using components(3) unfolding derivative_one_restriction by blast
    note partial = slp_classical_wirtinger_partial_lp_coordinate_bound[
      OF a_one_le derivative_zero_lp derivative_one_lp]
    have coordinate_sum_bound:
        "aim_complex_lp_norm a (slp_complex_partial_derivative ?h 0) +
            aim_complex_lp_norm a (slp_complex_partial_derivative ?h 1)
          \<le> slp_w1p_norm_on a X ?h (slp_classical_gradient ?h) +
            slp_w1p_norm_on a X ?h (slp_classical_gradient ?h)"
      by (rule add_mono[OF derivative_zero_bound derivative_one_bound])
    have partial_w1p_bound:
        "aim_complex_lp_norm a (slp_classical_wirtinger_partial ?h)
          \<le> 4 * slp_w1p_norm_on a X ?h (slp_classical_gradient ?h)"
    proof (rule order_trans[OF partial(2)])
      have scaled_coordinate_sum_bound:
          "2 * (aim_complex_lp_norm a
                (slp_complex_partial_derivative ?h 0) +
              aim_complex_lp_norm a
                (slp_complex_partial_derivative ?h 1))
            \<le> 2 *
              (slp_w1p_norm_on a X ?h (slp_classical_gradient ?h) +
                slp_w1p_norm_on a X ?h (slp_classical_gradient ?h))"
        by (rule mult_left_mono[OF coordinate_sum_bound]) simp
      show "2 * (aim_complex_lp_norm a
              (slp_complex_partial_derivative ?h 0) +
            aim_complex_lp_norm a
              (slp_complex_partial_derivative ?h 1))
          \<le> 4 * slp_w1p_norm_on a X ?h (slp_classical_gradient ?h)"
        using scaled_coordinate_sum_bound by simp
    qed
    have partial_error_bound:
        "aim_complex_lp_norm a (slp_classical_wirtinger_partial ?h)
          \<le> 4 * 48 * ?E"
    proof (rule order_trans[OF partial_w1p_bound])
      have scaled_h_w1p:
          "4 * slp_w1p_norm_on a X ?h (slp_classical_gradient ?h)
            \<le> 4 * (48 * ?E)"
        by (rule mult_left_mono[OF h_w1p_bound]) simp
      show "4 * slp_w1p_norm_on a X ?h (slp_classical_gradient ?h)
          \<le> 4 * 48 * ?E"
        using scaled_h_w1p by (simp only: mult.assoc)
    qed
    have conjugate_h_test:
        "slp_test_function_on UNIV (\<lambda>x. cnj (?h x))"
      by (rule iffD2[OF slp_test_function_on_cnj_iff])
        (rule h_test_UNIV)
    have conjugate_partial_test:
        "slp_test_function_on UNIV
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (?h x)))"
      by (rule slp_classical_wirtinger_partial_test_function[OF
            conjugate_h_test])
    have conjugate_partial_lp:
        "aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (?h x)))"
      by (rule slp_test_function_aim_complex_lp_on_plane[OF a_positive
            conjugate_partial_test])
    have target_above_two: "2 < aim_hls_target_exponent a"
      by (rule slp_qstar_exponent_relations(1)[OF a_lower a_upper])
    have source_identity:
        "slp_hls_source_exponent (aim_hls_target_exponent a) = a"
      unfolding slp_hls_source_exponent_def aim_hls_target_exponent_def
      using a_lower a_upper
      by (simp add: divide_simps algebra_simps)
    have partial_source_lp:
        "aim_complex_lp_on_plane
          (slp_hls_source_exponent (aim_hls_target_exponent a))
          (slp_classical_wirtinger_partial ?h)"
      using partial(1) by (simp only: source_identity)
    have conjugate_partial_source_lp:
        "aim_complex_lp_on_plane
          (slp_hls_source_exponent (aim_hls_target_exponent a))
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (?h x)))"
      using conjugate_partial_lp by (simp only: source_identity)
    have terminal_raw:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c ?h) \<and>
          aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_dbar_psi_inverse tau c ?h) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_psi_inverse tau c ?h)
            \<le> C /
                ((slp_hls_source_exponent (aim_hls_target_exponent a) - 1) *
                  (2 - slp_hls_source_exponent
                    (aim_hls_target_exponent a))) * inverse (sqrt tau) *
              (2 * aim_complex_lp_norm (aim_hls_target_exponent a) ?h +
                aim_complex_lp_norm
                  (slp_hls_source_exponent (aim_hls_target_exponent a))
                  (slp_classical_wirtinger_partial ?h)) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_dbar_psi_inverse tau c ?h)
            \<le> C /
                ((slp_hls_source_exponent (aim_hls_target_exponent a) - 1) *
                  (2 - slp_hls_source_exponent
                    (aim_hls_target_exponent a))) * inverse (sqrt tau) *
              (2 * aim_complex_lp_norm (aim_hls_target_exponent a) ?h +
                aim_complex_lp_norm
                  (slp_hls_source_exponent (aim_hls_target_exponent a))
                  (slp_classical_wirtinger_partial (\<lambda>x. cnj (?h x))))"
      by (rule terminal[OF target_above_two tau_lower normalized_lower
            h_test_UNIV conjunct1[OF target_data] partial_source_lp
            conjugate_partial_source_lp])
        (rule support)
    have terminal_data:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c ?h) \<and>
          aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_dbar_psi_inverse tau c ?h) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_psi_inverse tau c ?h)
            \<le> C / ?d * inverse (sqrt tau) *
              (2 * aim_complex_lp_norm (aim_hls_target_exponent a) ?h +
                aim_complex_lp_norm a
                  (slp_classical_wirtinger_partial ?h)) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_dbar_psi_inverse tau c ?h)
            \<le> C / ?d * inverse (sqrt tau) *
              (2 * aim_complex_lp_norm (aim_hls_target_exponent a) ?h +
                aim_complex_lp_norm a
                  (slp_classical_wirtinger_partial (\<lambda>x. cnj (?h x))))"
      using terminal_raw
      by (simp only: source_identity)
    have inner_bound:
        "2 * aim_complex_lp_norm (aim_hls_target_exponent a) ?h +
            aim_complex_lp_norm a (slp_classical_wirtinger_partial ?h)
          \<le> (2 * (K / ?d * 48) + 4 * 48) * ?E"
    proof -
      have target_scaled:
          "2 * aim_complex_lp_norm (aim_hls_target_exponent a) ?h
            \<le> 2 * (K / ?d * 48 * ?E)"
        by (rule mult_left_mono[OF conjunct2[OF target_data]]) simp
      note combined = add_mono[OF target_scaled partial_error_bound]
      show ?thesis
        using combined by (simp add: algebra_simps)
    qed
    have tau_positive: "0 < tau"
      using tau_lower by linarith
    have outer_nonnegative:
        "0 \<le> C / ?d * inverse (sqrt tau)"
      by (rule mult_nonneg_nonneg)
        (use C_div_positive in linarith, use tau_positive in simp)
    have scaled_inner:
        "C / ?d * inverse (sqrt tau) *
            (2 * aim_complex_lp_norm (aim_hls_target_exponent a) ?h +
              aim_complex_lp_norm a (slp_classical_wirtinger_partial ?h))
          \<le> C / ?d * inverse (sqrt tau) *
            ((2 * (K / ?d * 48) + 4 * 48) * ?E)"
      by (rule mult_left_mono[OF inner_bound outer_nonnegative])
    have coefficient_presentation:
        "C / ?d * inverse (sqrt tau) *
            ((2 * (K / ?d * 48) + 4 * 48) * ?E) =
          ?B * inverse (sqrt tau) * ?E"
      by (simp only: mult.assoc mult.commute mult.left_commute)
    have scaled_final:
        "C / ?d * inverse (sqrt tau) *
            (2 * aim_complex_lp_norm (aim_hls_target_exponent a) ?h +
              aim_complex_lp_norm a (slp_classical_wirtinger_partial ?h))
          \<le> ?B * inverse (sqrt tau) * ?E"
      by (rule order_trans[OF scaled_inner])
        (simp only: coefficient_presentation)
    have h_output_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c ?h)
          \<le> ?B * inverse (sqrt tau) * ?E"
      by (rule order_trans[OF
            terminal_data[THEN conjunct2, THEN conjunct2, THEN conjunct1]
            scaled_final])
    have f_test_UNIV: "slp_test_function_on UNIV f"
      using f_test unfolding slp_test_function_on_def by blast
    have g_test_UNIV: "slp_test_function_on UNIV g"
      using g_test unfolding slp_test_function_on_def by blast
    have output_difference:
        "(\<lambda>z. slp_partial_psi_inverse tau c f z -
            slp_partial_psi_inverse tau c g z) =
          slp_partial_psi_inverse tau c ?h"
      by (rule slp_partial_psi_inverse_diff_test_function[OF
            f_test_UNIV g_test_UNIV])
    have output_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (\<lambda>z. slp_partial_psi_inverse tau c f z -
            slp_partial_psi_inverse tau c g z)"
      using terminal_data[THEN conjunct1]
      unfolding output_difference .
    have output_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a)
            (\<lambda>z. slp_partial_psi_inverse tau c f z -
              slp_partial_psi_inverse tau c g z)
          \<le> ?B * inverse (sqrt tau) * ?E"
      using h_output_bound
      unfolding output_difference .
    show "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (\<lambda>z. slp_partial_psi_inverse tau c f z -
            slp_partial_psi_inverse tau c g z)"
      by (rule output_lp)
    show "aim_complex_lp_norm (aim_hls_target_exponent a)
            (\<lambda>z. slp_partial_psi_inverse tau c f z -
              slp_partial_psi_inverse tau c g z)
          \<le> ?B * inverse (sqrt tau) * ?E"
      by (rule output_bound)
  qed
qed

end

end
