theory Inverse_Schrodinger_Lp_W1p_Pairwise_Error_Sobolev
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Coarse_Triangle"
begin

section \<open>Compact-smooth subtraction\<close>

lemma slp_test_function_on_diff:
  assumes f_test: "slp_test_function_on X f"
    and g_test: "slp_test_function_on X g"
  shows "slp_test_function_on X (\<lambda>x. f x - g x)"
proof -
  have negative_g_test:
      "slp_test_function_on X (\<lambda>x. (-1 :: complex) * g x)"
    by (rule slp_test_function_on_mult_left[OF smooth_on_const g_test])
  have difference_test:
      "slp_test_function_on X
        (\<lambda>x. f x + (-1 :: complex) * g x)"
    by (rule slp_test_function_on_add[OF f_test negative_g_test])
  show ?thesis
    using difference_test by simp
qed

lemma slp_classical_gradient_diff:
  assumes f_test: "slp_test_function_on X f"
    and g_test: "slp_test_function_on X g"
  shows "slp_classical_gradient (\<lambda>x. f x - g x) =
    (\<lambda>x. slp_classical_gradient f x - slp_classical_gradient g x)"
proof -
  have f_smooth: "smooth_on UNIV f"
    using f_test unfolding slp_test_function_on_def by blast
  have g_smooth: "smooth_on UNIV g"
    using g_test unfolding slp_test_function_on_def by blast
  have derivative_difference:
      "frechet_derivative (\<lambda>x. f x - g x) (at x) =
        (\<lambda>h. frechet_derivative f (at x) h -
          frechet_derivative g (at x) h)" for x
  proof -
    have f_differentiable: "f differentiable at x"
      using smooth_on_imp_differentiable_on[OF f_smooth]
      by (simp add: differentiable_on_def)
    have g_differentiable: "g differentiable at x"
      using smooth_on_imp_differentiable_on[OF g_smooth]
      by (simp add: differentiable_on_def)
    have f_derivative:
        "(f has_derivative frechet_derivative f (at x)) (at x)"
      using f_differentiable by (simp only: frechet_derivative_works)
    have g_derivative:
        "(g has_derivative frechet_derivative g (at x)) (at x)"
      using g_differentiable by (simp only: frechet_derivative_works)
    have difference_derivative:
        "((\<lambda>x. f x - g x) has_derivative
          (\<lambda>h. frechet_derivative f (at x) h -
            frechet_derivative g (at x) h)) (at x)"
      by (rule has_derivative_diff[OF f_derivative g_derivative])
    have difference_differentiable:
        "(\<lambda>x. f x - g x) differentiable at x"
      by (rule differentiableI[OF difference_derivative])
    have difference_frechet:
        "((\<lambda>x. f x - g x) has_derivative
          frechet_derivative (\<lambda>x. f x - g x) (at x)) (at x)"
      using difference_differentiable
      by (simp only: frechet_derivative_works)
    show ?thesis
      by (rule has_derivative_unique[OF difference_frechet
            difference_derivative])
  qed
  show ?thesis
    unfolding slp_classical_gradient_def slp_complex_partial_derivative_def
    by (rule ext) (simp add: derivative_difference vec_eq_iff)
qed

section \<open>Pairwise target-exponent control by two approximation errors\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_test_function_pairwise_error_sobolev_hls:
  "\<exists>K::real. 0 < K \<and>
    (\<forall>a X u Du f g.
      1 < a \<and> a < 2 \<and> slp_w1p_pair_on a X u Du \<and>
        slp_test_function_on X f \<and>
        slp_w1p_pair_on a X f (slp_classical_gradient f) \<and>
        slp_test_function_on X g \<and>
        slp_w1p_pair_on a X g (slp_classical_gradient g)
      \<longrightarrow>
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
              (\<lambda>x. slp_classical_gradient g x - Du x)))"
proof -
  obtain K::real where K_positive: "0 < K"
    and smooth_gain:
      "\<And>a X h. 1 < a \<Longrightarrow> a < 2 \<Longrightarrow>
        slp_test_function_on X h \<Longrightarrow>
        slp_w1p_pair_on a X h (slp_classical_gradient h) \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) h \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a) h
          \<le> K / ((a - 1) * (2 - a)) *
            slp_w1p_norm_on a X h (slp_classical_gradient h)"
    using slp_test_function_w1p_sobolev_hls by blast
  show ?thesis
  proof (intro exI[of _ K] conjI)
    show "0 < K" by (rule K_positive)
    show "\<forall>a X u Du f g.
        1 < a \<and> a < 2 \<and> slp_w1p_pair_on a X u Du \<and>
          slp_test_function_on X f \<and>
          slp_w1p_pair_on a X f (slp_classical_gradient f) \<and>
          slp_test_function_on X g \<and>
          slp_w1p_pair_on a X g (slp_classical_gradient g)
        \<longrightarrow>
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
    proof (intro allI impI)
      fix a :: real and X :: "slp_point set" and u :: slp_scalar_field
        and Du :: slp_gradient_field and f g :: slp_scalar_field
      assume hypotheses:
        "1 < a \<and> a < 2 \<and> slp_w1p_pair_on a X u Du \<and>
          slp_test_function_on X f \<and>
          slp_w1p_pair_on a X f (slp_classical_gradient f) \<and>
          slp_test_function_on X g \<and>
          slp_w1p_pair_on a X g (slp_classical_gradient g)"
      from hypotheses have a_lower: "1 < a"
        and a_upper: "a < 2"
        and rough_pair: "slp_w1p_pair_on a X u Du"
        and f_test: "slp_test_function_on X f"
        and f_pair:
          "slp_w1p_pair_on a X f (slp_classical_gradient f)"
        and g_test: "slp_test_function_on X g"
        and g_pair:
          "slp_w1p_pair_on a X g (slp_classical_gradient g)"
        by blast+
      have a_one_le: "1 \<le> a"
        using a_lower by linarith
      have difference_test:
          "slp_test_function_on X (\<lambda>x. f x - g x)"
        by (rule slp_test_function_on_diff[OF f_test g_test])
      have gradient_difference:
          "slp_classical_gradient (\<lambda>x. f x - g x) =
            (\<lambda>x. slp_classical_gradient f x -
              slp_classical_gradient g x)"
        by (rule slp_classical_gradient_diff[OF f_test g_test])
      have difference_pair_raw:
          "slp_w1p_pair_on a X (\<lambda>x. f x - g x)
            (\<lambda>x. slp_classical_gradient f x -
              slp_classical_gradient g x)"
        by (rule slp_w1p_pair_on_diff[OF a_one_le f_pair g_pair])
      have difference_pair:
          "slp_w1p_pair_on a X (\<lambda>x. f x - g x)
            (slp_classical_gradient (\<lambda>x. f x - g x))"
        using difference_pair_raw unfolding gradient_difference .
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
      have pairwise_error_bound_raw:
          "slp_w1p_norm_on a X
              (\<lambda>x. (f x - u x) - (g x - u x))
              (\<lambda>x. (slp_classical_gradient f x - Du x) -
                (slp_classical_gradient g x - Du x))
            \<le> 48 *
              (slp_w1p_norm_on a X
                  (\<lambda>x. f x - u x)
                  (\<lambda>x. slp_classical_gradient f x - Du x) +
                slp_w1p_norm_on a X
                  (\<lambda>x. g x - u x)
                  (\<lambda>x. slp_classical_gradient g x - Du x))"
        by (rule slp_w1p_norm_on_diff_coarse_triangle[
              OF a_one_le f_error_pair g_error_pair])
      have pairwise_error_bound:
          "slp_w1p_norm_on a X (\<lambda>x. f x - g x)
              (slp_classical_gradient (\<lambda>x. f x - g x))
            \<le> 48 *
              (slp_w1p_norm_on a X
                  (\<lambda>x. f x - u x)
                  (\<lambda>x. slp_classical_gradient f x - Du x) +
                slp_w1p_norm_on a X
                  (\<lambda>x. g x - u x)
                  (\<lambda>x. slp_classical_gradient g x - Du x))"
        using pairwise_error_bound_raw
        unfolding gradient_difference by simp
      have smooth_difference:
          "aim_complex_lp_on_plane (aim_hls_target_exponent a)
              (\<lambda>x. f x - g x) \<and>
            aim_complex_lp_norm (aim_hls_target_exponent a)
              (\<lambda>x. f x - g x)
              \<le> K / ((a - 1) * (2 - a)) *
                slp_w1p_norm_on a X (\<lambda>x. f x - g x)
                  (slp_classical_gradient (\<lambda>x. f x - g x))"
        by (rule smooth_gain[OF a_lower a_upper difference_test
              difference_pair])
      have denominator_positive: "0 < (a - 1) * (2 - a)"
        by (rule mult_pos_pos) (use a_lower a_upper in linarith)+
      have coefficient_nonnegative:
          "0 \<le> K / ((a - 1) * (2 - a))"
        using K_positive denominator_positive by simp
      have scaled_error_bound:
          "K / ((a - 1) * (2 - a)) *
              slp_w1p_norm_on a X (\<lambda>x. f x - g x)
                (slp_classical_gradient (\<lambda>x. f x - g x))
            \<le> K / ((a - 1) * (2 - a)) *
              (48 *
                (slp_w1p_norm_on a X
                    (\<lambda>x. f x - u x)
                    (\<lambda>x. slp_classical_gradient f x - Du x) +
                  slp_w1p_norm_on a X
                    (\<lambda>x. g x - u x)
                    (\<lambda>x. slp_classical_gradient g x - Du x)))"
        by (rule mult_left_mono[OF pairwise_error_bound
              coefficient_nonnegative])
      have final_bound:
          "aim_complex_lp_norm (aim_hls_target_exponent a)
              (\<lambda>x. f x - g x)
            \<le> K / ((a - 1) * (2 - a)) * 48 *
              (slp_w1p_norm_on a X
                  (\<lambda>x. f x - u x)
                  (\<lambda>x. slp_classical_gradient f x - Du x) +
                slp_w1p_norm_on a X
                  (\<lambda>x. g x - u x)
                  (\<lambda>x. slp_classical_gradient g x - Du x))"
      proof (rule order_trans[OF conjunct2[OF smooth_difference]])
        show "K / ((a - 1) * (2 - a)) *
                slp_w1p_norm_on a X (\<lambda>x. f x - g x)
                  (slp_classical_gradient (\<lambda>x. f x - g x))
              \<le> K / ((a - 1) * (2 - a)) * 48 *
                (slp_w1p_norm_on a X
                    (\<lambda>x. f x - u x)
                    (\<lambda>x. slp_classical_gradient f x - Du x) +
                  slp_w1p_norm_on a X
                    (\<lambda>x. g x - u x)
                    (\<lambda>x. slp_classical_gradient g x - Du x))"
          using scaled_error_bound by (simp add: algebra_simps)
      qed
      show "aim_complex_lp_on_plane (aim_hls_target_exponent a)
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
        using conjunct1[OF smooth_difference] final_bound by blast
    qed
  qed
qed

end

end
