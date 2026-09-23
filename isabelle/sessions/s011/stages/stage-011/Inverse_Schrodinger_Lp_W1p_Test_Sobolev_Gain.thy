theory Inverse_Schrodinger_Lp_W1p_Test_Sobolev_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Component_Norm_Bounds"
begin

section \<open>Restriction identities for compact-smooth functions\<close>

lemma slp_test_function_restrict_field_eq:
  assumes f_test: "slp_test_function_on X f"
  shows "slp_restrict_field X f = f"
proof (rule ext)
  fix x :: slp_point
  have support_within: "closure {x. f x \<noteq> 0} \<subseteq> X"
    using f_test unfolding slp_test_function_on_def by blast
  have nonzero_within: "{x. f x \<noteq> 0} \<subseteq> X"
    using closure_subset support_within by blast
  show "slp_restrict_field X f x = f x"
    unfolding slp_restrict_field_def
    using nonzero_within by auto
qed

lemma slp_test_function_partial_restrict_field_eq:
  assumes f_test: "slp_test_function_on X f"
  shows "slp_restrict_field X (slp_complex_partial_derivative f i) =
    slp_complex_partial_derivative f i"
  by (rule slp_test_function_restrict_field_eq[OF
        slp_test_function_on_partial_derivative[OF f_test]])

section \<open>Compact-smooth Sobolev gain in the reviewed coordinate norm\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_test_function_w1p_sobolev_hls:
  "\<exists>K::real. 0 < K \<and>
    (\<forall>a X f.
      1 < a \<and> a < 2 \<and> slp_test_function_on X f \<and>
        slp_w1p_pair_on a X f (slp_classical_gradient f)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a) f
        \<le> K / ((a - 1) * (2 - a)) *
          slp_w1p_norm_on a X f (slp_classical_gradient f))"
proof -
  obtain C::real where C_positive: "0 < C"
    and smooth_gain:
      "\<And>a X f. 1 < a \<Longrightarrow> a < 2 \<Longrightarrow>
        slp_test_function_on X f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a) f
          \<le> C / ((a - 1) * (2 - a)) *
            aim_complex_lp_norm a (slp_classical_wirtinger_partial f)"
    using slp_test_function_planar_sobolev_hls by blast
  show ?thesis
  proof (intro exI[of _ "4 * C"] conjI)
    show "0 < 4 * C"
      using C_positive by simp
    show "\<forall>a X f.
        1 < a \<and> a < 2 \<and> slp_test_function_on X f \<and>
          slp_w1p_pair_on a X f (slp_classical_gradient f)
        \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a) f
          \<le> (4 * C) / ((a - 1) * (2 - a)) *
            slp_w1p_norm_on a X f (slp_classical_gradient f)"
    proof (intro allI impI)
      fix a :: real and X :: "slp_point set" and f :: slp_scalar_field
      assume hypotheses:
        "1 < a \<and> a < 2 \<and> slp_test_function_on X f \<and>
          slp_w1p_pair_on a X f (slp_classical_gradient f)"
      from hypotheses have a_lower: "1 < a"
        and a_upper: "a < 2"
        and f_test: "slp_test_function_on X f"
        and f_pair: "slp_w1p_pair_on a X f (slp_classical_gradient f)"
        by blast+
      have a_positive: "0 < a"
        using a_lower by linarith
      have a_one_le: "1 \<le> a"
        using a_lower by linarith
      have gradient_zero:
          "(\<lambda>x. slp_classical_gradient f x $ 0) =
            slp_complex_partial_derivative f 0"
        by (rule ext) (simp add: slp_classical_gradient_def)
      have gradient_one:
          "(\<lambda>x. slp_classical_gradient f x $ 1) =
            slp_complex_partial_derivative f 1"
        by (rule ext) (simp add: slp_classical_gradient_def)
      have derivative_zero_restriction:
          "slp_restrict_field X
              (\<lambda>x. slp_classical_gradient f x $ 0) =
            slp_complex_partial_derivative f 0"
        unfolding gradient_zero
        by (rule slp_test_function_partial_restrict_field_eq[OF f_test])
      have derivative_one_restriction:
          "slp_restrict_field X
              (\<lambda>x. slp_classical_gradient f x $ 1) =
            slp_complex_partial_derivative f 1"
        unfolding gradient_one
        by (rule slp_test_function_partial_restrict_field_eq[OF f_test])
      note components = slp_w1p_norm_on_component_bounds[OF a_positive f_pair]
      have derivative_zero_lp:
          "aim_complex_lp_on_plane a
            (slp_complex_partial_derivative f 0)"
        using components(2) unfolding derivative_zero_restriction by blast
      have derivative_one_lp:
          "aim_complex_lp_on_plane a
            (slp_complex_partial_derivative f 1)"
        using components(3) unfolding derivative_one_restriction by blast
      have derivative_zero_bound:
          "aim_complex_lp_norm a (slp_complex_partial_derivative f 0)
            \<le> slp_w1p_norm_on a X f (slp_classical_gradient f)"
        using components(2) unfolding derivative_zero_restriction by blast
      have derivative_one_bound:
          "aim_complex_lp_norm a (slp_complex_partial_derivative f 1)
            \<le> slp_w1p_norm_on a X f (slp_classical_gradient f)"
        using components(3) unfolding derivative_one_restriction by blast
      note partial = slp_classical_wirtinger_partial_lp_coordinate_bound[
        OF a_one_le derivative_zero_lp derivative_one_lp]
      have partial_bound:
          "aim_complex_lp_norm a (slp_classical_wirtinger_partial f)
            \<le> 4 * slp_w1p_norm_on a X f (slp_classical_gradient f)"
      proof (rule order_trans[OF partial(2)])
        have coordinate_sum_bound:
            "aim_complex_lp_norm a (slp_complex_partial_derivative f 0) +
                aim_complex_lp_norm a (slp_complex_partial_derivative f 1)
              \<le> slp_w1p_norm_on a X f (slp_classical_gradient f) +
                slp_w1p_norm_on a X f (slp_classical_gradient f)"
          by (rule add_mono[OF derivative_zero_bound derivative_one_bound])
        have scaled_coordinate_sum_bound:
            "2 * (aim_complex_lp_norm a
                  (slp_complex_partial_derivative f 0) +
                aim_complex_lp_norm a
                  (slp_complex_partial_derivative f 1))
              \<le> 2 *
                (slp_w1p_norm_on a X f (slp_classical_gradient f) +
                  slp_w1p_norm_on a X f (slp_classical_gradient f))"
          by (rule mult_left_mono[OF coordinate_sum_bound]) simp
        show "2 * (aim_complex_lp_norm a
                (slp_complex_partial_derivative f 0) +
              aim_complex_lp_norm a
                (slp_complex_partial_derivative f 1))
            \<le> 4 * slp_w1p_norm_on a X f (slp_classical_gradient f)"
          using scaled_coordinate_sum_bound by simp
      qed
      have smooth:
          "aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
            aim_complex_lp_norm (aim_hls_target_exponent a) f
              \<le> C / ((a - 1) * (2 - a)) *
                aim_complex_lp_norm a (slp_classical_wirtinger_partial f)"
        by (rule smooth_gain[OF a_lower a_upper f_test])
      have smooth_lp:
          "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
        by (rule conjunct1[OF smooth])
      have smooth_bound:
          "aim_complex_lp_norm (aim_hls_target_exponent a) f
            \<le> C / ((a - 1) * (2 - a)) *
              aim_complex_lp_norm a (slp_classical_wirtinger_partial f)"
        by (rule conjunct2[OF smooth])
      have denominator_positive: "0 < (a - 1) * (2 - a)"
        by (rule mult_pos_pos) (use a_lower a_upper in linarith)+
      have coefficient_nonnegative:
          "0 \<le> C / ((a - 1) * (2 - a))"
        using C_positive denominator_positive by simp
      have scaled_partial_bound:
          "C / ((a - 1) * (2 - a)) *
              aim_complex_lp_norm a (slp_classical_wirtinger_partial f)
            \<le> C / ((a - 1) * (2 - a)) *
              (4 * slp_w1p_norm_on a X f (slp_classical_gradient f))"
        by (rule mult_left_mono[OF partial_bound coefficient_nonnegative])
      have final_bound:
          "aim_complex_lp_norm (aim_hls_target_exponent a) f
            \<le> (4 * C) / ((a - 1) * (2 - a)) *
              slp_w1p_norm_on a X f (slp_classical_gradient f)"
      proof (rule order_trans[OF smooth_bound])
        show "C / ((a - 1) * (2 - a)) *
              aim_complex_lp_norm a (slp_classical_wirtinger_partial f)
            \<le> (4 * C) / ((a - 1) * (2 - a)) *
              slp_w1p_norm_on a X f (slp_classical_gradient f)"
          using scaled_partial_bound by (simp add: algebra_simps)
      qed
      show "aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a) f
          \<le> (4 * C) / ((a - 1) * (2 - a)) *
            slp_w1p_norm_on a X f (slp_classical_gradient f)"
        using smooth_lp final_bound by blast
    qed
  qed
qed

end

end
