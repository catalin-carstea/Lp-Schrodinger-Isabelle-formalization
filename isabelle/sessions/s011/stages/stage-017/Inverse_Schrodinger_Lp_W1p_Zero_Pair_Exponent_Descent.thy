theory Inverse_Schrodinger_Lp_W1p_Zero_Pair_Exponent_Descent
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_H1_Zero_W1p_Two"
begin

section \<open>Finite-measure descent of the reviewed Sobolev norm\<close>

theorem slp_w1p_norm_on_mono_exponent_bounded:
  assumes p_one_le: "1 \<le> (p::real)"
    and exponent_order: "p < q"
    and X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
    and pair_q: "slp_w1p_pair_on q X u Du"
  shows pair_p: "slp_w1p_pair_on p X u Du"
    and norm_bound:
      "slp_w1p_norm_on p X u Du \<le>
        12 * measure lborel X powr (1 / p - 1 / q) *
          slp_w1p_norm_on q X u Du"
proof -
  have p_positive: "0 < p" using p_one_le by linarith
  have q_positive: "0 < q" using p_positive exponent_order by linarith
  have weak: "slp_weak_gradient_on X u Du"
    and u_q: "slp_complex_lp_on q X u"
    and D0_q: "slp_complex_lp_on q X (\<lambda>x. Du x $ 0)"
    and D1_q: "slp_complex_lp_on q X (\<lambda>x. Du x $ 1)"
    using pair_q unfolding slp_w1p_pair_on_def by blast+
  note u_descent = slp_complex_lp_norm_on_mono_exponent_bounded[
    OF p_positive exponent_order X_measurable X_bounded u_q]
  note D0_descent = slp_complex_lp_norm_on_mono_exponent_bounded[
    OF p_positive exponent_order X_measurable X_bounded D0_q]
  note D1_descent = slp_complex_lp_norm_on_mono_exponent_bounded[
    OF p_positive exponent_order X_measurable X_bounded D1_q]
  have established_pair_p: "slp_w1p_pair_on p X u Du"
    unfolding slp_w1p_pair_on_def
    using weak u_descent(1) D0_descent(1) D1_descent(1) by blast
  show "slp_w1p_pair_on p X u Du"
    by (rule established_pair_p)

  let ?A = "measure lborel X powr (1 / p - 1 / q)"
  let ?W = "slp_w1p_norm_on q X u Du"
  note q_components = slp_w1p_norm_on_component_bounds[
    OF q_positive pair_q]
  have U_q_bound: "slp_complex_lp_norm_on q X u \<le> ?W"
    using q_components(1) unfolding slp_complex_lp_norm_on_def by blast
  have D0_q_bound:
      "slp_complex_lp_norm_on q X (\<lambda>x. Du x $ 0) \<le> ?W"
    using q_components(2) unfolding slp_complex_lp_norm_on_def by blast
  have D1_q_bound:
      "slp_complex_lp_norm_on q X (\<lambda>x. Du x $ 1) \<le> ?W"
    using q_components(3) unfolding slp_complex_lp_norm_on_def by blast
  have A_nonnegative: "0 \<le> ?A" by simp
  have U_p_bound: "slp_complex_lp_norm_on p X u \<le> ?A * ?W"
    by (rule order_trans[OF u_descent(2)
          mult_left_mono[OF U_q_bound A_nonnegative]])
  have D0_p_bound:
      "slp_complex_lp_norm_on p X (\<lambda>x. Du x $ 0) \<le> ?A * ?W"
    by (rule order_trans[OF D0_descent(2)
          mult_left_mono[OF D0_q_bound A_nonnegative]])
  have D1_p_bound:
      "slp_complex_lp_norm_on p X (\<lambda>x. Du x $ 1) \<le> ?A * ?W"
    by (rule order_trans[OF D1_descent(2)
          mult_left_mono[OF D1_q_bound A_nonnegative]])
  have component_sum:
      "aim_complex_lp_norm p (slp_restrict_field X u) +
          aim_complex_lp_norm p
            (slp_restrict_field X (\<lambda>x. Du x $ 0)) +
          aim_complex_lp_norm p
            (slp_restrict_field X (\<lambda>x. Du x $ 1))
        \<le> 3 * (?A * ?W)"
    using U_p_bound D0_p_bound D1_p_bound
    unfolding slp_complex_lp_norm_on_def by linarith
  have coarse:
      "slp_w1p_norm_on p X u Du \<le>
        4 *
          (aim_complex_lp_norm p (slp_restrict_field X u) +
            aim_complex_lp_norm p
              (slp_restrict_field X (\<lambda>x. Du x $ 0)) +
            aim_complex_lp_norm p
              (slp_restrict_field X (\<lambda>x. Du x $ 1)))"
    by (rule slp_w1p_norm_on_component_sum_bound[
          OF p_one_le established_pair_p])
  have scaled_sum:
      "4 *
          (aim_complex_lp_norm p (slp_restrict_field X u) +
            aim_complex_lp_norm p
              (slp_restrict_field X (\<lambda>x. Du x $ 0)) +
            aim_complex_lp_norm p
              (slp_restrict_field X (\<lambda>x. Du x $ 1)))
        \<le> 4 * (3 * (?A * ?W))"
    by (rule mult_left_mono[OF component_sum]) simp
  show "slp_w1p_norm_on p X u Du \<le> 12 * ?A * ?W"
    by (rule order_trans[OF coarse order_trans[OF scaled_sum]])
       (simp add: algebra_simps)
qed

theorem slp_w1p_zero_pair_on_mono_exponent_bounded:
  assumes p_one_le: "1 \<le> (p::real)"
    and exponent_order: "p < q"
    and X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
    and zero_q: "slp_w1p_zero_pair_on q X u Du"
  shows "slp_w1p_zero_pair_on p X u Du"
proof -
  have p_positive: "0 < p" using p_one_le by linarith
  have q_one_le: "1 \<le> q" using p_one_le exponent_order by linarith
  obtain phi :: "nat \<Rightarrow> slp_scalar_field"
    where pair_q: "slp_w1p_pair_on q X u Du"
      and phi_q:
        "\<forall>n. slp_test_function_on X (phi n) \<and>
          slp_w1p_pair_on q X (phi n) (slp_classical_gradient (phi n))"
      and q_limit:
        "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          slp_w1p_norm_on q X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    using zero_q unfolding slp_w1p_zero_pair_on_def by blast
  have pair_p: "slp_w1p_pair_on p X u Du"
    by (rule slp_w1p_norm_on_mono_exponent_bounded(1)[OF
          p_one_le exponent_order X_measurable X_bounded pair_q])
  have phi_p:
      "\<forall>n. slp_test_function_on X (phi n) \<and>
        slp_w1p_pair_on p X (phi n) (slp_classical_gradient (phi n))"
  proof (intro allI conjI)
    fix n
    show "slp_test_function_on X (phi n)" using phi_q by blast
    show "slp_w1p_pair_on p X (phi n) (slp_classical_gradient (phi n))"
      by (rule slp_w1p_norm_on_mono_exponent_bounded(1)[OF
            p_one_le exponent_order X_measurable X_bounded])
         (use phi_q in blast)
  qed
  let ?K = "12 * measure lborel X powr (1 / p - 1 / q)"
  have K_nonnegative: "0 \<le> ?K" by simp
  have error_q:
      "slp_w1p_pair_on q X
        (\<lambda>x. phi n x - u x)
        (\<lambda>x. slp_classical_gradient (phi n) x - Du x)" for n
    by (rule slp_w1p_pair_on_diff[OF q_one_le])
       (use phi_q pair_q in blast)+
  have error_descent:
      "slp_w1p_norm_on p X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x)
        \<le> ?K *
          slp_w1p_norm_on q X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x)" for n
    using slp_w1p_norm_on_mono_exponent_bounded(2)[OF
        p_one_le exponent_order X_measurable X_bounded error_q]
    by (simp only: mult.assoc)
  have p_limit:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    show "\<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    proof (cases "?K = 0")
      case True
      show ?thesis
      proof (intro exI[where x=0] allI impI)
        fix n :: nat
        assume "0 \<le> n"
        have norm_nonnegative:
            "0 \<le> slp_w1p_norm_on p X
              (\<lambda>x. phi n x - u x)
              (\<lambda>x. slp_classical_gradient (phi n) x - Du x)"
          unfolding slp_w1p_norm_on_def by (rule powr_ge_zero)
        have norm_zero:
            "slp_w1p_norm_on p X
              (\<lambda>x. phi n x - u x)
              (\<lambda>x. slp_classical_gradient (phi n) x - Du x) = 0"
          using error_descent[of n] norm_nonnegative True by simp
        show "slp_w1p_norm_on p X
              (\<lambda>x. phi n x - u x)
              (\<lambda>x. slp_classical_gradient (phi n) x - Du x)
            < epsilon"
          using norm_zero epsilon_positive by simp
      qed
    next
      case False
      have K_positive: "0 < ?K" using K_nonnegative False by linarith
      have reduced_positive: "0 < epsilon / ?K"
        using epsilon_positive K_positive by simp
      obtain N where tail:
          "\<forall>n\<ge>N.
            slp_w1p_norm_on q X
              (\<lambda>x. phi n x - u x)
              (\<lambda>x. slp_classical_gradient (phi n) x - Du x)
            < epsilon / ?K"
        using q_limit[rule_format, OF reduced_positive] by blast
      show ?thesis
      proof (intro exI[where x=N] allI impI)
        fix n :: nat
        assume n_ge: "N \<le> n"
        have q_small:
            "slp_w1p_norm_on q X
              (\<lambda>x. phi n x - u x)
              (\<lambda>x. slp_classical_gradient (phi n) x - Du x)
            < epsilon / ?K"
          using tail n_ge by blast
        have scaled:
            "?K * slp_w1p_norm_on q X
                (\<lambda>x. phi n x - u x)
                (\<lambda>x. slp_classical_gradient (phi n) x - Du x)
              < ?K * (epsilon / ?K)"
          by (rule mult_strict_left_mono[OF q_small K_positive])
        have cancellation: "?K * (epsilon / ?K) = epsilon"
          using K_positive by simp
        show "slp_w1p_norm_on p X
              (\<lambda>x. phi n x - u x)
              (\<lambda>x. slp_classical_gradient (phi n) x - Du x)
            < epsilon"
          using error_descent[of n] scaled cancellation by linarith
      qed
    qed
  qed
  show ?thesis
    unfolding slp_w1p_zero_pair_on_def
    using pair_p phi_p p_limit by blast
qed

end
