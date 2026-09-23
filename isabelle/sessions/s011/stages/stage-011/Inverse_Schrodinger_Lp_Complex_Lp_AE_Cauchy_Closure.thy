theory Inverse_Schrodinger_Lp_Complex_Lp_AE_Cauchy_Closure
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Zero_Pair_AE_Subsequence"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_NN_Integral_Fatou_Finite"
begin

section \<open>Concrete planar Lp closure under norm-Cauchy and a.e. convergence\<close>

theorem aim_complex_lp_norm_cauchy_AE_limit:
  fixes F :: "nat \<Rightarrow> slp_scalar_field"
    and f :: slp_scalar_field
  assumes exponent_positive: "0 < p"
    and sequence_lp: "\<And>n. aim_complex_lp_on_plane p (F n)"
    and limit_measurable: "f \<in> borel_measurable lborel"
    and norm_cauchy:
      "\<forall>epsilon>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
        aim_complex_lp_norm p (\<lambda>x. F m x - F n x) < epsilon"
    and pointwise_limit: "AE x in lborel. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
  shows "aim_complex_lp_on_plane p f \<and>
    (\<forall>epsilon>0. \<exists>N. \<forall>m\<ge>N.
      aim_complex_lp_norm p (\<lambda>x. F m x - f x) < epsilon)"
proof -
  have limit_error_bound:
      "\<And>delta. 0 < delta \<Longrightarrow> \<exists>N. \<forall>m\<ge>N.
        aim_complex_lp_on_plane p (\<lambda>x. F m x - f x) \<and>
        aim_complex_lp_norm p (\<lambda>x. F m x - f x) \<le> delta"
  proof -
    fix delta :: real
    assume delta_positive: "0 < delta"
    obtain N where cauchy_tail:
        "\<forall>m\<ge>N. \<forall>n\<ge>N.
          aim_complex_lp_norm p (\<lambda>x. F m x - F n x) < delta"
      using norm_cauchy delta_positive by blast
    show "\<exists>N. \<forall>m\<ge>N.
        aim_complex_lp_on_plane p (\<lambda>x. F m x - f x) \<and>
        aim_complex_lp_norm p (\<lambda>x. F m x - f x) \<le> delta"
    proof (rule exI[of _ N], intro allI impI)
      fix m
      assume m_tail: "N \<le> m"
      let ?H = "\<lambda>n x. F m x - F n x"
      let ?h = "\<lambda>x. F m x - f x"
      let ?U = "\<lambda>n x. ennreal
        (Real_Vector_Spaces.norm (?H n x) powr p)"
      let ?v = "\<lambda>x. ennreal
        (Real_Vector_Spaces.norm (?h x) powr p)"
      have difference_lp:
          "aim_complex_lp_on_plane p (?H n)" for n
        by (rule aim_complex_lp_on_plane_diff[OF exponent_positive
              sequence_lp sequence_lp])
      have difference_power_integrable:
          "integrable lborel
            (\<lambda>x. Real_Vector_Spaces.norm (?H n x) powr p)" for n
        using difference_lp[of n]
        unfolding aim_complex_lp_on_plane_def by blast
      have U_measurable: "?U n \<in> borel_measurable lborel" for n
        using borel_measurable_integrable[
          OF difference_power_integrable[of n]] by measurable
      have Fm_measurable: "F m \<in> borel_measurable lborel"
        using sequence_lp[of m]
        unfolding aim_complex_lp_on_plane_def by blast
      have target_error_measurable: "?h \<in> borel_measurable lborel"
        using Fm_measurable limit_measurable by measurable
      have power_pointwise_limit:
          "AE x in lborel. (\<lambda>n. ?U n x) \<longlonglongrightarrow> ?v x"
      proof (use pointwise_limit in eventually_elim)
        fix x
        assume x_limit: "(\<lambda>n. F n x) \<longlonglongrightarrow> f x"
        have difference_limit:
            "(\<lambda>n. ?H n x) \<longlonglongrightarrow> ?h x"
          using x_limit by (intro tendsto_intros)
        have norm_limit:
            "(\<lambda>n. Real_Vector_Spaces.norm (?H n x))
              \<longlonglongrightarrow> Real_Vector_Spaces.norm (?h x)"
          by (rule tendsto_norm[OF difference_limit])
        have power_limit:
            "(\<lambda>n. Real_Vector_Spaces.norm (?H n x) powr p)
              \<longlonglongrightarrow> Real_Vector_Spaces.norm (?h x) powr p"
          by (rule tendsto_powr2[OF norm_limit tendsto_const])
            (use exponent_positive in auto)
        show "(\<lambda>n. ?U n x) \<longlonglongrightarrow> ?v x"
          by (rule tendsto_ennrealI[OF power_limit])
      qed
      have fatou_bound:
          "(\<integral>\<^sup>+x. ?v x \<partial>lborel) \<le>
            liminf (\<lambda>n. \<integral>\<^sup>+x. ?U n x \<partial>lborel)"
        by (rule slp_nn_integral_le_liminf_of_AE_tendsto[
              OF U_measurable power_pointwise_limit])
      have eventual_sequence_bound:
          "eventually
            (\<lambda>n. (\<integral>\<^sup>+x. ?U n x \<partial>lborel) \<le>
              ennreal (delta powr p)) sequentially"
      proof (rule eventually_sequentiallyI[of N])
        fix n
        assume n_tail: "N \<le> n"
        let ?J = "integral\<^sup>L lborel
          (\<lambda>x. Real_Vector_Spaces.norm (?H n x) powr p)"
        have J_nonnegative: "0 \<le> ?J"
          by (rule Bochner_Integration.integral_nonneg) simp
        have norm_power:
            "(aim_complex_lp_norm p (?H n)) powr p = ?J"
          unfolding aim_complex_lp_norm_def
          using exponent_positive J_nonnegative by (simp add: powr_powr)
        have norm_nonnegative:
            "0 \<le> aim_complex_lp_norm p (?H n)"
          unfolding aim_complex_lp_norm_def by simp
        have powered_bound:
            "(aim_complex_lp_norm p (?H n)) powr p < delta powr p"
          by (rule powr_less_mono2[OF exponent_positive])
            (use norm_nonnegative cauchy_tail m_tail n_tail in auto)
        have J_bound: "?J < delta powr p"
          using powered_bound by (simp only: norm_power)
        have nn_as_real:
            "(\<integral>\<^sup>+x. ?U n x \<partial>lborel) = ennreal ?J"
          using difference_power_integrable[of n]
          by (subst nn_integral_eq_integral) auto
        show "(\<integral>\<^sup>+x. ?U n x \<partial>lborel) \<le>
            ennreal (delta powr p)"
          using J_bound nn_as_real by simp
      qed
      have liminf_bound:
          "liminf (\<lambda>n. \<integral>\<^sup>+x. ?U n x \<partial>lborel) \<le>
            ennreal (delta powr p)"
      proof -
        have constant_liminf:
            "liminf (\<lambda>n. ennreal (delta powr p)) =
              ennreal (delta powr p)"
          by (rule lim_imp_Liminf[OF trivial_limit_sequentially tendsto_const])
        have "liminf (\<lambda>n. \<integral>\<^sup>+x. ?U n x \<partial>lborel) \<le>
            liminf (\<lambda>n. ennreal (delta powr p))"
          by (rule Liminf_mono[OF eventual_sequence_bound])
        then show ?thesis by (simp only: constant_liminf)
      qed
      have target_nn_bound:
          "(\<integral>\<^sup>+x. ?v x \<partial>lborel) \<le>
            ennreal (delta powr p)"
        by (rule order_trans[OF fatou_bound liminf_bound])
      have target_nn_less_top:
          "(\<integral>\<^sup>+x. ?v x \<partial>lborel) < \<infinity>"
      proof -
        have "ennreal (delta powr p) < \<infinity>" by simp
        then show ?thesis
          by (rule order_le_less_trans[OF target_nn_bound])
      qed
      have target_power_measurable:
          "(\<lambda>x. Real_Vector_Spaces.norm (?h x) powr p)
            \<in> borel_measurable lborel"
        using target_error_measurable by measurable
      have target_power_integrable:
          "integrable lborel
            (\<lambda>x. Real_Vector_Spaces.norm (?h x) powr p)"
      proof (rule integrableI_nn_integral_finite[OF target_power_measurable])
        show "AE x in lborel.
            0 \<le> Real_Vector_Spaces.norm (?h x) powr p"
          by simp
        show "(\<integral>\<^sup>+x.
              Real_Vector_Spaces.norm (?h x) powr p \<partial>lborel) =
            ennreal (enn2real (\<integral>\<^sup>+x. ?v x \<partial>lborel))"
          using target_nn_less_top by simp
      qed
      have target_error_lp:
          "aim_complex_lp_on_plane p ?h"
        using target_error_measurable target_power_integrable
        unfolding aim_complex_lp_on_plane_def by blast
      let ?I = "integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm (?h x) powr p)"
      have I_nonnegative: "0 \<le> ?I"
        by (rule Bochner_Integration.integral_nonneg) simp
      have target_nn_as_real:
          "(\<integral>\<^sup>+x. ?v x \<partial>lborel) = ennreal ?I"
        using target_power_integrable
        by (subst nn_integral_eq_integral) auto
      have I_bound: "?I \<le> delta powr p"
        using target_nn_bound target_nn_as_real by simp
      have inverse_nonnegative: "0 \<le> 1 / p"
        using exponent_positive by simp
      have root_bound:
          "?I powr (1 / p) \<le> (delta powr p) powr (1 / p)"
        by (rule powr_mono2[OF inverse_nonnegative I_nonnegative I_bound])
      have target_norm_bound:
          "aim_complex_lp_norm p ?h \<le> delta"
        unfolding aim_complex_lp_norm_def
        using root_bound exponent_positive delta_positive
        by (simp add: powr_powr)
      show "aim_complex_lp_on_plane p ?h \<and>
          aim_complex_lp_norm p ?h \<le> delta"
        using target_error_lp target_norm_bound by blast
    qed
  qed
  have norm_converges:
      "\<forall>epsilon>0. \<exists>N. \<forall>m\<ge>N.
        aim_complex_lp_norm p (\<lambda>x. F m x - f x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    have half_positive: "0 < epsilon / 2"
      using epsilon_positive by simp
    obtain N where tail:
        "\<forall>m\<ge>N.
          aim_complex_lp_on_plane p (\<lambda>x. F m x - f x) \<and>
          aim_complex_lp_norm p (\<lambda>x. F m x - f x) \<le> epsilon / 2"
      using limit_error_bound[OF half_positive] by blast
    show "\<exists>N. \<forall>m\<ge>N.
        aim_complex_lp_norm p (\<lambda>x. F m x - f x) < epsilon"
    proof (rule exI[of _ N], intro allI impI)
      fix m
      assume m_tail: "N \<le> m"
      have half_bound:
          "aim_complex_lp_norm p (\<lambda>x. F m x - f x) \<le> epsilon / 2"
        using tail m_tail by blast
      have half_less: "epsilon / 2 < epsilon"
        using epsilon_positive by simp
      show "aim_complex_lp_norm p (\<lambda>x. F m x - f x) < epsilon"
        by (rule le_less_trans[OF half_bound half_less])
    qed
  qed
  have one_positive: "0 < (1::real)" by simp
  obtain N where one_tail:
      "\<forall>m\<ge>N.
        aim_complex_lp_on_plane p (\<lambda>x. F m x - f x) \<and>
        aim_complex_lp_norm p (\<lambda>x. F m x - f x) \<le> 1"
    using limit_error_bound[OF one_positive] by blast
  have reconstructed_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. F N x - (F N x - f x))"
    by (rule aim_complex_lp_on_plane_diff[OF exponent_positive
          sequence_lp conjunct1[OF one_tail[rule_format, OF order_refl]]])
  have limit_lp: "aim_complex_lp_on_plane p f"
    using reconstructed_lp by simp
  show ?thesis using limit_lp norm_converges by blast
qed

section \<open>Target-exponent membership of the rough Sobolev representative\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_target_limit:
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and zero_pair: "slp_w1p_zero_pair_on a X u Du"
  shows "aim_complex_lp_on_plane (aim_hls_target_exponent a)
      (slp_restrict_field X u) \<and>
    (\<exists>psi :: nat \<Rightarrow> slp_scalar_field.
      (\<forall>n. slp_test_function_on X (psi n) \<and>
        slp_w1p_pair_on a X (psi n) (slp_classical_gradient (psi n))) \<and>
      (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a X
          (\<lambda>x. psi n x - u x)
          (\<lambda>x. slp_classical_gradient (psi n) x - Du x) < epsilon) \<and>
      (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. psi n x - slp_restrict_field X u x) < epsilon))"
proof -
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" and r :: "nat \<Rightarrow> nat"
    where phi_pairs:
        "\<forall>n. slp_test_function_on X (phi n) \<and>
          slp_w1p_pair_on a X (phi n) (slp_classical_gradient (phi n))"
      and phi_converges:
        "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          slp_w1p_norm_on a X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
      and r_strict: "strict_mono r"
      and phi_AE:
        "AE x in lborel.
          (\<lambda>n. phi (r n) x - slp_restrict_field X u x)
            \<longlonglongrightarrow> 0"
    using slp_w1p_zero_pair_function_AE_subsequence[OF a_lower zero_pair]
    by blast
  let ?psi = "\<lambda>n. phi (r n)"
  have r_lower: "n \<le> r n" for n
    using r_strict by (rule seq_suble)
  have psi_pairs:
      "\<forall>n. slp_test_function_on X (?psi n) \<and>
        slp_w1p_pair_on a X (?psi n) (slp_classical_gradient (?psi n))"
    using phi_pairs by blast
  have psi_converges:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a X
          (\<lambda>x. ?psi n x - u x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - Du x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail:
        "\<forall>n\<ge>N.
          slp_w1p_norm_on a X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
      using phi_converges epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a X
          (\<lambda>x. ?psi n x - u x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - Du x) < epsilon"
    proof (rule exI[of _ N], intro allI impI)
      fix n
      assume n_tail: "N \<le> n"
      have rn_tail: "N \<le> r n"
        using n_tail r_lower[of n] by linarith
      show "slp_w1p_norm_on a X
          (\<lambda>x. ?psi n x - u x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - Du x) < epsilon"
        using tail rn_tail by blast
    qed
  qed
  have psi_pointwise:
      "AE x in lborel.
        (\<lambda>n. ?psi n x) \<longlonglongrightarrow> slp_restrict_field X u x"
  proof (use phi_AE in eventually_elim)
    fix x
    assume error_tends:
        "(\<lambda>n. ?psi n x - slp_restrict_field X u x)
          \<longlonglongrightarrow> 0"
    show "(\<lambda>n. ?psi n x) \<longlonglongrightarrow> slp_restrict_field X u x"
      using error_tends Lim_null by auto
  qed
  have rough_pair: "slp_w1p_pair_on a X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have rough_plane:
      "aim_complex_lp_on_plane a (slp_restrict_field X u)"
    using slp_w1p_pair_onD(2)[OF rough_pair]
    unfolding slp_complex_lp_on_def .
  have rough_measurable:
      "slp_restrict_field X u \<in> borel_measurable lborel"
    using rough_plane unfolding aim_complex_lp_on_plane_def by blast
  have target_exponent_positive: "0 < aim_hls_target_exponent a"
    unfolding aim_hls_target_exponent_def
    using a_lower a_upper
    by (intro divide_pos_pos mult_pos_pos) auto
  obtain C::real where C_positive: "0 < C"
    and smooth_gain:
      "\<And>a X f. 1 < a \<Longrightarrow> a < 2 \<Longrightarrow>
        slp_test_function_on X f \<Longrightarrow>
        slp_w1p_pair_on a X f (slp_classical_gradient f) \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a) f
          \<le> C / ((a - 1) * (2 - a)) *
            slp_w1p_norm_on a X f (slp_classical_gradient f)"
    using slp_test_function_w1p_sobolev_hls by blast
  have psi_target_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) (?psi n)" for n
    by (rule conjunct1[OF smooth_gain[OF a_lower a_upper
          conjunct1[OF spec[OF psi_pairs]]
          conjunct2[OF spec[OF psi_pairs]]]])
  obtain K::real where K_positive: "0 < K"
    and pairwise_gain:
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
  define L where "L = K / ((a - 1) * (2 - a)) * 48"
  let ?E = "\<lambda>n. slp_w1p_norm_on a X
    (\<lambda>x. ?psi n x - u x)
    (\<lambda>x. slp_classical_gradient (?psi n) x - Du x)"
  have pairwise:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (\<lambda>x. ?psi m x - ?psi n x) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. ?psi m x - ?psi n x) \<le> L * (?E m + ?E n)"
    for m n
    unfolding L_def
    by (rule pairwise_gain[OF a_lower a_upper rough_pair
          conjunct1[OF spec[OF psi_pairs]]
          conjunct2[OF spec[OF psi_pairs]]
          conjunct1[OF spec[OF psi_pairs]]
          conjunct2[OF spec[OF psi_pairs]]])
  have denominator_positive: "0 < (a - 1) * (2 - a)"
    by (rule mult_pos_pos) (use a_lower a_upper in linarith)+
  have L_positive: "0 < L"
    unfolding L_def using K_positive denominator_positive by simp
  have psi_target_cauchy:
      "\<forall>epsilon>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. ?psi m x - ?psi n x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    let ?delta = "epsilon / (2 * L)"
    have two_L_positive: "0 < 2 * L"
      using L_positive by simp
    have delta_positive: "0 < ?delta"
      by (rule divide_pos_pos[OF epsilon_positive two_L_positive])
    obtain N where tail: "\<forall>n\<ge>N. ?E n < ?delta"
      using psi_converges delta_positive by blast
    show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. ?psi m x - ?psi n x) < epsilon"
    proof (rule exI[of _ N], intro allI impI)
      fix m
      assume m_tail: "N \<le> m"
      fix n
      assume n_tail: "N \<le> n"
      have error_sum: "?E m + ?E n < 2 * ?delta"
      proof -
        have "?E m + ?E n < ?delta + ?delta"
          by (rule add_strict_mono[OF tail[rule_format, OF m_tail]
                tail[rule_format, OF n_tail]])
        then show ?thesis by simp
      qed
      have scaled_error_sum: "L * (?E m + ?E n) < L * (2 * ?delta)"
        by (rule mult_strict_left_mono[OF error_sum L_positive])
      have two_L_nonzero: "2 * L \<noteq> 0"
        using two_L_positive by simp
      have normalization: "L * (2 * ?delta) = epsilon"
        using two_L_nonzero by (simp add: algebra_simps)
      have target_bound:
          "aim_complex_lp_norm (aim_hls_target_exponent a)
            (\<lambda>x. ?psi m x - ?psi n x) \<le> L * (?E m + ?E n)"
        by (rule conjunct2[OF pairwise])
      show "aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. ?psi m x - ?psi n x) < epsilon"
        by (rule le_less_trans[OF target_bound])
          (use scaled_error_sum normalization in simp)
    qed
  qed
  have closure:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_restrict_field X u) \<and>
        (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          aim_complex_lp_norm (aim_hls_target_exponent a)
            (\<lambda>x. ?psi n x - slp_restrict_field X u x) < epsilon)"
    by (rule aim_complex_lp_norm_cauchy_AE_limit[
          OF target_exponent_positive psi_target_lp rough_measurable
            psi_target_cauchy psi_pointwise])
  show ?thesis
    by (rule conjI[OF conjunct1[OF closure]], rule exI[of _ ?psi])
      (use psi_pairs psi_converges closure in blast)
qed

end

end
