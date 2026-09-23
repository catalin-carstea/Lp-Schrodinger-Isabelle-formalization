theory Inverse_Schrodinger_Lp_W1p_Zero_Pair_Target_Cauchy
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Pairwise_Error_Sobolev"
begin

section \<open>Target-exponent Cauchy approximants for a zero Sobolev pair\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_target_cauchy_approximants:
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and zero_pair: "slp_w1p_zero_pair_on a X u Du"
  shows "\<exists>phi :: nat \<Rightarrow> slp_scalar_field.
    (\<forall>n. slp_test_function_on X (phi n) \<and>
      slp_w1p_pair_on a X (phi n) (slp_classical_gradient (phi n))) \<and>
    (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
      slp_w1p_norm_on a X
        (\<lambda>x. phi n x - u x)
        (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon) \<and>
    (\<forall>m n. aim_complex_lp_on_plane (aim_hls_target_exponent a)
      (\<lambda>x. phi m x - phi n x)) \<and>
    (\<forall>epsilon>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (\<lambda>x. phi m x - phi n x) < epsilon)"
proof -
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
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" where
      phi_pairs:
        "\<forall>n. slp_test_function_on X (phi n) \<and>
          slp_w1p_pair_on a X (phi n) (slp_classical_gradient (phi n))"
    and phi_converges:
        "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          slp_w1p_norm_on a X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have rough_pair: "slp_w1p_pair_on a X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  define L where "L = K / ((a - 1) * (2 - a)) * 48"
  let ?E = "\<lambda>n. slp_w1p_norm_on a X
    (\<lambda>x. phi n x - u x)
    (\<lambda>x. slp_classical_gradient (phi n) x - Du x)"
  have pairwise:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (\<lambda>x. phi m x - phi n x) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. phi m x - phi n x) \<le> L * (?E m + ?E n)"
    for m n
    unfolding L_def
    by (rule pairwise_gain[OF a_lower a_upper rough_pair
          conjunct1[OF spec[OF phi_pairs]]
          conjunct2[OF spec[OF phi_pairs]]
          conjunct1[OF spec[OF phi_pairs]]
          conjunct2[OF spec[OF phi_pairs]]])
  have pairwise_membership:
      "\<forall>m n. aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (\<lambda>x. phi m x - phi n x)"
    using pairwise by blast
  have denominator_positive: "0 < (a - 1) * (2 - a)"
  proof (rule mult_pos_pos)
    show "0 < a - 1" using a_lower by simp
    show "0 < 2 - a" using a_upper by simp
  qed
  have L_positive: "0 < L"
    unfolding L_def using K_positive denominator_positive by simp
  have pairwise_cauchy:
      "\<forall>epsilon>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. phi m x - phi n x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    let ?delta = "epsilon / (2 * L)"
    have two_L_positive: "0 < 2 * L"
      using L_positive by simp
    have delta_positive: "0 < ?delta"
      by (rule divide_pos_pos[OF epsilon_positive two_L_positive])
    obtain N where tail: "\<forall>n\<ge>N. ?E n < ?delta"
      using phi_converges delta_positive by blast
    show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. phi m x - phi n x) < epsilon"
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
            (\<lambda>x. phi m x - phi n x) \<le> L * (?E m + ?E n)"
        by (rule conjunct2[OF pairwise])
      show "aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. phi m x - phi n x) < epsilon"
        by (rule le_less_trans[OF target_bound])
          (use scaled_error_sum normalization in simp)
    qed
  qed
  show ?thesis
    by (rule exI[of _ phi])
      (use phi_pairs phi_converges pairwise_membership pairwise_cauchy in blast)
qed

end

end
