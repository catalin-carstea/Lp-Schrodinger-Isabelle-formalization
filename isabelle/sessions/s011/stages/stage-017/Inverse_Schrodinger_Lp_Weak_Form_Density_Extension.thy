theory Inverse_Schrodinger_Lp_Weak_Form_Density_Extension
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Smooth_Weak_Solution"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_H1_Zero_Target_Limit"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Quantitative_Complex_Holder"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Double_Localized_Cauchy_Conjugate"
begin

section \<open>One common Sobolev approximation for both weak-form terms\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

lemma slp_w1p_exact_approximants_target_subsequence:
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and rough_pair: "slp_w1p_pair_on a X u Du"
    and phi_pairs:
      "\<forall>n. slp_test_function_on X (phi n) \<and>
        slp_w1p_pair_on a X (phi n) (slp_classical_gradient (phi n))"
    and phi_converges:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
  shows "\<exists>r :: nat \<Rightarrow> nat.
    strict_mono r \<and>
    aim_complex_lp_on_plane (aim_hls_target_exponent a)
      (slp_restrict_field X u) \<and>
    (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (\<lambda>x. phi (r n) x - slp_restrict_field X u x) < epsilon)"
proof -
  have a_positive: "0 < a" using a_lower by linarith
  have a_one_le: "1 \<le> a" using a_lower by linarith
  let ?e = "\<lambda>n x. phi n x - u x"
  let ?De = "\<lambda>n x. slp_classical_gradient (phi n) x - Du x"
  let ?W = "\<lambda>n. slp_w1p_norm_on a X (?e n) (?De n)"
  have error_pairs: "slp_w1p_pair_on a X (?e n) (?De n)" for n
    by (rule slp_w1p_pair_on_diff[OF a_one_le
          conjunct2[OF spec[OF phi_pairs]] rough_pair])
  have error_norm_nonnegative: "0 \<le> ?W n" for n
    unfolding slp_w1p_norm_on_def by simp
  have error_norm_tends: "(?W \<longlongrightarrow> 0) sequentially"
  proof (rule metric_LIMSEQ_I)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail: "\<forall>n\<ge>N. ?W n < epsilon"
      using phi_converges epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N. dist (?W n) 0 < epsilon"
      by (rule exI[of _ N])
        (use tail error_norm_nonnegative in auto)
  qed
  have power_integral_tends:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (?e n) x) powr a)) \<longlongrightarrow> 0)
        sequentially"
    by (rule slp_w1p_function_power_integral_tendsto_zero[
          OF a_positive error_pairs error_norm_tends])
  have power_integrable:
      "integrable lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (?e n) x) powr a)" for n
    by (rule slp_w1p_pair_power_integrable(1)[OF error_pairs])
  have power_L1_tends:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (Real_Vector_Spaces.norm
            (slp_restrict_field X (?e n) x) powr a))) \<longlongrightarrow> 0)
        sequentially"
    using power_integral_tends by simp
  obtain r :: "nat \<Rightarrow> nat" where r_strict: "strict_mono r"
    and power_AE:
      "AE x in lborel.
        (\<lambda>n. Real_Vector_Spaces.norm
          (slp_restrict_field X (?e (r n)) x) powr a) \<longlonglongrightarrow> 0"
    using tendsto_L1_AE_subseq[OF power_integrable power_L1_tends] by blast
  have error_AE:
      "AE x in lborel.
        (\<lambda>n. slp_restrict_field X (?e (r n)) x) \<longlonglongrightarrow> 0"
  proof (use power_AE in eventually_elim)
    fix x
    assume power_tends:
      "(\<lambda>n. Real_Vector_Spaces.norm
        (slp_restrict_field X (?e (r n)) x) powr a) \<longlonglongrightarrow> 0"
    have inverse_positive: "0 < 1 / a" using a_positive by simp
    have norm_tends:
        "(\<lambda>n. Real_Vector_Spaces.norm
          (slp_restrict_field X (?e (r n)) x)) \<longlonglongrightarrow> 0"
    proof -
      have "((\<lambda>n. (Real_Vector_Spaces.norm
          (slp_restrict_field X (?e (r n)) x) powr a) powr (1 / a))
          \<longlongrightarrow> 0 powr (1 / a)) sequentially"
        by (rule tendsto_powr2[OF power_tends tendsto_const])
          (use inverse_positive in auto)
      then show ?thesis using a_positive by (simp add: powr_powr)
    qed
    show "(\<lambda>n. slp_restrict_field X (?e (r n)) x) \<longlonglongrightarrow> 0"
      using norm_tends tendsto_norm_zero_iff by blast
  qed
  have restricted_error:
      "slp_restrict_field X (?e n) =
        (\<lambda>x. phi n x - slp_restrict_field X u x)" for n
  proof -
    have phi_restricted: "slp_restrict_field X (phi n) = phi n"
      by (rule slp_test_function_restrict_field_eq[
            OF conjunct1[OF spec[OF phi_pairs]]])
    have "slp_restrict_field X (?e n) =
        (\<lambda>x. slp_restrict_field X (phi n) x -
          slp_restrict_field X u x)"
      by (rule ext) (simp add: slp_restrict_field_def)
    also have "\<dots> = (\<lambda>x. phi n x - slp_restrict_field X u x)"
      using phi_restricted by simp
    finally show ?thesis .
  qed
  let ?psi = "\<lambda>n. phi (r n)"
  have psi_AE:
      "AE x in lborel.
        (\<lambda>n. ?psi n x - slp_restrict_field X u x) \<longlonglongrightarrow> 0"
    using error_AE by (simp only: restricted_error)
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
    obtain N where tail: "\<forall>n\<ge>N. ?W n < epsilon"
      using phi_converges epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a X
          (\<lambda>x. ?psi n x - u x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - Du x) < epsilon"
    proof (rule exI[of _ N], intro allI impI)
      fix n
      assume "N \<le> n"
      then have "N \<le> r n" using r_lower[of n] by linarith
      then show "slp_w1p_norm_on a X
          (\<lambda>x. ?psi n x - u x)
          (\<lambda>x. slp_classical_gradient (?psi n) x - Du x) < epsilon"
        using tail by blast
    qed
  qed
  have psi_pointwise:
      "AE x in lborel.
        (\<lambda>n. ?psi n x) \<longlonglongrightarrow> slp_restrict_field X u x"
  proof (use psi_AE in eventually_elim)
    fix x
    assume error_tends:
        "(\<lambda>n. ?psi n x - slp_restrict_field X u x) \<longlonglongrightarrow> 0"
    show "(\<lambda>n. ?psi n x) \<longlonglongrightarrow> slp_restrict_field X u x"
      using error_tends Lim_null by auto
  qed
  have rough_plane: "aim_complex_lp_on_plane a (slp_restrict_field X u)"
    using slp_w1p_pair_onD(2)[OF rough_pair]
    unfolding slp_complex_lp_on_def .
  have rough_measurable:
      "slp_restrict_field X u \<in> borel_measurable lborel"
    using rough_plane unfolding aim_complex_lp_on_plane_def by blast
  have target_positive: "0 < aim_hls_target_exponent a"
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
    have two_L_positive: "0 < 2 * L" using L_positive by simp
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
        using tail[rule_format, OF m_tail] tail[rule_format, OF n_tail]
        by linarith
      have scaled: "L * (?E m + ?E n) < L * (2 * ?delta)"
        by (rule mult_strict_left_mono[OF error_sum L_positive])
      have normalization: "L * (2 * ?delta) = epsilon"
        using two_L_positive by (simp add: algebra_simps)
      show "aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. ?psi m x - ?psi n x) < epsilon"
        by (rule le_less_trans[OF conjunct2[OF pairwise]])
          (use scaled normalization in simp)
    qed
  qed
  have closure:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_restrict_field X u) \<and>
        (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          aim_complex_lp_norm (aim_hls_target_exponent a)
            (\<lambda>x. ?psi n x - slp_restrict_field X u x) < epsilon)"
    by (rule aim_complex_lp_norm_cauchy_AE_limit[
          OF target_positive psi_target_lp rough_measurable
            psi_target_cauchy psi_pointwise])
  show ?thesis
    by (rule exI[of _ r])
      (use r_strict closure in blast)
qed

lemma slp_restricted_complex_holder_pairing:
  fixes q r :: real
    and f g :: slp_scalar_field
  assumes q_lower: "1 < q"
    and r_lower: "1 < r"
    and conjugate: "1 / q + 1 / r = 1"
    and f_lp: "aim_complex_lp_on_plane q (slp_restrict_field U f)"
    and g_lp: "aim_complex_lp_on_plane r (slp_restrict_field U g)"
  shows integrable:
      "set_integrable lborel U (\<lambda>x. f x * g x)"
    and bound:
      "norm (set_lebesgue_integral lborel U (\<lambda>x. f x * g x)) \<le>
        aim_complex_lp_norm q (slp_restrict_field U f) *
        aim_complex_lp_norm r (slp_restrict_field U g)"
proof -
  have presentation:
      "(\<lambda>x. indicator U x *\<^sub>R (f x * g x)) =
        (\<lambda>x. slp_restrict_field U f x * slp_restrict_field U g x)"
    by (rule ext)
      (simp add: indicator_def slp_restrict_field_def)
  note holder = slp_aim_complex_lp_on_plane_holder_integral_bound[
    OF q_lower r_lower conjugate f_lp g_lp]
  show "set_integrable lborel U (\<lambda>x. f x * g x)"
    using holder(1) unfolding set_integrable_def presentation .
  show "norm (set_lebesgue_integral lborel U (\<lambda>x. f x * g x)) \<le>
      aim_complex_lp_norm q (slp_restrict_field U f) *
      aim_complex_lp_norm r (slp_restrict_field U g)"
    using holder(2)
    unfolding set_lebesgue_integral_def presentation aim_complex_lp_norm_def .
qed

lemma slp_h1_zero_pair_joint_target_approximants:
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and U_measurable: "U \<in> sets (lborel :: slp_point measure)"
    and U_bounded: "bounded U"
    and zero_h1: "slp_h1_zero_pair_on U u Du"
  shows "\<exists>psi :: nat \<Rightarrow> slp_scalar_field.
    (\<forall>n. slp_test_function_on U (psi n) \<and>
      slp_h1_pair_on U (psi n) (slp_classical_gradient (psi n))) \<and>
    (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
      slp_h1_squared_distance U (psi n)
        (slp_classical_gradient (psi n)) u Du < epsilon) \<and>
    aim_complex_lp_on_plane (aim_hls_target_exponent a)
      (slp_restrict_field U u) \<and>
    (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (\<lambda>x. psi n x - slp_restrict_field U u x) < epsilon)"
proof -
  have a_one_le: "1 \<le> a" using a_lower by linarith
  have base_h1: "slp_h1_pair_on U u Du"
    using zero_h1 unfolding slp_h1_zero_pair_on_def by blast
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" where
      phi_test: "\<And>n. slp_test_function_on U (phi n)"
    and phi_h1:
      "\<And>n. slp_h1_pair_on U (phi n) (slp_classical_gradient (phi n))"
    and h1_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_h1_squared_distance U (phi n)
          (slp_classical_gradient (phi n)) u Du < epsilon"
    using zero_h1 unfolding slp_h1_zero_pair_on_def by blast
  have base_two: "slp_w1p_pair_on 2 U u Du"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF U_measurable base_h1])
  have phi_two:
      "slp_w1p_pair_on 2 U (phi n) (slp_classical_gradient (phi n))"
    for n
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF U_measurable phi_h1])
  have error_two:
      "slp_w1p_pair_on 2 U
        (\<lambda>x. phi n x - u x)
        (\<lambda>x. slp_classical_gradient (phi n) x - Du x)" for n
    by (rule slp_w1p_pair_on_diff[OF _ phi_two base_two]) simp
  have distance_nonnegative:
      "0 \<le> slp_h1_squared_distance U (phi n)
        (slp_classical_gradient (phi n)) u Du" for n
    unfolding slp_h1_squared_distance_def set_lebesgue_integral_def
    by (rule integral_nonneg_AE) simp
  have norm_two_identity:
      "slp_w1p_norm_on 2 U
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) =
        slp_h1_squared_distance U (phi n)
          (slp_classical_gradient (phi n)) u Du powr (1 / 2)" for n
    by (rule slp_w1p_norm_on_two_eq_h1_squared_distance_root[
          OF U_measurable phi_h1 base_h1])
  have norm_two_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on 2 U
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    have epsilon_power_positive: "0 < epsilon powr 2"
      using epsilon_positive by simp
    obtain N where tail:
        "\<forall>n\<ge>N. slp_h1_squared_distance U (phi n)
          (slp_classical_gradient (phi n)) u Du < epsilon powr 2"
      using h1_tail epsilon_power_positive by blast
    show "\<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on 2 U
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    proof (rule exI[of _ N], intro allI impI)
      fix n
      assume N_le_n: "N \<le> n"
      have powered_less:
          "slp_h1_squared_distance U (phi n)
              (slp_classical_gradient (phi n)) u Du powr (1 / 2) <
            (epsilon powr 2) powr (1 / 2)"
        by (rule powr_less_mono2)
          (use distance_nonnegative[of n] tail N_le_n in auto)
      show "slp_w1p_norm_on 2 U
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
        using powered_less epsilon_positive
        by (simp add: norm_two_identity powr_powr)
    qed
  qed
  have base_a: "slp_w1p_pair_on a U u Du"
    by (rule slp_w1p_norm_on_mono_exponent_bounded(1)[OF
          a_one_le a_upper U_measurable U_bounded base_two])
  have phi_a:
      "slp_w1p_pair_on a U (phi n) (slp_classical_gradient (phi n))"
    for n
    by (rule slp_w1p_norm_on_mono_exponent_bounded(1)[OF
          a_one_le a_upper U_measurable U_bounded phi_two])
  let ?K = "12 * measure lborel U powr (1 / a - 1 / 2)"
  have K_nonnegative: "0 \<le> ?K" by simp
  have error_descent:
      "slp_w1p_norm_on a U
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) \<le>
        ?K * slp_w1p_norm_on 2 U
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x)" for n
    using slp_w1p_norm_on_mono_exponent_bounded(2)[OF
      a_one_le a_upper U_measurable U_bounded error_two]
    by (simp only: mult.assoc)
  have norm_a_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a U
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    show "\<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a U
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    proof (cases "?K = 0")
      case True
      show ?thesis
      proof (rule exI[of _ 0], intro allI impI)
        fix n :: nat
        assume "0 \<le> n"
        have norm_nonnegative:
            "0 \<le> slp_w1p_norm_on a U
              (\<lambda>x. phi n x - u x)
              (\<lambda>x. slp_classical_gradient (phi n) x - Du x)"
          unfolding slp_w1p_norm_on_def by simp
        show "slp_w1p_norm_on a U
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
          using error_descent[of n] norm_nonnegative True epsilon_positive
          by simp
      qed
    next
      case False
      have K_positive: "0 < ?K" using K_nonnegative False by linarith
      have reduced_positive: "0 < epsilon / ?K"
        using epsilon_positive K_positive by simp
      obtain N where tail:
          "\<forall>n\<ge>N. slp_w1p_norm_on 2 U
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) <
              epsilon / ?K"
        using norm_two_tail reduced_positive by blast
      show ?thesis
      proof (rule exI[of _ N], intro allI impI)
        fix n
        assume N_le_n: "N \<le> n"
        have scaled:
            "?K * slp_w1p_norm_on 2 U
                (\<lambda>x. phi n x - u x)
                (\<lambda>x. slp_classical_gradient (phi n) x - Du x) <
              epsilon"
        proof -
          have strict:
              "?K * slp_w1p_norm_on 2 U
                  (\<lambda>x. phi n x - u x)
                  (\<lambda>x. slp_classical_gradient (phi n) x - Du x) <
                ?K * (epsilon / ?K)"
            by (rule mult_strict_left_mono[
                  OF tail[rule_format, OF N_le_n] K_positive])
          have cancellation: "?K * (epsilon / ?K) = epsilon"
            using K_positive by simp
          show ?thesis using strict cancellation by simp
        qed
        show "slp_w1p_norm_on a U
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
          by (rule le_less_trans[OF error_descent scaled])
      qed
    qed
  qed
  have exact_pairs:
      "\<forall>n. slp_test_function_on U (phi n) \<and>
        slp_w1p_pair_on a U (phi n) (slp_classical_gradient (phi n))"
    using phi_test phi_a by blast
  obtain r :: "nat \<Rightarrow> nat" where r_strict: "strict_mono r"
    and rough_target:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_restrict_field U u)"
    and target_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. phi (r n) x - slp_restrict_field U u x) < epsilon"
    using slp_w1p_exact_approximants_target_subsequence[
      OF a_lower a_upper base_a exact_pairs norm_a_tail]
    by blast
  let ?psi = "\<lambda>n. phi (r n)"
  have r_lower: "n \<le> r n" for n
    using r_strict by (rule seq_suble)
  have psi_h1:
      "\<forall>n. slp_test_function_on U (?psi n) \<and>
        slp_h1_pair_on U (?psi n) (slp_classical_gradient (?psi n))"
    using phi_test phi_h1 by blast
  have psi_h1_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_h1_squared_distance U (?psi n)
          (slp_classical_gradient (?psi n)) u Du < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail:
        "\<forall>n\<ge>N. slp_h1_squared_distance U (phi n)
          (slp_classical_gradient (phi n)) u Du < epsilon"
      using h1_tail epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N. slp_h1_squared_distance U (?psi n)
        (slp_classical_gradient (?psi n)) u Du < epsilon"
    proof (rule exI[of _ N], intro allI impI)
      fix n
      assume "N \<le> n"
      then have "N \<le> r n" using r_lower[of n] by linarith
      then show "slp_h1_squared_distance U (?psi n)
          (slp_classical_gradient (?psi n)) u Du < epsilon"
        using tail by blast
    qed
  qed
  show ?thesis
    by (rule exI[of _ ?psi])
      (use psi_h1 psi_h1_tail rough_target target_tail in blast)
qed

lemma slp_sum_two_components:
  fixes f :: "2 \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i\<in>UNIV. f i) = f 0 + f 1"
proof -
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  show ?thesis unfolding universe_two by simp
qed

theorem slp_smooth_test_weak_form_dense:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and U_measurable: "U \<in> sets (lborel :: slp_point measure)"
    and U_bounded: "bounded U"
    and F_h1: "slp_h1_data_on U F"
    and weighted_lp:
      "aim_complex_lp_on_plane p
        (slp_restrict_field U (\<lambda>x. V x * fst F x))"
    and smooth_tests:
      "\<forall>phi. slp_test_function_on U phi \<longrightarrow>
        slp_weak_form_integrable U V F
          (phi, slp_classical_gradient phi) \<and>
        slp_weak_form U V F
          (phi, slp_classical_gradient phi) = 0"
  shows "slp_weak_solution U V F"
proof -
  let ?t = "slp_double_kernel_source_exponent p"
  let ?r = "aim_hls_target_exponent ?t"
  have t_lower: "1 < ?t" and t_upper: "?t < 2"
    and target_identity: "?r = p / (p - 1)"
    using slp_double_kernel_source_exponent_arithmetic[OF p_lower p_upper]
    by blast+
  have target_holder: "?r = slp_holder_conjugate p"
    using target_identity unfolding slp_holder_conjugate_def by simp
  have r_lower: "1 < ?r"
    unfolding target_holder
    by (rule slp_holder_conjugate_lower_and_pair(1)[OF p_lower])
  have conjugate: "1 / p + 1 / ?r = 1"
    unfolding target_holder
    using slp_holder_conjugate_lower_and_pair(2)[OF p_lower]
    by (simp only: add.commute)
  have r_positive: "0 < ?r" using r_lower by linarith
  have F_pair: "slp_h1_pair_on U (fst F) (snd F)"
    using F_h1 unfolding slp_h1_data_on_def .
  have F_two: "slp_w1p_pair_on 2 U (fst F) (snd F)"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF U_measurable F_pair])
  have two_positive: "0 < (2::real)" by simp
  note F_components = slp_w1p_norm_on_component_bounds[
    OF two_positive F_two]
  have two_lower: "1 < (2::real)" by simp
  have two_conjugate: "1 / (2::real) + 1 / 2 = 1" by simp
  show ?thesis
    unfolding slp_weak_solution_def
  proof (rule conjI[OF F_h1], intro allI impI)
    fix G
    assume G_zero_data: "slp_h1_zero_data_on U G"
    have G_zero: "slp_h1_zero_pair_on U (fst G) (snd G)"
      using G_zero_data unfolding slp_h1_zero_data_on_def .
    have G_pair: "slp_h1_pair_on U (fst G) (snd G)"
      using G_zero unfolding slp_h1_zero_pair_on_def by blast
    have G_two: "slp_w1p_pair_on 2 U (fst G) (snd G)"
      by (rule slp_h1_pair_on_w1p_pair_on_two[OF U_measurable G_pair])
    note G_components = slp_w1p_norm_on_component_bounds[
      OF two_positive G_two]
    obtain psi :: "nat \<Rightarrow> slp_scalar_field" where
        psi_h1:
          "\<forall>n. slp_test_function_on U (psi n) \<and>
            slp_h1_pair_on U (psi n) (slp_classical_gradient (psi n))"
      and psi_h1_tail:
          "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
            slp_h1_squared_distance U (psi n)
              (slp_classical_gradient (psi n)) (fst G) (snd G) < epsilon"
      and G_target: "aim_complex_lp_on_plane ?r
          (slp_restrict_field U (fst G))"
      and psi_target_tail:
          "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
            aim_complex_lp_norm ?r
              (\<lambda>x. psi n x - slp_restrict_field U (fst G) x) < epsilon"
      using slp_h1_zero_pair_joint_target_approximants[
        OF t_lower t_upper U_measurable U_bounded G_zero]
      by blast
    have energy_zero_integrable:
        "set_integrable lborel U
          (\<lambda>x. snd F x $ 0 * snd G x $ 0)"
      by (rule slp_restricted_complex_holder_pairing(1)[OF
        two_lower two_lower two_conjugate
        conjunct1[OF F_components(2)] conjunct1[OF G_components(2)]])
    have energy_one_integrable:
        "set_integrable lborel U
          (\<lambda>x. snd F x $ 1 * snd G x $ 1)"
      by (rule slp_restricted_complex_holder_pairing(1)[OF
        two_lower two_lower two_conjugate
        conjunct1[OF F_components(3)] conjunct1[OF G_components(3)]])
    have energy_integrable:
        "set_integrable lborel U
          (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i * snd G x $ i)"
    proof -
      have pointwise:
          "(\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i * snd G x $ i) =
            (\<lambda>x. snd F x $ 0 * snd G x $ 0 +
              snd F x $ 1 * snd G x $ 1)"
        by (rule ext) (simp only: slp_sum_two_components)
      show ?thesis
        unfolding pointwise
        by (rule set_integral_add(1)[OF
              energy_zero_integrable energy_one_integrable])
    qed
    have potential_integrable:
        "set_integrable lborel U
          (\<lambda>x. V x * fst F x * fst G x)"
      by (rule slp_restricted_complex_holder_pairing(1)[OF
        p_lower r_lower conjugate weighted_lp G_target])
    have G_form_integrable: "slp_weak_form_integrable U V F G"
      unfolding slp_weak_form_integrable_def
      using energy_integrable potential_integrable by blast
    have G_form_zero: "slp_weak_form U V F G = 0"
    proof -
      let ?A0 = "aim_complex_lp_norm 2
        (slp_restrict_field U (\<lambda>x. snd F x $ 0))"
      let ?A1 = "aim_complex_lp_norm 2
        (slp_restrict_field U (\<lambda>x. snd F x $ 1))"
      let ?Q = "aim_complex_lp_norm p
        (slp_restrict_field U (\<lambda>x. V x * fst F x))"
      let ?C = "?A0 + ?A1 + ?Q"
      have A0_nonnegative: "0 \<le> ?A0"
        unfolding aim_complex_lp_norm_def by simp
      have A1_nonnegative: "0 \<le> ?A1"
        unfolding aim_complex_lp_norm_def by simp
      have Q_nonnegative: "0 \<le> ?Q"
        unfolding aim_complex_lp_norm_def by simp
      have C_nonnegative: "0 \<le> ?C"
        using A0_nonnegative A1_nonnegative Q_nonnegative by linarith
      have arbitrarily_small:
          "\<forall>epsilon>0. norm (slp_weak_form U V F G) < epsilon"
      proof (intro allI impI)
        fix epsilon :: real
        assume epsilon_positive: "0 < epsilon"
        let ?delta = "epsilon / (?C + 1)"
        have denominator_positive: "0 < ?C + 1"
          using C_nonnegative by linarith
        have delta_positive: "0 < ?delta"
          by (rule divide_pos_pos[OF epsilon_positive denominator_positive])
        have delta_nonzero: "?delta \<noteq> 0"
        proof
          assume "?delta = 0"
          then show False using delta_positive by linarith
        qed
        have delta_square_positive: "0 < ?delta powr 2"
        proof -
          have power_iff: "(0 < ?delta powr (2::real)) = (?delta \<noteq> 0)"
            by (rule powr_gt_zero)
          show ?thesis by (rule iffD2[OF power_iff delta_nonzero])
        qed
        obtain Nh where h1_tail:
            "\<forall>n\<ge>Nh. slp_h1_squared_distance U (psi n)
              (slp_classical_gradient (psi n)) (fst G) (snd G) <
                ?delta powr 2"
          using psi_h1_tail delta_square_positive by blast
        obtain Nt where target_tail:
            "\<forall>n\<ge>Nt. aim_complex_lp_norm ?r
              (\<lambda>x. psi n x - slp_restrict_field U (fst G) x) <
                ?delta"
          using psi_target_tail delta_positive by blast
        let ?n = "max Nh Nt"
        have n_h: "Nh \<le> ?n" and n_t: "Nt \<le> ?n" by simp_all
        have psi_test: "slp_test_function_on U (psi ?n)"
          using psi_h1 by blast
        have psi_pair:
            "slp_h1_pair_on U (psi ?n)
              (slp_classical_gradient (psi ?n))"
          using psi_h1 by blast
        have psi_two:
            "slp_w1p_pair_on 2 U (psi ?n)
              (slp_classical_gradient (psi ?n))"
          by (rule slp_h1_pair_on_w1p_pair_on_two[
                OF U_measurable psi_pair])
        have error_two:
            "slp_w1p_pair_on 2 U
              (\<lambda>x. psi ?n x - fst G x)
              (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x)"
          by (rule slp_w1p_pair_on_diff[OF _ psi_two G_two]) simp
        have distance_nonnegative:
            "0 \<le> slp_h1_squared_distance U (psi ?n)
              (slp_classical_gradient (psi ?n)) (fst G) (snd G)"
          unfolding slp_h1_squared_distance_def set_lebesgue_integral_def
          by (rule integral_nonneg_AE) simp
        have error_two_norm:
            "slp_w1p_norm_on 2 U
                (\<lambda>x. psi ?n x - fst G x)
                (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x) <
              ?delta"
        proof -
          have powered_less:
              "slp_h1_squared_distance U (psi ?n)
                  (slp_classical_gradient (psi ?n)) (fst G) (snd G)
                    powr (1 / 2) <
                (?delta powr 2) powr (1 / 2)"
            by (rule powr_less_mono2)
              (use distance_nonnegative h1_tail[rule_format, OF n_h] in auto)
          have delta_abs: "abs ?delta = ?delta"
            by (rule abs_of_pos[OF delta_positive])
          show ?thesis
            using powered_less delta_positive
              delta_abs
              slp_w1p_norm_on_two_eq_h1_squared_distance_root[
                OF U_measurable psi_pair G_pair]
            by (simp add: powr_powr)
        qed
        note error_components = slp_w1p_norm_on_component_bounds[
          OF two_positive error_two]
        have error_restriction:
            "slp_restrict_field U (\<lambda>x. psi ?n x - fst G x) =
              (\<lambda>x. psi ?n x - slp_restrict_field U (fst G) x)"
        proof -
          have psi_restricted: "slp_restrict_field U (psi ?n) = psi ?n"
            by (rule slp_test_function_restrict_field_eq[OF psi_test])
          have psi_outside: "\<And>x. x \<notin> U \<Longrightarrow> psi ?n x = 0"
          proof -
            fix x
            assume x_outside: "x \<notin> U"
            have pointwise:
                "slp_restrict_field U (psi ?n) x = psi ?n x"
              by (rule fun_cong[OF psi_restricted])
            then show "psi ?n x = 0"
              using x_outside by (simp add: slp_restrict_field_def)
          qed
          show ?thesis
          proof (rule ext)
            fix x
            show "slp_restrict_field U (\<lambda>y. psi ?n y - fst G y) x =
                psi ?n x - slp_restrict_field U (fst G) x"
              by (cases "x \<in> U")
                (simp_all add: slp_restrict_field_def psi_outside)
          qed
        qed
        have psi_a:
            "slp_w1p_pair_on ?t U (psi ?n)
              (slp_classical_gradient (psi ?n))"
          by (rule slp_h1_pair_on_w1p_pair_on_below_two[
                OF _ t_upper U_measurable U_bounded psi_pair])
            (use t_lower in linarith)
        obtain K::real where K_positive: "0 < K"
          and smooth_gain:
            "\<And>a X f. 1 < a \<Longrightarrow> a < 2 \<Longrightarrow>
              slp_test_function_on X f \<Longrightarrow>
              slp_w1p_pair_on a X f (slp_classical_gradient f) \<Longrightarrow>
              aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
              aim_complex_lp_norm (aim_hls_target_exponent a) f
                \<le> K / ((a - 1) * (2 - a)) *
                  slp_w1p_norm_on a X f (slp_classical_gradient f)"
          using slp_test_function_w1p_sobolev_hls by blast
        have psi_target: "aim_complex_lp_on_plane ?r (psi ?n)"
          by (rule conjunct1[OF smooth_gain[
                OF t_lower t_upper psi_test psi_a]])
        have error_target:
            "aim_complex_lp_on_plane ?r
              (\<lambda>x. psi ?n x - slp_restrict_field U (fst G) x)"
          by (rule aim_complex_lp_on_plane_diff[
                OF r_positive psi_target G_target])
        have error_target_restricted:
            "aim_complex_lp_on_plane ?r
              (slp_restrict_field U (\<lambda>x. psi ?n x - fst G x))"
          using error_target unfolding error_restriction .
        have error_zero_pairing:
            "set_integrable lborel U
              (\<lambda>x. snd F x $ 0 *
                (slp_classical_gradient (psi ?n) x - snd G x) $ 0) \<and>
            norm (set_lebesgue_integral lborel U
              (\<lambda>x. snd F x $ 0 *
                (slp_classical_gradient (psi ?n) x - snd G x) $ 0)) \<le>
              ?A0 * slp_w1p_norm_on 2 U
                (\<lambda>x. psi ?n x - fst G x)
                (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x)"
          using slp_restricted_complex_holder_pairing[
            OF two_lower two_lower two_conjugate
              conjunct1[OF F_components(2)]
              conjunct1[OF error_components(2)]]
            conjunct2[OF error_components(2)]
          by (auto intro: order_trans mult_left_mono A0_nonnegative)
        have error_one_pairing:
            "set_integrable lborel U
              (\<lambda>x. snd F x $ 1 *
                (slp_classical_gradient (psi ?n) x - snd G x) $ 1) \<and>
            norm (set_lebesgue_integral lborel U
              (\<lambda>x. snd F x $ 1 *
                (slp_classical_gradient (psi ?n) x - snd G x) $ 1)) \<le>
              ?A1 * slp_w1p_norm_on 2 U
                (\<lambda>x. psi ?n x - fst G x)
                (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x)"
          using slp_restricted_complex_holder_pairing[
            OF two_lower two_lower two_conjugate
              conjunct1[OF F_components(3)]
              conjunct1[OF error_components(3)]]
            conjunct2[OF error_components(3)]
          by (auto intro: order_trans mult_left_mono A1_nonnegative)
        have error_energy_integrable:
            "set_integrable lborel U
              (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                (slp_classical_gradient (psi ?n) x - snd G x) $ i)"
        proof -
          have pointwise:
              "(\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                  (slp_classical_gradient (psi ?n) x - snd G x) $ i) =
                (\<lambda>x. snd F x $ 0 *
                    (slp_classical_gradient (psi ?n) x - snd G x) $ 0 +
                  snd F x $ 1 *
                    (slp_classical_gradient (psi ?n) x - snd G x) $ 1)"
            by (rule ext) (simp only: slp_sum_two_components)
          show ?thesis
            unfolding pointwise
            by (rule set_integral_add(1)[OF
              conjunct1[OF error_zero_pairing]
              conjunct1[OF error_one_pairing]])
        qed
        have error_energy_bound:
            "norm (set_lebesgue_integral lborel U
              (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                (slp_classical_gradient (psi ?n) x - snd G x) $ i)) \<le>
              (?A0 + ?A1) * slp_w1p_norm_on 2 U
                (\<lambda>x. psi ?n x - fst G x)
                (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x)"
        proof -
          have pointwise:
              "(\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                  (slp_classical_gradient (psi ?n) x - snd G x) $ i) =
                (\<lambda>x. snd F x $ 0 *
                    (slp_classical_gradient (psi ?n) x - snd G x) $ 0 +
                  snd F x $ 1 *
                    (slp_classical_gradient (psi ?n) x - snd G x) $ 1)"
            by (rule ext) (simp only: slp_sum_two_components)
          have integral_sum:
              "set_lebesgue_integral lborel U
                  (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                    (slp_classical_gradient (psi ?n) x - snd G x) $ i) =
                set_lebesgue_integral lborel U
                  (\<lambda>x. snd F x $ 0 *
                    (slp_classical_gradient (psi ?n) x - snd G x) $ 0) +
                set_lebesgue_integral lborel U
                  (\<lambda>x. snd F x $ 1 *
                    (slp_classical_gradient (psi ?n) x - snd G x) $ 1)"
            unfolding pointwise
            by (rule set_integral_add(2)[OF
              conjunct1[OF error_zero_pairing]
              conjunct1[OF error_one_pairing]])
          have component_sum_bound:
              "norm (set_lebesgue_integral lborel U
                  (\<lambda>x. snd F x $ 0 *
                    (slp_classical_gradient (psi ?n) x - snd G x) $ 0)) +
                norm (set_lebesgue_integral lborel U
                  (\<lambda>x. snd F x $ 1 *
                    (slp_classical_gradient (psi ?n) x - snd G x) $ 1)) \<le>
                (?A0 + ?A1) * slp_w1p_norm_on 2 U
                  (\<lambda>x. psi ?n x - fst G x)
                  (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x)"
          proof -
            have "norm (set_lebesgue_integral lborel U
                    (\<lambda>x. snd F x $ 0 *
                      (slp_classical_gradient (psi ?n) x - snd G x) $ 0)) +
                  norm (set_lebesgue_integral lborel U
                    (\<lambda>x. snd F x $ 1 *
                      (slp_classical_gradient (psi ?n) x - snd G x) $ 1)) \<le>
                  ?A0 * slp_w1p_norm_on 2 U
                    (\<lambda>x. psi ?n x - fst G x)
                    (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x) +
                  ?A1 * slp_w1p_norm_on 2 U
                    (\<lambda>x. psi ?n x - fst G x)
                    (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x)"
              by (rule add_mono[OF
                conjunct2[OF error_zero_pairing]
                conjunct2[OF error_one_pairing]])
            also have "... =
                (?A0 + ?A1) * slp_w1p_norm_on 2 U
                  (\<lambda>x. psi ?n x - fst G x)
                  (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x)"
              by (rule distrib_right[symmetric])
            finally show ?thesis .
          qed
          show ?thesis
            unfolding integral_sum
            by (rule order_trans[OF norm_triangle_ineq component_sum_bound])
        qed
        have error_potential_pairing:
            "set_integrable lborel U
              (\<lambda>x. (V x * fst F x) * (psi ?n x - fst G x)) \<and>
            norm (set_lebesgue_integral lborel U
              (\<lambda>x. (V x * fst F x) * (psi ?n x - fst G x))) \<le>
              ?Q * aim_complex_lp_norm ?r
                (\<lambda>x. psi ?n x - slp_restrict_field U (fst G) x)"
          using slp_restricted_complex_holder_pairing[
            OF p_lower r_lower conjugate weighted_lp
              error_target_restricted]
          unfolding error_restriction by blast
        note test_form = smooth_tests[rule_format, OF psi_test]
        have test_energy_integrable:
            "set_integrable lborel U
              (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                slp_classical_gradient (psi ?n) x $ i)"
          using test_form unfolding slp_weak_form_integrable_def by simp
        have test_potential_integrable:
            "set_integrable lborel U
              (\<lambda>x. V x * fst F x * psi ?n x)"
          using test_form unfolding slp_weak_form_integrable_def by simp
        have energy_difference:
            "set_lebesgue_integral lborel U
                (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                  slp_classical_gradient (psi ?n) x $ i) -
              set_lebesgue_integral lborel U
                (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i * snd G x $ i) =
              set_lebesgue_integral lborel U
                (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                  (slp_classical_gradient (psi ?n) x - snd G x) $ i)"
        proof -
          note raw = set_integral_diff(2)[OF
            test_energy_integrable energy_integrable]
          have pointwise:
              "(\<lambda>x. (\<Sum>i\<in>UNIV. snd F x $ i *
                    slp_classical_gradient (psi ?n) x $ i) -
                  (\<Sum>i\<in>UNIV. snd F x $ i * snd G x $ i)) =
                (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                  (slp_classical_gradient (psi ?n) x - snd G x) $ i)"
            by (rule ext) (simp add: slp_sum_two_components algebra_simps)
          show ?thesis using raw unfolding pointwise by (rule sym)
        qed
        have potential_difference:
            "set_lebesgue_integral lborel U
                (\<lambda>x. V x * fst F x * psi ?n x) -
              set_lebesgue_integral lborel U
                (\<lambda>x. V x * fst F x * fst G x) =
              set_lebesgue_integral lborel U
                (\<lambda>x. (V x * fst F x) * (psi ?n x - fst G x))"
        proof -
          note raw = set_integral_diff(2)[OF
            test_potential_integrable potential_integrable]
          have pointwise:
              "(\<lambda>x. V x * fst F x * psi ?n x -
                  V x * fst F x * fst G x) =
                (\<lambda>x. (V x * fst F x) * (psi ?n x - fst G x))"
            by (rule ext) (simp add: algebra_simps)
          show ?thesis using raw unfolding pointwise by (rule sym)
        qed
        have weak_difference:
            "slp_weak_form U V F
                (psi ?n, slp_classical_gradient (psi ?n)) -
              slp_weak_form U V F G =
              set_lebesgue_integral lborel U
                (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                  (slp_classical_gradient (psi ?n) x - snd G x) $ i) +
              set_lebesgue_integral lborel U
                (\<lambda>x. (V x * fst F x) * (psi ?n x - fst G x))"
          unfolding slp_weak_form_def
          using energy_difference potential_difference
          by (simp add: algebra_simps)
        have weak_norm_bound:
            "norm (slp_weak_form U V F G) \<le>
              (?A0 + ?A1) * slp_w1p_norm_on 2 U
                (\<lambda>x. psi ?n x - fst G x)
                (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x) +
              ?Q * aim_complex_lp_norm ?r
                (\<lambda>x. psi ?n x - slp_restrict_field U (fst G) x)"
        proof -
          have test_zero:
              "slp_weak_form U V F
                (psi ?n, slp_classical_gradient (psi ?n)) = 0"
            using test_form by blast
          have presentation:
              "norm (slp_weak_form U V F G) =
                norm (set_lebesgue_integral lborel U
                  (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                    (slp_classical_gradient (psi ?n) x - snd G x) $ i) +
                  set_lebesgue_integral lborel U
                    (\<lambda>x. (V x * fst F x) *
                      (psi ?n x - fst G x)))"
          proof -
            have negated:
                "- slp_weak_form U V F G =
                  set_lebesgue_integral lborel U
                    (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i *
                      (slp_classical_gradient (psi ?n) x - snd G x) $ i) +
                  set_lebesgue_integral lborel U
                    (\<lambda>x. (V x * fst F x) *
                      (psi ?n x - fst G x))"
              using weak_difference test_zero by simp
            note normed = arg_cong[where f=norm, OF negated]
            show ?thesis using normed by simp
          qed
          show ?thesis
            unfolding presentation
            by (rule order_trans[OF norm_triangle_ineq])
              (rule add_mono[OF error_energy_bound
                conjunct2[OF error_potential_pairing]])
        qed
        have scaled_bound:
            "(?A0 + ?A1) * slp_w1p_norm_on 2 U
                (\<lambda>x. psi ?n x - fst G x)
                (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x) +
              ?Q * aim_complex_lp_norm ?r
                (\<lambda>x. psi ?n x - slp_restrict_field U (fst G) x) <
              epsilon"
        proof -
          have first_strict:
              "(?A0 + ?A1) * slp_w1p_norm_on 2 U
                  (\<lambda>x. psi ?n x - fst G x)
                  (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x)
                \<le> (?A0 + ?A1) * ?delta"
            by (rule mult_left_mono)
              (use error_two_norm A0_nonnegative A1_nonnegative in auto)
          have second_strict:
              "?Q * aim_complex_lp_norm ?r
                  (\<lambda>x. psi ?n x - slp_restrict_field U (fst G) x)
                \<le> ?Q * ?delta"
            by (rule mult_left_mono)
              (use target_tail[rule_format, OF n_t] Q_nonnegative in auto)
          have combined:
              "(?A0 + ?A1) * slp_w1p_norm_on 2 U
                  (\<lambda>x. psi ?n x - fst G x)
                  (\<lambda>x. slp_classical_gradient (psi ?n) x - snd G x) +
                ?Q * aim_complex_lp_norm ?r
                  (\<lambda>x. psi ?n x - slp_restrict_field U (fst G) x)
                \<le> ?C * ?delta"
            by (rule order_trans[OF add_mono[OF first_strict second_strict]])
              (simp only: distrib_right)
          have C_less: "?C * ?delta < epsilon"
          proof -
            have "?C < ?C + 1" by linarith
            then have "?C * epsilon < (?C + 1) * epsilon"
              by (rule mult_strict_right_mono[OF _ epsilon_positive])
            then show ?thesis
              using denominator_positive by (simp add: field_simps)
          qed
          show ?thesis by (rule le_less_trans[OF combined C_less])
        qed
        show "norm (slp_weak_form U V F G) < epsilon"
          by (rule le_less_trans[OF weak_norm_bound scaled_bound])
      qed
      show ?thesis
      proof (rule ccontr)
        assume nonzero: "slp_weak_form U V F G \<noteq> 0"
        have norm_positive: "0 < norm (slp_weak_form U V F G)"
          using nonzero by simp
        have impossible:
            "norm (slp_weak_form U V F G) <
              norm (slp_weak_form U V F G)"
          using arbitrarily_small[rule_format, OF norm_positive] .
        show False using impossible by simp
      qed
    qed
    show "slp_weak_form_integrable U V F G \<and>
        slp_weak_form U V F G = 0"
      using G_form_integrable G_form_zero by blast
  qed
qed

end

end
