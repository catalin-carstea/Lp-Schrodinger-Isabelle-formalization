theory Inverse_Schrodinger_Lp_W1p_Rough_Partial_Psi_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Zero_Pair_Partial_Psi_Target_Limit"
begin

section \<open>Zero-reference data for uniform smooth estimates\<close>

lemma slp_w1p_zero_function_data:
  "slp_test_function_on X (\<lambda>x. 0) \<and>
    slp_classical_gradient (\<lambda>x. 0) = (\<lambda>x. 0) \<and>
    slp_w1p_pair_on a X (\<lambda>x. 0) (\<lambda>x. 0) \<and>
    slp_w1p_norm_on a X (\<lambda>x. 0) (\<lambda>x. 0) = 0 \<and>
    slp_partial_psi_inverse tau c (\<lambda>x. 0) = (\<lambda>x. 0)"
proof -
  have zero_test: "slp_test_function_on X (\<lambda>x. 0)"
    unfolding slp_test_function_on_def using smooth_on_const by simp
  have zero_gradient: "slp_classical_gradient (\<lambda>x. 0) = (\<lambda>x. 0)"
    by (rule ext)
      (simp add: slp_classical_gradient_def slp_complex_partial_derivative_def
        vec_eq_iff)
  have zero_weak: "slp_weak_gradient_on X (\<lambda>x. 0) (\<lambda>x. 0)"
    by (simp add: slp_weak_gradient_on_def set_integrable_def)
  have zero_restrict: "slp_restrict_field X (\<lambda>x. 0) = (\<lambda>x. 0)"
    by (rule ext) (simp add: slp_restrict_field_def)
  have zero_lp: "slp_complex_lp_on a X (\<lambda>x. 0)"
    by (simp add: slp_complex_lp_on_def aim_complex_lp_on_plane_def
        zero_restrict)
  have zero_pair: "slp_w1p_pair_on a X (\<lambda>x. 0) (\<lambda>x. 0)"
    using zero_weak zero_lp unfolding slp_w1p_pair_on_def by simp
  have zero_norm: "slp_w1p_norm_on a X (\<lambda>x. 0) (\<lambda>x. 0) = 0"
    by (simp add: slp_w1p_norm_on_def slp_restrict_field_def)
  have zero_integrand:
      "slp_cauchy_integrand SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c (\<lambda>x. 0)) z = (\<lambda>y. 0)" for z
    by (rule ext)
      (simp add: slp_cauchy_integrand_def slp_oscillatory_modulation_def)
  have zero_operator: "slp_partial_psi_inverse tau c (\<lambda>x. 0) = (\<lambda>x. 0)"
    by (rule ext)
      (simp add: slp_partial_psi_inverse_def slp_cauchy_transform_def
        zero_integrand)
  show ?thesis using zero_test zero_gradient zero_pair zero_norm zero_operator
    by blast
qed

section \<open>Uniform smooth-input gain in the reviewed Sobolev norm\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_test_function_w1p_partial_psi_gain:
  assumes a_lower: "1 < a" and a_upper: "a < 2"
  shows "\<exists>B::real. 0 < B \<and>
    (\<forall>tau R c f.
      2 \<le> tau \<and> 1 \<le> R * sqrt tau \<and>
        slp_test_function_on X f \<and>
        slp_w1p_pair_on a X f (slp_classical_gradient f) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm_class.norm (y - c) \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c f)
        \<le> B * inverse (sqrt tau) *
          slp_w1p_norm_on a X f (slp_classical_gradient f))"
proof -
  have zero_test: "slp_test_function_on X (\<lambda>x. 0)"
    using slp_w1p_zero_function_data by blast
  have zero_gradient: "slp_classical_gradient (\<lambda>x. 0) = (\<lambda>x. 0)"
    using slp_w1p_zero_function_data by blast
  have zero_pair: "slp_w1p_pair_on a X (\<lambda>x. 0) (\<lambda>x. 0)"
    using slp_w1p_zero_function_data by blast
  have zero_classical_pair:
      "slp_w1p_pair_on a X (\<lambda>x. 0) (slp_classical_gradient (\<lambda>x. 0))"
    using zero_pair by (simp only: zero_gradient)
  have zero_norm: "slp_w1p_norm_on a X (\<lambda>x. 0) (\<lambda>x. 0) = 0"
    using slp_w1p_zero_function_data by blast
  obtain B::real where B_positive: "0 < B"
    and pairwise_gain:
      "\<And>tau R c f g.
        2 \<le> tau \<Longrightarrow> 1 \<le> R * sqrt tau \<Longrightarrow>
        slp_test_function_on X f \<Longrightarrow>
        slp_w1p_pair_on a X f (slp_classical_gradient f) \<Longrightarrow>
        slp_test_function_on X g \<Longrightarrow>
        slp_w1p_pair_on a X g (slp_classical_gradient g) \<Longrightarrow>
        (\<And>y. f y - g y \<noteq> 0 \<Longrightarrow>
          norm_class.norm (y - c) \<le> R) \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (\<lambda>z. slp_partial_psi_inverse tau c f z -
            slp_partial_psi_inverse tau c g z) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>z. slp_partial_psi_inverse tau c f z -
            slp_partial_psi_inverse tau c g z)
          \<le> B * inverse (sqrt tau) *
            (slp_w1p_norm_on a X f (slp_classical_gradient f) +
              slp_w1p_norm_on a X g (slp_classical_gradient g))"
    using slp_test_function_pairwise_error_partial_psi_gain[
      OF a_lower a_upper zero_pair] by simp blast
  have smooth_gain:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c f)
        \<le> B * inverse (sqrt tau) *
          slp_w1p_norm_on a X f (slp_classical_gradient f)"
    if tau_lower: "2 \<le> tau" and normalized: "1 \<le> R * sqrt tau"
      and f_test: "slp_test_function_on X f"
      and f_pair: "slp_w1p_pair_on a X f (slp_classical_gradient f)"
      and support: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm_class.norm (y - c) \<le> R"
    for tau R c f
  proof -
    have zero_operator:
        "slp_partial_psi_inverse tau c (\<lambda>x. 0) = (\<lambda>x. 0)"
      using slp_w1p_zero_function_data by blast
    have difference_support:
        "\<And>y. f y - (0::complex) \<noteq> 0 \<Longrightarrow>
          norm_class.norm (y - c) \<le> R"
      using support by simp
    note application = pairwise_gain[OF tau_lower normalized f_test f_pair
      zero_test zero_classical_pair difference_support]
    show ?thesis
      using application by (simp add: zero_operator zero_gradient zero_norm)
  qed
  show ?thesis
    by (rule exI[of _ B], rule conjI[OF B_positive])
      (use smooth_gain in blast)
qed

section \<open>Uniform gain for the literal rough Sobolev representative\<close>

theorem slp_w1p_zero_pair_partial_psi_gain:
  assumes a_lower: "1 < a" and a_upper: "a < 2"
    and X_bounded: "bounded X"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau c f Df.
      2 \<le> tau \<and> slp_w1p_zero_pair_on a X f Df
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c (slp_restrict_field X f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c (slp_restrict_field X f))
        \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df)"
proof -
  obtain B::real where B_positive: "0 < B"
    and smooth_gain:
      "\<And>tau R c f.
        2 \<le> tau \<Longrightarrow> 1 \<le> R * sqrt tau \<Longrightarrow>
        slp_test_function_on X f \<Longrightarrow>
        slp_w1p_pair_on a X f (slp_classical_gradient f) \<Longrightarrow>
        (\<And>y. f y \<noteq> 0 \<Longrightarrow> norm_class.norm (y - c) \<le> R)
        \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c f)
          \<le> B * inverse (sqrt tau) *
            slp_w1p_norm_on a X f (slp_classical_gradient f)"
    using slp_test_function_w1p_partial_psi_gain[OF a_lower a_upper] by blast
  have a_one_le: "1 \<le> a" using a_lower by linarith
  have target_one_le: "1 \<le> aim_hls_target_exponent a"
    using slp_qstar_exponent_relations(1)[OF a_lower a_upper] by linarith
  have target_positive: "0 < aim_hls_target_exponent a"
    using target_one_le by linarith
  obtain A::real where X_bound:
      "\<And>y. y \<in> X \<Longrightarrow> norm_class.norm y \<le> A"
    using X_bounded unfolding bounded_iff by blast
  have reverse_power_functions:
      "(\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. v y - w y) x) powr a) =
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. w y - v y) x) powr a)" for v w
  proof (rule ext)
    fix x
    show "Real_Vector_Spaces.norm
        (slp_restrict_field X (\<lambda>y. v y - w y) x) powr a =
      Real_Vector_Spaces.norm
        (slp_restrict_field X (\<lambda>y. w y - v y) x) powr a"
      by (cases "x \<in> X")
        (simp_all add: slp_restrict_field_def norm_minus_commute)
  qed
  have tail_limit: "(G \<longlongrightarrow> 0) sequentially"
    if nonnegative: "\<And>n. 0 \<le> G n"
      and tails: "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N. G n < epsilon"
    for G :: "nat \<Rightarrow> real"
  proof (rule metric_LIMSEQ_I)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail: "\<forall>n\<ge>N. G n < epsilon"
      using tails epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N. dist (G n) 0 < epsilon"
      by (rule exI[of _ N]) (use tail nonnegative in auto)
  qed
  have rough_gain:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c (slp_restrict_field X f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c (slp_restrict_field X f))
        \<le> (192 * B) * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
    if tau_lower: "2 \<le> tau"
      and zero_pair: "slp_w1p_zero_pair_on a X f Df"
    for tau c f Df
  proof -
    let ?s = "aim_hls_target_exponent a"
    let ?T = "slp_partial_psi_inverse tau c (slp_restrict_field X f)"
    let ?W = "slp_w1p_norm_on a X f Df"
    let ?K = "B * inverse (sqrt tau)"
    let ?R = "1 + max 0 A + norm_class.norm c"
    obtain psi :: "nat \<Rightarrow> slp_scalar_field" where psi_pairs:
        "\<forall>n. slp_test_function_on X (psi n) \<and>
          slp_w1p_pair_on a X (psi n) (slp_classical_gradient (psi n))"
      and source_tails:
        "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          slp_w1p_norm_on a X (\<lambda>x. psi n x - f x)
            (\<lambda>x. slp_classical_gradient (psi n) x - Df x) < epsilon"
      and rough_output_lp: "aim_complex_lp_on_plane ?s ?T"
      and output_tails:
        "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          aim_complex_lp_norm ?s
            (\<lambda>z. slp_partial_psi_inverse tau c (psi n) z - ?T z)
            < epsilon"
      using slp_w1p_zero_pair_partial_psi_target_limit[
        OF a_lower a_upper X_bounded zero_pair] tau_lower by blast
    let ?E = "\<lambda>n. slp_w1p_norm_on a X (\<lambda>x. psi n x - f x)
      (\<lambda>x. slp_classical_gradient (psi n) x - Df x)"
    let ?F = "\<lambda>n. slp_partial_psi_inverse tau c (psi n)"
    let ?O = "\<lambda>n. aim_complex_lp_norm ?s (\<lambda>z. ?F n z - ?T z)"
    have rough_pair: "slp_w1p_pair_on a X f Df"
      using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
    have E_nonnegative: "0 \<le> ?E n" for n
      unfolding slp_w1p_norm_on_def by simp
    have O_nonnegative: "0 \<le> ?O n" for n
      unfolding aim_complex_lp_norm_def by simp
    have E_tends: "(?E \<longlongrightarrow> 0) sequentially"
      by (rule tail_limit[OF E_nonnegative source_tails])
    have O_tends: "(?O \<longlongrightarrow> 0) sequentially"
      by (rule tail_limit[OF O_nonnegative output_tails])
    have K_nonnegative: "0 \<le> ?K"
      using B_positive tau_lower by simp
    have R_lower: "1 \<le> ?R" by simp
    have R_nonnegative: "0 \<le> ?R" by simp
    have sqrt_lower: "1 \<le> sqrt tau"
      by (rule real_sqrt_ge_one) (use tau_lower in linarith)
    have R_product: "?R \<le> ?R * sqrt tau"
      using mult_left_mono[OF sqrt_lower R_nonnegative] by simp
    have normalized: "1 \<le> ?R * sqrt tau"
      by (rule order_trans[OF R_lower R_product])
    have psi_support: "norm_class.norm (y - c) \<le> ?R"
      if nonzero: "psi n y \<noteq> 0" for n y
    proof -
      have support_within: "closure {x. psi n x \<noteq> 0} \<subseteq> X"
        using psi_pairs unfolding slp_test_function_on_def by blast
      have y_in_support: "y \<in> closure {x. psi n x \<noteq> 0}"
        by (rule subsetD[OF closure_subset]) (use nonzero in simp)
      have y_in: "y \<in> X"
        by (rule subsetD[OF support_within y_in_support])
      have y_bound: "norm_class.norm y \<le> max 0 A"
        using X_bound[OF y_in] by linarith
      have triangle: "norm_class.norm (y - c) \<le>
          norm_class.norm y + norm_class.norm c"
        by (rule norm_triangle_ineq4)
      show ?thesis using triangle y_bound by linarith
    qed
    have smooth_estimate:
        "aim_complex_lp_on_plane ?s (?F n) \<and>
          aim_complex_lp_norm ?s (?F n) \<le>
            ?K * slp_w1p_norm_on a X (psi n) (slp_classical_gradient (psi n))"
      for n
      by (rule smooth_gain[OF tau_lower normalized
            conjunct1[OF spec[OF psi_pairs]]
            conjunct2[OF spec[OF psi_pairs]] psi_support])
    have source_norm_bound:
        "slp_w1p_norm_on a X (psi n) (slp_classical_gradient (psi n))
          \<le> 48 * (?W + ?E n)" for n
    proof -
      have reverse_error_pair:
          "slp_w1p_pair_on a X (\<lambda>x. f x - psi n x)
            (\<lambda>x. Df x - slp_classical_gradient (psi n) x)"
        by (rule slp_w1p_pair_on_diff[OF a_one_le rough_pair
              conjunct2[OF spec[OF psi_pairs]]])
      note function_power = reverse_power_functions[of f "psi n"]
      note zero_power = reverse_power_functions[
        of "\<lambda>x. Df x $ 0" "\<lambda>x. slp_classical_gradient (psi n) x $ 0"]
      note one_power = reverse_power_functions[
        of "\<lambda>x. Df x $ 1" "\<lambda>x. slp_classical_gradient (psi n) x $ 1"]
      have reverse_error_norm:
          "slp_w1p_norm_on a X (\<lambda>x. f x - psi n x)
            (\<lambda>x. Df x - slp_classical_gradient (psi n) x) = ?E n"
        unfolding slp_w1p_norm_on_def
        by (simp only: vector_minus_component function_power zero_power one_power)
      note source_triangle = slp_w1p_norm_on_diff_coarse_triangle[
        OF a_one_le rough_pair reverse_error_pair]
      show ?thesis using source_triangle reverse_error_norm by simp
    qed
    have output_majorant:
        "aim_complex_lp_norm ?s ?T \<le>
          4 * (?K * 48 * (?W + ?E n) + ?O n)" for n
    proof -
      have smooth_lp: "aim_complex_lp_on_plane ?s (?F n)"
        by (rule conjunct1[OF smooth_estimate])
      have error_lp: "aim_complex_lp_on_plane ?s (\<lambda>z. ?F n z - ?T z)"
        by (rule aim_complex_lp_on_plane_diff[
              OF target_positive smooth_lp rough_output_lp])
      note output_triangle = slp_complex_lp_diff_norm_coarse_triangle(2)[
        OF target_one_le smooth_lp error_lp]
      have first_bound:
          "aim_complex_lp_norm ?s ?T \<le>
            4 * (aim_complex_lp_norm ?s (?F n) + ?O n)"
        using output_triangle by simp
      have scaled_source:
          "?K * slp_w1p_norm_on a X (psi n) (slp_classical_gradient (psi n))
            \<le> ?K * (48 * (?W + ?E n))"
        by (rule mult_left_mono[OF source_norm_bound K_nonnegative])
      have smooth_bound:
          "aim_complex_lp_norm ?s (?F n) \<le> ?K * 48 * (?W + ?E n)"
        using order_trans[OF conjunct2[OF smooth_estimate] scaled_source]
        by (simp add: algebra_simps)
      have inside_bound:
          "aim_complex_lp_norm ?s (?F n) + ?O n \<le>
            ?K * 48 * (?W + ?E n) + ?O n"
        by (rule add_mono[OF smooth_bound order_refl])
      show ?thesis
        by (rule order_trans[OF first_bound], rule mult_left_mono[OF inside_bound])
          simp
    qed
    have majorant_tends:
        "((\<lambda>n. 4 * (?K * 48 * (?W + ?E n) + ?O n))
          \<longlongrightarrow> (192 * B) * inverse (sqrt tau) * ?W) sequentially"
    proof -
      have raw_limit:
          "((\<lambda>n. 4 * (?K * 48 * (?W + ?E n) + ?O n))
            \<longlongrightarrow> 4 * (?K * 48 * (?W + 0) + 0)) sequentially"
        using E_tends O_tends by (intro tendsto_intros)
      show ?thesis using raw_limit by (simp add: algebra_simps)
    qed
    have rough_bound:
        "aim_complex_lp_norm ?s ?T \<le>
          (192 * B) * inverse (sqrt tau) * ?W"
    proof (rule LIMSEQ_le_const[OF majorant_tends])
      show "\<exists>N. \<forall>n\<ge>N. aim_complex_lp_norm ?s ?T \<le>
          4 * (?K * 48 * (?W + ?E n) + ?O n)"
        by (rule exI[of _ 0]) (use output_majorant in blast)
    qed
    show ?thesis by (rule conjI[OF rough_output_lp rough_bound])
  qed
  have constant_positive: "0 < 192 * B" using B_positive by simp
  show ?thesis
    by (rule exI[of _ "192 * B"], rule conjI[OF constant_positive])
      (use rough_gain in blast)
qed

end

end
