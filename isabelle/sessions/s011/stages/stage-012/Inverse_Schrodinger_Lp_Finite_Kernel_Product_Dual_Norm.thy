theory Inverse_Schrodinger_Lp_Finite_Kernel_Product_Dual_Norm
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Center_Error_Functional_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel_Product_Power_Integral_Bound"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Frequency-uniform product-dual norms for the literal finite kernel\<close>

context aim_planar_riesz_hls
begin

theorem slp_finite_kernel_product_dual_norm_bound:
  fixes tau B M p :: real and Y :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and target_measurable: "Y \<in> sets lborel"
    and target_bounded: "bounded Y"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> Y \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> M"
    and M_nonnegative: "0 \<le> M"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows "aim_complex_lp_norm (slp_mixed_product_dual_exponent p)
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt) \<le>
    (integral\<^sup>L lborel (\<lambda>x. enn2real
      (slp_mixed_center_density (2 * B) cutoff q qt (\<lambda>_. 1) (\<lambda>_. 1)
        CARD('i) CARD('j) Q x) powr slp_mixed_product_dual_exponent p)) powr
      (1 / slp_mixed_product_dual_exponent p)"
proof -
  let ?b = "slp_mixed_product_dual_exponent p"
  let ?G = "slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
    tau Q cutoff q cutoff qt"
  let ?D = "slp_mixed_center_density (2 * B) cutoff q qt
    (\<lambda>_. 1) (\<lambda>_. 1) CARD('i) CARD('j) Q"
  have power_bound:
      "integral\<^sup>L lborel (\<lambda>x. norm (?G x) powr ?b) \<le>
        integral\<^sup>L lborel (\<lambda>x. enn2real (?D x) powr ?b)"
    by (rule slp_mixed_center_finite_oscillatory_kernel_product_power_integral_bound[
        OF B_nonnegative p_lower p_upper target_measurable target_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound M_nonnegative
        Q_support cutoff_support q_support qt_support])
  have b_lower: "1 < ?b"
    by (rule slp_mixed_product_duality_exponents(3)[OF p_lower p_upper])
  have reciprocal_nonnegative: "0 \<le> 1 / ?b" using b_lower by simp
  have power_nonnegative:
      "0 \<le> integral\<^sup>L lborel (\<lambda>x. norm (?G x) powr ?b)"
    by (rule integral_nonneg_AE) simp
  show ?thesis unfolding aim_complex_lp_norm_def
    by (rule powr_mono2[OF reciprocal_nonnegative power_nonnegative power_bound])
qed


theorem slp_test_cutoff_finite_kernel_product_dual_cap:
  fixes p :: real and Y :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and target_bounded: "bounded Y" and target_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
  shows "\<exists>D::real. 0 < D \<and> (\<forall>tau.
    integrable lborel
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt) \<and>
    aim_complex_lp_on_plane (slp_mixed_product_dual_exponent p)
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
        tau Q cutoff q cutoff qt) \<and>
    aim_complex_lp_norm (slp_mixed_product_dual_exponent p)
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
        tau Q cutoff q cutoff qt) \<le> D)"
proof -
  obtain B::real where B_positive: "0 < B"
    and Y_bound: "\<And>x. x \<in> Y \<Longrightarrow> norm x \<le> B"
    by (rule bounded_normE[OF target_bounded]) blast
  have B_nonnegative: "0 \<le> B" using B_positive by simp
  have cutoff_plane: "slp_test_function_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by auto
  have cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    by (rule borel_measurable_integrable,
        rule slp_test_function_integrable_bounded(1)[OF cutoff_plane])
  have cutoff_range_bounded: "bounded (range cutoff)"
    by (rule slp_test_function_integrable_bounded(2)[OF cutoff_plane])
  obtain M::real where M_positive: "0 < M"
    and M_bound: "\<And>x. norm (cutoff x) \<le> M"
    using cutoff_range_bounded unfolding bounded_pos by blast
  have M_nonnegative: "0 \<le> M" using M_positive by simp
  have cutoff_in: "x \<in> Y" if "cutoff x \<noteq> 0" for x
    using cutoff_test closure_subset[of "{x. cutoff x \<noteq> 0}"] that
    unfolding slp_test_function_on_def by blast
  have cutoff_support: "norm x \<le> B" if "cutoff x \<noteq> 0" for x
    by (rule Y_bound[OF cutoff_in[OF that]])
  have potential_support: "norm x \<le> B"
    if nonzero: "f x \<noteq> 0" and identity: "\<forall>x. cutoff x * f x = f x"
    for f :: slp_scalar_field and x :: slp_point
  proof -
    have cutoff_nonzero: "cutoff x \<noteq> 0"
      using nonzero identity[rule_format, of x] by auto
    show ?thesis by (rule cutoff_support[OF cutoff_nonzero])
  qed
  have q_support: "norm x \<le> B" if "q x \<noteq> 0" for x
    by (rule potential_support[OF that cutoff_q])
  have qt_support: "norm x \<le> B" if "qt x \<noteq> 0" for x
    by (rule potential_support[OF that cutoff_qt])
  have Q_support: "norm x \<le> B" if "Q x \<noteq> 0" for x
    by (rule Y_bound[OF Q_in[OF that]])
  have Q_outside: "Q x = 0" if "x \<notin> Y" for x
    using Q_in that by blast
  have p_at_least_one: "1 \<le> p" using p_lower by simp
  have Q_integrable: "integrable lborel Q"
    by (rule slp_bounded_supported_lp_integrable[OF p_at_least_one
        target_measurable target_bounded Q_lp Q_in])
  let ?b = "slp_mixed_product_dual_exponent p"
  let ?G = "\<lambda>tau. slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
    tau Q cutoff q cutoff qt"
  let ?D = "(integral\<^sup>L lborel (\<lambda>x. enn2real
    (slp_mixed_center_density (2 * B) cutoff q qt (\<lambda>_. 1) (\<lambda>_. 1)
      CARD('i) CARD('j) Q x) powr ?b)) powr (1 / ?b)"
  have D_nonnegative: "0 \<le> ?D" by simp
  have G_integrable: "integrable lborel (?G tau)" for tau
    by (rule slp_mixed_center_finite_oscillatory_kernel_properties(3)[OF
        B_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp M_bound
        M_nonnegative Q_integrable Q_support cutoff_support q_support qt_support])
  have G_lp: "aim_complex_lp_on_plane ?b (?G tau)" for tau
    by (rule slp_mixed_center_finite_oscillatory_kernel_product_dual_lp[OF
        B_nonnegative p_lower p_upper target_measurable target_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside M_bound M_nonnegative
        Q_support cutoff_support q_support qt_support])
  have G_bound: "aim_complex_lp_norm ?b (?G tau) \<le> ?D" for tau
    by (rule slp_finite_kernel_product_dual_norm_bound[OF
        B_nonnegative p_lower p_upper target_measurable target_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside M_bound M_nonnegative
        Q_support cutoff_support q_support qt_support])
  show ?thesis
  proof (rule exI[of _ "?D + 1"], intro conjI allI)
    show "0 < ?D + 1" using D_nonnegative by linarith
    fix tau::real
    show "integrable lborel (?G tau)" by (rule G_integrable)
    show "aim_complex_lp_on_plane ?b (?G tau)" by (rule G_lp)
    show "aim_complex_lp_norm ?b (?G tau) \<le> ?D + 1"
      using G_bound[of tau] by linarith
  qed
qed

end

end
