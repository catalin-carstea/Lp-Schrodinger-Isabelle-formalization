theory Inverse_Schrodinger_Lp_Mixed_Weighted_Product_Error
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Cauchy_Product_Error"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Kernel"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Unit-terminal weighted kernels and the product error\<close>

lemma slp_mixed_unit_terminal_weighted_kernel:
  fixes frequency :: real and center :: slp_point
    and Q left_cutoff q right_cutoff qt H :: slp_scalar_field
  shows "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i::finite) TYPE('j::finite) frequency Q left_cutoff q (\<lambda>_. 1)
      right_cutoff qt (\<lambda>_. 1) H center =
    H center * slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
      frequency Q left_cutoff q right_cutoff qt center"
proof -
  let ?raw = "slp_parameterized_real_phase_integrand frequency
    slp_mixed_center_finite_residual
    (slp_mixed_center_finite_complex_amplitude Q left_cutoff q right_cutoff qt)
    center :: ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  have integrand:
      "(slp_mixed_center_finite_weighted_oscillatory_integrand frequency
        Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1) H center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) =
        (\<lambda>coordinates. H center * ?raw coordinates)"
    by (rule ext)
      (simp add: slp_mixed_center_finite_weighted_oscillatory_integrand_def
        slp_parameterized_real_phase_integrand_def
        slp_mixed_center_finite_weighted_complex_amplitude_def
        slp_mixed_center_finite_complex_amplitude_def algebra_simps)
  show ?thesis
    unfolding slp_mixed_center_finite_weighted_oscillatory_kernel_def
      slp_mixed_center_finite_oscillatory_kernel_def
      slp_mixed_center_finite_fiber_integral_def
      slp_parameterized_real_phase_fiber_integral_def
      slp_parameterized_complex_fiber_integral_def
    by (simp only: integrand Bochner_Integration.integral_mult_right_zero)
qed

context slp_mixed_center_error_hls_plancherel
begin

theorem slp_mixed_weighted_cauchy_product_error:
  fixes p :: real and Y :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and target_bounded: "bounded Y" and target_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
    and phi_test: "slp_test_function_on UNIV phi"
  shows integrability:
    "\<forall>tau. 2 \<le> tau \<longrightarrow> integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_kernel
        TYPE('i::finite) TYPE('j::finite) tau Q cutoff q (\<lambda>_. 1)
        cutoff qt (\<lambda>_. 1)
        (\<lambda>c. slp_center_average tau
          (\<lambda>x. phi x * (slp_cauchy_transform left_orientation q x *
            slp_cauchy_transform right_orientation qt x)) c -
          phi c * (slp_cauchy_transform left_orientation q c *
            slp_cauchy_transform right_orientation qt c)))"
    and decay:
    "((\<lambda>tau. integral\<^sup>L lborel
      (slp_mixed_center_finite_weighted_oscillatory_kernel
        TYPE('i) TYPE('j) tau Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1)
        (\<lambda>c. slp_center_average tau
          (\<lambda>x. phi x * (slp_cauchy_transform left_orientation q x *
            slp_cauchy_transform right_orientation qt x)) c -
          phi c * (slp_cauchy_transform left_orientation q c *
            slp_cauchy_transform right_orientation qt c))))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?F = "\<lambda>x. phi x * (slp_cauchy_transform left_orientation q x *
    slp_cauchy_transform right_orientation qt x)"
  let ?H = "\<lambda>tau c. slp_center_average tau ?F c - ?F c"
  let ?G = "\<lambda>tau. slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
    tau Q cutoff q cutoff qt"
  let ?W = "\<lambda>tau. slp_mixed_center_finite_weighted_oscillatory_kernel
    TYPE('i) TYPE('j) tau Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (?H tau)"
  have kernel: "?W tau = (\<lambda>x. ?H tau x * ?G tau x)" for tau
    by (rule ext) (rule slp_mixed_unit_terminal_weighted_kernel)
  let ?Z = "closure {x. phi x \<noteq> 0}"
  have Z_compact: "compact ?Z"
    using phi_test unfolding slp_test_function_on_def by blast
  have Z_bounded: "bounded ?Z" by (rule compact_imp_bounded[OF Z_compact])
  have Z_borel: "?Z \<in> sets borel"
    by (rule borel_closed[OF closed_closure])
  have Z_measurable: "?Z \<in> sets lborel"
    using Z_borel by (simp only: sets_lborel)
  have F_lp: "aim_complex_lp_on_plane (slp_mixed_product_exponent p) ?F"
    using slp_test_two_cauchy_product_half_hls_target_lp[
      where left_orientation=left_orientation and right_orientation=right_orientation,
      OF p_lower p_upper q_lp qt_lp phi_test]
    by (simp only: slp_mixed_product_exponent_def)
  have F_support: "\<forall>x. ?F x \<noteq> 0 \<longrightarrow> x \<in> ?Z"
    using closure_subset[of "{x. phi x \<noteq> 0}"] by auto
  have integrable_family:
      "\<forall>tau h. 2 \<le> tau \<and>
        aim_complex_lp_on_plane (slp_mixed_product_exponent p) h \<and>
        (\<forall>x. h x \<noteq> 0 \<longrightarrow> x \<in> ?Z) \<longrightarrow>
        integrable lborel
          (\<lambda>x. (slp_center_average tau h x - h x) * ?G tau x)"
    using slp_mixed_finite_product_error_uniform_bound[
      where 'i='i and 'j='j and Z="?Z", OF p_lower p_upper target_bounded
        target_measurable cutoff_test q_lp qt_lp Q_lp cutoff_q cutoff_qt
        Q_support Z_bounded Z_measurable] by blast
  show "\<forall>tau. 2 \<le> tau \<longrightarrow> integrable lborel (?W tau)"
  proof (intro allI impI)
    fix tau::real
    assume frequency: "2 \<le> tau"
    have "integrable lborel (\<lambda>x. ?H tau x * ?G tau x)"
      using integrable_family[rule_format, of tau "?F"] frequency F_lp F_support
      by blast
    then show "integrable lborel (?W tau)" by (simp only: kernel)
  qed
  have limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>x. ?H tau x * ?G tau x))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_mixed_cauchy_product_error_tendsto_zero[
        OF p_lower p_upper target_bounded target_measurable cutoff_test
          q_lp qt_lp Q_lp cutoff_q cutoff_qt Q_support phi_test])
  show "((\<lambda>tau. integral\<^sup>L lborel (?W tau)) \<longlongrightarrow> 0) at_top"
    using limit by (simp only: kernel)
qed

end


end
