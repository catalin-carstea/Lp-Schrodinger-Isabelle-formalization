theory Inverse_Schrodinger_Lp_Mixed_Product_Error_Uniform_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Finite_Kernel_Product_Dual_Norm"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Uniform boundedness on a fixed supported Lp subspace\<close>

lemma slp_center_average_error_family_uniform_bound:
  fixes G :: "real \<Rightarrow> slp_scalar_field"
    and a b A D :: real and Z :: "slp_point set"
  assumes a_lower: "1 < a" and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and support_measurable: "Z \<in> sets lborel"
    and support_bounded: "bounded Z"
    and A_nonnegative: "0 \<le> A" and D_nonnegative: "0 \<le> D"
    and kernel_integrable: "\<And>tau. 2 \<le> tau \<Longrightarrow> integrable lborel (G tau)"
    and kernel_lp: "\<And>tau. 2 \<le> tau \<Longrightarrow> aim_complex_lp_on_plane b (G tau)"
    and kernel_norm: "\<And>tau. 2 \<le> tau \<Longrightarrow> aim_complex_lp_norm b (G tau) \<le> D"
    and transpose_bound: "\<And>tau x. 2 \<le> tau \<Longrightarrow> x \<in> Z \<Longrightarrow>
      norm (slp_center_average tau (G tau) x) \<le> A"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau F.
    2 \<le> tau \<and> aim_complex_lp_on_plane a F \<and>
      (\<forall>x. F x \<noteq> 0 \<longrightarrow> x \<in> Z) \<longrightarrow>
    integrable lborel (\<lambda>x. (slp_center_average tau F x - F x) * G tau x) \<and>
    norm (integral\<^sup>L lborel
      (\<lambda>x. (slp_center_average tau F x - F x) * G tau x)) \<le>
        C * aim_complex_lp_norm a F)"
proof -
  let ?V = "measure lborel Z powr (1 / b)"
  let ?C = "A * ?V + D + 1"
  have AV_nonnegative: "0 \<le> A * ?V"
    by (intro mult_nonneg_nonneg A_nonnegative) simp
  have C_positive: "0 < ?C" using AV_nonnegative D_nonnegative by linarith
  show ?thesis
  proof (rule exI[of _ ?C], intro conjI allI impI)
    show "0 < ?C" by (rule C_positive)
    fix tau::real and F::slp_scalar_field
    assume input: "2 \<le> tau \<and> aim_complex_lp_on_plane a F \<and>
      (\<forall>x. F x \<noteq> 0 \<longrightarrow> x \<in> Z)"
    have tau: "2 \<le> tau" and F_lp: "aim_complex_lp_on_plane a F"
      using input by blast+
    have F_support: "x \<in> Z" if "F x \<noteq> 0" for x
      using input that by blast
    have local_transpose: "norm (slp_center_average tau (G tau) x) \<le> A"
      if "x \<in> Z" for x
      by (rule transpose_bound[OF tau that])
    note error = slp_center_average_error_functional_bound[OF
      a_lower b_lower conjugate support_measurable support_bounded F_lp
      F_support kernel_lp[OF tau] kernel_integrable[OF tau] A_nonnegative
      local_transpose]
    show "integrable lborel
        (\<lambda>x. (slp_center_average tau F x - F x) * G tau x)"
      by (rule error(1))
    have F_norm_nonnegative: "0 \<le> aim_complex_lp_norm a F"
      unfolding aim_complex_lp_norm_def by simp
    have scalar_bound: "A * ?V + aim_complex_lp_norm b (G tau) \<le> ?C"
      using kernel_norm[OF tau] by linarith
    have product_bound:
        "(A * ?V + aim_complex_lp_norm b (G tau)) * aim_complex_lp_norm a F \<le>
          ?C * aim_complex_lp_norm a F"
      by (rule mult_right_mono[OF scalar_bound F_norm_nonnegative])
    show "norm (integral\<^sup>L lborel
        (\<lambda>x. (slp_center_average tau F x - F x) * G tau x)) \<le>
          ?C * aim_complex_lp_norm a F"
      by (rule order_trans[OF error(2) product_bound])
  qed
qed


context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_mixed_finite_product_error_uniform_bound:
  fixes p :: real and Y Z :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and target_bounded: "bounded Y" and target_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
    and support_bounded: "bounded Z" and support_measurable: "Z \<in> sets lborel"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau F.
    2 \<le> tau \<and> aim_complex_lp_on_plane (slp_mixed_product_exponent p) F \<and>
      (\<forall>x. F x \<noteq> 0 \<longrightarrow> x \<in> Z) \<longrightarrow>
    integrable lborel (\<lambda>x. (slp_center_average tau F x - F x) *
      slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt x) \<and>
    norm (integral\<^sup>L lborel (\<lambda>x. (slp_center_average tau F x - F x) *
      slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
        tau Q cutoff q cutoff qt x)) \<le>
      C * aim_complex_lp_norm (slp_mixed_product_exponent p) F)"
proof -
  let ?a = "slp_mixed_product_exponent p"
  let ?b = "slp_mixed_product_dual_exponent p"
  let ?G = "\<lambda>tau. slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
    tau Q cutoff q cutoff qt"
  obtain D::real where D_positive: "0 < D"
    and D_data: "\<forall>tau. integrable lborel (?G tau) \<and>
      aim_complex_lp_on_plane ?b (?G tau) \<and> aim_complex_lp_norm ?b (?G tau) \<le> D"
    using slp_test_cutoff_finite_kernel_product_dual_cap[
      where 'i='i and 'j='j, OF p_lower p_upper target_bounded target_measurable
        cutoff_test q_lp qt_lp Q_lp cutoff_q cutoff_qt Q_support] by blast
  obtain T::real where T_positive: "0 < T"
    and T_data: "\<forall>tau center q qt Q.
      2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
        aim_complex_lp_on_plane p qt \<and> aim_complex_lp_on_plane p Q \<and>
        (\<forall>x. cutoff x * q x = q x) \<and>
        (\<forall>x. cutoff x * qt x = qt x) \<and> (\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y) \<longrightarrow>
      norm (slp_center_average tau
        (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
          tau Q cutoff q cutoff qt) center) \<le>
        T * aim_complex_lp_norm p Q * (aim_complex_lp_norm p q)^CARD('i) *
          (aim_complex_lp_norm p qt)^CARD('j)"
    using slp_finite_center_transpose_uniform_bound[
      where 'i='i and 'j='j, OF p_lower p_upper target_bounded
        target_measurable cutoff_test] by blast
  let ?A = "T * aim_complex_lp_norm p Q * (aim_complex_lp_norm p q)^CARD('i) *
    (aim_complex_lp_norm p qt)^CARD('j)"
  have A_nonnegative: "0 \<le> ?A"
    by (intro mult_nonneg_nonneg)
      (simp_all add: aim_complex_lp_norm_def less_imp_le[OF T_positive])
  have D_nonnegative: "0 \<le> D" using D_positive by simp
  have G_integrable: "integrable lborel (?G tau)" if "2 \<le> tau" for tau
    using D_data by blast
  have G_lp: "aim_complex_lp_on_plane ?b (?G tau)" if "2 \<le> tau" for tau
    using D_data by blast
  have G_norm: "aim_complex_lp_norm ?b (?G tau) \<le> D" if "2 \<le> tau" for tau
    using D_data by blast
  have transpose_bound: "norm (slp_center_average tau (?G tau) x) \<le> ?A"
    if tau: "2 \<le> tau" and x: "x \<in> Z" for tau x
  proof -
    have data: "2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
        aim_complex_lp_on_plane p qt \<and> aim_complex_lp_on_plane p Q \<and>
        (\<forall>x. cutoff x * q x = q x) \<and>
        (\<forall>x. cutoff x * qt x = qt x) \<and> (\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y)"
      using tau q_lp qt_lp Q_lp cutoff_q cutoff_qt Q_support by blast
    show ?thesis by (rule T_data[rule_format, OF data])
  qed
  note exponents = slp_mixed_product_duality_exponents[OF p_lower p_upper]
  show ?thesis
    by (rule slp_center_average_error_family_uniform_bound[OF
        exponents(2) exponents(3) exponents(4) support_measurable support_bounded
        A_nonnegative D_nonnegative G_integrable G_lp G_norm transpose_bound])
qed

end

end
