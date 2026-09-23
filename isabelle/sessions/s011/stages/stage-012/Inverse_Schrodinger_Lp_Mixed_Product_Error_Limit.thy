theory Inverse_Schrodinger_Lp_Mixed_Product_Error_Limit
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Center_Error_Approximation_Transfer"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Supported Lp convergence of the physical product error\<close>

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_supported_center_error_lp_limit:
  fixes a C :: real and Z :: "slp_point set"
    and density :: "slp_point \<Rightarrow> ennreal"
    and kernel :: "real \<Rightarrow> slp_scalar_field"
    and f :: slp_scalar_field
  assumes exponent_lower: "1 < a"
    and set_measurable: "Z \<in> sets lborel"
    and set_bounded: "bounded Z"
    and field_lp: "aim_complex_lp_on_plane a f"
    and field_support: "\<And>x. f x \<noteq> 0 \<Longrightarrow> x \<in> Z"
    and density_l2: "slp_positive_ennreal_lp_on_plane 2 density"
    and kernel_measurable: "\<And>tau. kernel tau \<in> borel_measurable lborel"
    and dominated: "\<And>tau. AE x in lborel. ennreal (norm (kernel tau x)) \<le> density x"
    and uniform_integrability:
      "\<And>tau h. 2 \<le> tau \<Longrightarrow> aim_complex_lp_on_plane a h \<Longrightarrow>
        (\<forall>x. h x \<noteq> 0 \<longrightarrow> x \<in> Z) \<Longrightarrow>
        integrable lborel (\<lambda>x. (slp_center_average tau h x - h x) * kernel tau x)"
    and uniform_bound:
      "\<And>tau h. 2 \<le> tau \<Longrightarrow> aim_complex_lp_on_plane a h \<Longrightarrow>
        (\<forall>x. h x \<noteq> 0 \<longrightarrow> x \<in> Z) \<Longrightarrow>
        norm (integral\<^sup>L lborel
          (\<lambda>x. (slp_center_average tau h x - h x) * kernel tau x)) \<le>
        C * aim_complex_lp_norm a h"
  shows "((\<lambda>tau. integral\<^sup>L lborel
      (\<lambda>x. (slp_center_average tau f x - f x) * kernel tau x))
      \<longlongrightarrow> 0) at_top"
proof -
  have a_positive: "0 < a" using exponent_lower by simp
  obtain g :: "nat \<Rightarrow> slp_scalar_field" where
      g_data: "\<forall>n. aim_complex_lp_on_plane a (g n) \<and> integrable lborel (g n) \<and>
        aim_complex_lp_on_plane 2 (g n) \<and> (\<forall>x. g n x \<noteq> 0 \<longrightarrow> x \<in> Z)"
    and approximation:
      "(\<lambda>n. aim_complex_lp_norm a (\<lambda>x. f x - g n x)) \<longlonglongrightarrow> 0"
    using slp_supported_l1_l2_value_approximation[OF a_positive
      set_measurable set_bounded field_lp field_support] by blast
  have g_lp: "aim_complex_lp_on_plane a (g n)" for n using g_data by blast
  have g_integrable: "integrable lborel (g n)" for n using g_data by blast
  have g_l2: "aim_complex_lp_on_plane 2 (g n)" for n using g_data by blast
  have g_support: "\<forall>x. g n x \<noteq> 0 \<longrightarrow> x \<in> Z" for n
    using g_data by blast
  have f_support: "\<forall>x. f x \<noteq> 0 \<longrightarrow> x \<in> Z"
    using field_support by blast
  have f_integrable: "integrable lborel f"
    by (rule slp_bounded_supported_lp_integrable[
        where p=a and Y=Z, OF _ set_measurable set_bounded field_lp field_support])
      (use exponent_lower in simp)
  let ?I = "\<lambda>tau h. integral\<^sup>L lborel
    (\<lambda>x. (slp_center_average tau h x - h x) * kernel tau x)"
  have approximant_decay: "((\<lambda>tau. ?I tau (g n)) \<longlongrightarrow> 0) at_top" for n
    by (rule slp_center_error_l2_density_pairing_tendsto_zero[
        OF density_l2 kernel_measurable dominated g_integrable g_l2])
  have difference_bound:
      "norm (?I tau f - ?I tau (g n)) \<le>
        C * aim_complex_lp_norm a (\<lambda>x. f x - g n x)"
    if frequency: "2 \<le> tau" for tau n
  proof -
    have error_lp: "aim_complex_lp_on_plane a (\<lambda>x. f x - g n x)"
      by (rule aim_complex_lp_on_plane_diff[OF a_positive field_lp g_lp])
    have error_support: "\<forall>x. f x - g n x \<noteq> 0 \<longrightarrow> x \<in> Z"
    proof (intro allI impI)
      fix x
      assume nonzero: "f x - g n x \<noteq> 0"
      show "x \<in> Z"
      proof (rule ccontr)
        assume outside: "x \<notin> Z"
        have f_zero: "f x = 0" using field_support[of x] outside by blast
        have g_zero: "g n x = 0" using g_support[of n] outside by blast
        show False using nonzero f_zero g_zero by simp
      qed
    qed
    have f_pairing: "integrable lborel
        (\<lambda>x. (slp_center_average tau f x - f x) * kernel tau x)"
      by (rule uniform_integrability[OF frequency field_lp f_support])
    have g_pairing: "integrable lborel
        (\<lambda>x. (slp_center_average tau (g n) x - g n x) * kernel tau x)"
      by (rule uniform_integrability[OF frequency g_lp g_support])
    have identity: "?I tau (\<lambda>x. f x - g n x) = ?I tau f - ?I tau (g n)"
      by (rule slp_center_error_pairing_diff[OF
          f_integrable g_integrable f_pairing g_pairing])
    have bound: "norm (?I tau (\<lambda>x. f x - g n x)) \<le>
        C * aim_complex_lp_norm a (\<lambda>x. f x - g n x)"
      by (rule uniform_bound[OF frequency error_lp error_support])
    show ?thesis using bound by (simp only: identity)
  qed
  show ?thesis
    by (rule slp_uniform_pairing_sequence_limit[
        OF approximation difference_bound approximant_decay])
qed

end

section \<open>Literal positive-order mixed-kernel product error\<close>

locale slp_mixed_center_error_hls_plancherel =
  slp_qstar_centered_smooth_far_hls_context +
  hormander_euclidean_l2_fourier_plancherel

context slp_mixed_center_error_hls_plancherel
begin

theorem slp_mixed_finite_product_error_tendsto_zero:
  fixes p :: real and Y Z :: "slp_point set"
    and cutoff q qt Q F :: slp_scalar_field
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
    and F_lp: "aim_complex_lp_on_plane (slp_mixed_product_exponent p) F"
    and F_support: "\<And>x. F x \<noteq> 0 \<Longrightarrow> x \<in> Z"
  shows "((\<lambda>tau. integral\<^sup>L lborel
    (\<lambda>x. (slp_center_average tau F x - F x) *
      slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt x)) \<longlongrightarrow> 0) at_top"
proof -
  let ?a = "slp_mixed_product_exponent p"
  let ?G = "\<lambda>tau. slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
    tau Q cutoff q cutoff qt"
  obtain C::real where C_positive: "0 < C"
    and C_data: "\<forall>tau h.
      2 \<le> tau \<and> aim_complex_lp_on_plane ?a h \<and>
        (\<forall>x. h x \<noteq> 0 \<longrightarrow> x \<in> Z) \<longrightarrow>
      integrable lborel (\<lambda>x. (slp_center_average tau h x - h x) * ?G tau x) \<and>
      norm (integral\<^sup>L lborel
        (\<lambda>x. (slp_center_average tau h x - h x) * ?G tau x)) \<le>
          C * aim_complex_lp_norm ?a h"
    using slp_mixed_finite_product_error_uniform_bound[
      where 'i='i and 'j='j and Z=Z, OF p_lower p_upper target_bounded
        target_measurable cutoff_test q_lp qt_lp Q_lp cutoff_q cutoff_qt
        Q_support support_bounded support_measurable] by blast
  obtain density :: "slp_point \<Rightarrow> ennreal" where
      density_l2: "slp_positive_ennreal_lp_on_plane 2 density"
    and density_data: "\<forall>tau. ?G tau \<in> borel_measurable lborel \<and>
      (AE x in lborel. ennreal (norm (?G tau x)) \<le> density x)"
    using slp_test_cutoff_finite_kernel_l2_dominator[
      where 'i='i and 'j='j, OF p_lower p_upper target_bounded target_measurable
        cutoff_test q_lp qt_lp Q_lp cutoff_q cutoff_qt Q_support] by blast
  have measurable: "?G tau \<in> borel_measurable lborel" for tau
    using density_data by blast
  have dominated: "AE x in lborel. ennreal (norm (?G tau x)) \<le> density x" for tau
    using density_data by blast
  have pairing_integrable:
      "integrable lborel (\<lambda>x. (slp_center_average tau h x - h x) * ?G tau x)"
    if "2 \<le> tau" and "aim_complex_lp_on_plane ?a h"
      and "\<forall>x. h x \<noteq> 0 \<longrightarrow> x \<in> Z" for tau h
    using C_data[rule_format, of tau h] that by blast
  have pairing_bound:
      "norm (integral\<^sup>L lborel
        (\<lambda>x. (slp_center_average tau h x - h x) * ?G tau x)) \<le>
          C * aim_complex_lp_norm ?a h"
    if "2 \<le> tau" and "aim_complex_lp_on_plane ?a h"
      and "\<forall>x. h x \<noteq> 0 \<longrightarrow> x \<in> Z" for tau h
    using C_data[rule_format, of tau h] that by blast
  show ?thesis
    by (rule slp_supported_center_error_lp_limit[
        OF slp_mixed_product_duality_exponents(2)[OF p_lower p_upper]
          support_measurable support_bounded F_lp F_support density_l2
          measurable dominated pairing_integrable pairing_bound])
qed

end


end
