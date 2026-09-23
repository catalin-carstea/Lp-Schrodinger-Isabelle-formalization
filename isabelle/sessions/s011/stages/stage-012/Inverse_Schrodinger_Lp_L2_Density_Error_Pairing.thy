theory Inverse_Schrodinger_Lp_L2_Density_Error_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Finite_Kernel_L2_Dominator"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Center_Error_L2_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Complex pairings dominated by a positive L2 density\<close>

lemma slp_l2_density_complex_pairing_bound:
  fixes density :: "slp_point \<Rightarrow> ennreal"
    and error kernel :: slp_scalar_field
  assumes density_l2: "slp_positive_ennreal_lp_on_plane 2 density"
    and error_l2: "aim_complex_lp_on_plane 2 error"
    and kernel_measurable: "kernel \<in> borel_measurable lborel"
    and dominated: "AE x in lborel. ennreal (norm (kernel x)) \<le> density x"
  shows "integrable lborel (\<lambda>x. error x * kernel x)"
    "ennreal (norm (integral\<^sup>L lborel (\<lambda>x. error x * kernel x))) \<le>
      (\<integral>\<^sup>+x. density x * ennreal (norm (error x)) \<partial>lborel)"
proof -
  let ?f = "\<lambda>x. error x * kernel x"
  let ?P = "\<integral>\<^sup>+x. density x * ennreal (norm (error x)) \<partial>lborel"
  have error_measurable: "error \<in> borel_measurable lborel"
    using error_l2 unfolding aim_complex_lp_on_plane_def by blast
  have product_measurable: "?f \<in> borel_measurable lborel"
    using error_measurable kernel_measurable by measurable
  have pairing_finite: "?P < top_class.top"
    by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[
        where q=2 and r=2, OF _ _ _ density_l2 error_l2]) simp_all
  have pointwise_bound: "AE x in lborel.
      ennreal (norm (?f x)) \<le> density x * ennreal (norm (error x))"
    using dominated
  proof eventually_elim
    fix x
    assume x: "ennreal (norm (kernel x)) \<le> density x"
    have "ennreal (norm (error x)) * ennreal (norm (kernel x)) \<le>
        ennreal (norm (error x)) * density x"
      by (rule mult_left_mono[OF x]) simp
    then show "ennreal (norm (?f x)) \<le> density x * ennreal (norm (error x))"
      by (simp add: norm_mult ennreal_mult mult.commute)
  qed
  have integral_bound: "(\<integral>\<^sup>+x. ennreal (norm (?f x)) \<partial>lborel) \<le> ?P"
    by (rule nn_integral_mono_AE[OF pointwise_bound])
  have norm_integral_finite:
      "(\<integral>\<^sup>+x. ennreal (norm (?f x)) \<partial>lborel) < top_class.top"
    by (rule order_le_less_trans[OF integral_bound pairing_finite])
  have product_integrable: "integrable lborel ?f"
    using product_measurable norm_integral_finite
    by (simp add: Bochner_Integration.integrable_iff_bounded)
  show "integrable lborel ?f" by (rule product_integrable)
  have norm_bound: "ennreal (norm (integral\<^sup>L lborel ?f)) \<le>
      (\<integral>\<^sup>+x. ennreal (norm (?f x)) \<partial>lborel)"
    by (rule Bochner_Integration.integral_norm_bound_ennreal[OF product_integrable])
  show "ennreal (norm (integral\<^sup>L lborel ?f)) \<le> ?P"
    by (rule order_trans[OF norm_bound integral_bound])
qed

lemma slp_l2_density_complex_pairing_tendsto_zero:
  fixes density :: "slp_point \<Rightarrow> ennreal"
    and error kernel :: "'a \<Rightarrow> slp_scalar_field"
    and F :: "'a filter"
  assumes density_l2: "slp_positive_ennreal_lp_on_plane 2 density"
    and error_l2: "\<And>i. aim_complex_lp_on_plane 2 (error i)"
    and kernel_measurable: "\<And>i. kernel i \<in> borel_measurable lborel"
    and dominated: "\<And>i. AE x in lborel. ennreal (norm (kernel i x)) \<le> density x"
    and error_square_decay:
      "((\<lambda>i. \<integral>\<^sup>+x. ennreal (norm (error i x)) ^ 2 \<partial>lborel)
        \<longlongrightarrow> 0) F"
  shows "((\<lambda>i. integral\<^sup>L lborel (\<lambda>x. error i x * kernel i x))
      \<longlongrightarrow> 0) F"
proof -
  let ?I = "\<lambda>i. integral\<^sup>L lborel (\<lambda>x. error i x * kernel i x)"
  let ?P = "\<lambda>i. \<integral>\<^sup>+x. density x * ennreal (norm (error i x)) \<partial>lborel"
  have pairing_decay: "(?P \<longlongrightarrow> 0) F"
    by (rule slp_positive_ennreal_complex_l2_pairing_tendsto_zero[
        OF density_l2 error_l2 error_square_decay])
  have norm_bound: "ennreal (norm (?I i)) \<le> ?P i" for i
    by (rule slp_l2_density_complex_pairing_bound(2)[OF
        density_l2 error_l2 kernel_measurable dominated])
  have norm_ennreal_decay: "((\<lambda>i. ennreal (norm (?I i))) \<longlongrightarrow> 0) F"
    by (rule tendsto_sandwich[where f="\<lambda>_. 0" and h="?P"])
      (use norm_bound pairing_decay in auto)
  have norm_real_decay: "((\<lambda>i. norm (?I i)) \<longlongrightarrow> 0) F"
  proof -
    have cast_decay:
        "((\<lambda>i. ennreal (norm (?I i))) \<longlongrightarrow> ennreal 0) F"
      using norm_ennreal_decay by simp
    show ?thesis by (rule tendsto_ennrealD[OF cast_decay]) simp_all
  qed
  show ?thesis using norm_real_decay by (rule tendsto_norm_zero_cancel)
qed

section \<open>The actual undamped physical error on L1 intersect L2\<close>

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_center_error_l2_density_pairing_tendsto_zero:
  fixes density :: "slp_point \<Rightarrow> ennreal"
    and kernel :: "real \<Rightarrow> slp_scalar_field"
    and f :: slp_scalar_field
  assumes density_l2: "slp_positive_ennreal_lp_on_plane 2 density"
    and kernel_measurable: "\<And>tau. kernel tau \<in> borel_measurable lborel"
    and dominated: "\<And>tau. AE x in lborel. ennreal (norm (kernel tau x)) \<le> density x"
    and f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
  shows "((\<lambda>tau. integral\<^sup>L lborel
      (\<lambda>x. (slp_center_average tau f x - f x) * kernel tau x))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?error = "\<lambda>tau x. if 0 < tau then slp_center_average tau f x - f x else 0"
  have error_l2: "aim_complex_lp_on_plane 2 (?error tau)" for tau
  proof (cases "0 < tau")
    case True
    have "aim_complex_lp_on_plane 2 (\<lambda>x. slp_center_average tau f x - f x)"
      by (rule slp_center_average_error_l2_l1_l2[OF True f_integrable f_l2])
    then show ?thesis using True by simp
  next
    case False
    show ?thesis using False unfolding aim_complex_lp_on_plane_def by simp
  qed
  have tau_positive: "eventually (\<lambda>tau::real. 0 < tau) at_top" by simp
  have raw_square_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x. ennreal (norm
          (slp_center_average tau f x - f x)) ^ 2 \<partial>lborel)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_center_average_error_square_nn_integral_tendsto_zero[
        OF f_integrable f_l2])
  have square_eventual:
      "eventually (\<lambda>tau. (\<integral>\<^sup>+x. ennreal (norm (?error tau x)) ^ 2 \<partial>lborel)
        = (\<integral>\<^sup>+x. ennreal (norm
          (slp_center_average tau f x - f x)) ^ 2 \<partial>lborel)) at_top"
    using tau_positive by eventually_elim simp
  have error_square_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x. ennreal (norm (?error tau x)) ^ 2 \<partial>lborel)
        \<longlongrightarrow> 0) at_top"
    using tendsto_cong[OF square_eventual] raw_square_decay by blast
  have clipped_decay:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>x. ?error tau x * kernel tau x))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_l2_density_complex_pairing_tendsto_zero[
        OF density_l2 error_l2 kernel_measurable dominated error_square_decay])
  have pairing_eventual:
      "eventually (\<lambda>tau. integral\<^sup>L lborel (\<lambda>x. ?error tau x * kernel tau x)
        = integral\<^sup>L lborel
          (\<lambda>x. (slp_center_average tau f x - f x) * kernel tau x)) at_top"
    using tau_positive by eventually_elim simp
  show ?thesis using tendsto_cong[OF pairing_eventual] clipped_decay by blast
qed

end

end
