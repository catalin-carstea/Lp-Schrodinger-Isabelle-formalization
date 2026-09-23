theory Inverse_Schrodinger_Lp_Center_Error_Approximation_Transfer
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Supported_Value_Truncations"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exact differences of physical center-error functionals\<close>

lemma slp_center_average_diff:
  fixes tau :: real and f g :: slp_scalar_field
  assumes f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
  shows "slp_center_average tau (\<lambda>x. f x - g x) c =
      slp_center_average tau f c - slp_center_average tau g c"
proof -
  have f_kernel: "integrable lborel (\<lambda>x. slp_center_kernel tau c x * f x)"
    by (rule slp_center_kernel_integrable_mult[OF f_integrable])
  have g_kernel: "integrable lborel (\<lambda>x. slp_center_kernel tau c x * g x)"
    by (rule slp_center_kernel_integrable_mult[OF g_integrable])
  have difference_integral:
      "integral\<^sup>L lborel (\<lambda>x. slp_center_kernel tau c x * (f x - g x)) =
        integral\<^sup>L lborel (\<lambda>x. slp_center_kernel tau c x * f x) -
        integral\<^sup>L lborel (\<lambda>x. slp_center_kernel tau c x * g x)"
    by (simp only: right_diff_distrib Bochner_Integration.integral_diff[OF f_kernel g_kernel])
  show ?thesis
    unfolding slp_center_average_def
    by (subst difference_integral) (rule right_diff_distrib)
qed

lemma slp_center_error_pairing_diff:
  fixes tau :: real and f g kernel :: slp_scalar_field
  assumes f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
    and f_pairing_integrable:
      "integrable lborel (\<lambda>x. (slp_center_average tau f x - f x) * kernel x)"
    and g_pairing_integrable:
      "integrable lborel (\<lambda>x. (slp_center_average tau g x - g x) * kernel x)"
  shows "integral\<^sup>L lborel
      (\<lambda>x. (slp_center_average tau (\<lambda>y. f y - g y) x - (f x - g x)) * kernel x) =
    integral\<^sup>L lborel (\<lambda>x. (slp_center_average tau f x - f x) * kernel x) -
    integral\<^sup>L lborel (\<lambda>x. (slp_center_average tau g x - g x) * kernel x)"
proof -
  have pointwise:
      "(slp_center_average tau (\<lambda>y. f y - g y) x - (f x - g x)) * kernel x =
        (slp_center_average tau f x - f x) * kernel x -
        (slp_center_average tau g x - g x) * kernel x" for x
    by (simp add: slp_center_average_diff[OF f_integrable g_integrable] algebra_simps)
  show ?thesis
    by (simp only: pointwise
        Bochner_Integration.integral_diff[OF f_pairing_integrable g_pairing_integrable])
qed

section \<open>Sequence approximation transfers a uniformly bounded limit\<close>

lemma slp_uniform_pairing_sequence_limit:
  fixes target :: "real \<Rightarrow> complex"
    and approximant :: "nat \<Rightarrow> real \<Rightarrow> complex"
    and error_size :: "nat \<Rightarrow> real"
    and C :: real
  assumes error_decay: "error_size \<longlonglongrightarrow> 0"
    and uniform_difference:
      "\<And>tau n. 2 \<le> tau \<Longrightarrow>
        norm (target tau - approximant n tau) \<le> C * error_size n"
    and approximant_decay:
      "\<And>n. ((\<lambda>tau. approximant n tau) \<longlongrightarrow> 0) at_top"
  shows "(target \<longlongrightarrow> 0) at_top"
proof (unfold tendsto_iff, intro allI impI)
  fix epsilon :: real
  assume epsilon_positive: "0 < epsilon"
  have half_positive: "0 < epsilon / 2" using epsilon_positive by simp
  have scaled_error_decay: "(\<lambda>n. C * error_size n) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. C * error_size n) \<longlonglongrightarrow> C * 0"
      by (rule tendsto_mult[OF tendsto_const error_decay])
    then show ?thesis by simp
  qed
  obtain n :: nat where approximation_small: "C * error_size n < epsilon / 2"
    using order_tendstoD(2)[OF scaled_error_decay half_positive]
    by (auto simp: eventually_sequentially)
  have eventually_small:
      "eventually (\<lambda>tau. dist (approximant n tau) 0 < epsilon / 2) at_top"
    using approximant_decay[of n] half_positive unfolding tendsto_iff by blast
  have eventually_frequency: "eventually (\<lambda>tau::real. 2 \<le> tau) at_top"
    by (rule eventually_ge_at_top)
  show "eventually (\<lambda>tau. dist (target tau) 0 < epsilon) at_top"
    using eventually_small eventually_frequency
  proof eventually_elim
    fix tau
    assume small: "dist (approximant n tau) 0 < epsilon / 2"
      and frequency: "2 \<le> tau"
    have difference: "norm (target tau - approximant n tau) < epsilon / 2"
      using uniform_difference[OF frequency, of n] approximation_small by linarith
    have approximant_small: "norm (approximant n tau) < epsilon / 2"
      using small by (simp add: dist_norm)
    have "norm (target tau) \<le>
        norm (approximant n tau) + norm (target tau - approximant n tau)"
      by (rule norm_triangle_sub)
    also have "... < epsilon" using difference approximant_small by linarith
    finally show "dist (target tau) 0 < epsilon" by (simp add: dist_norm)
  qed
qed

end
