theory Inverse_Schrodinger_Lp_Fourier_Continuity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Born_Conditional_Cancellation"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Continuous representatives for Fourier inversion\<close>

lemma slp_fourier_transform_continuous:
  fixes f :: slp_scalar_field
  assumes f_integrable: "integrable lborel f"
  shows "continuous_on UNIV (slp_fourier_transform f)"
proof (rule continuous_on_sequentiallyI)
  fix u :: "nat \<Rightarrow> slp_point" and a :: slp_point
  assume u_in: "\<forall>n. u n \<in> UNIV" and a_in: "a \<in> UNIV"
    and u_limit: "u \<longlonglongrightarrow> a"
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_integrable by measurable
  have target_measurable:
      "(\<lambda>x. slp_fourier_phase a x * f x) \<in> borel_measurable lborel"
    using f_measurable slp_fourier_phase_measurable[of a] by measurable
  have sequence_measurable:
      "(\<lambda>x. slp_fourier_phase (u n) x * f x) \<in> borel_measurable lborel" for n
    using f_measurable slp_fourier_phase_measurable[of "u n"] by measurable
  have bound_integrable: "integrable lborel (\<lambda>x. norm (f x))"
    using f_integrable by simp
  have pointwise:
      "AE x in lborel. (\<lambda>n. slp_fourier_phase (u n) x * f x)
        \<longlonglongrightarrow> slp_fourier_phase a x * f x"
    unfolding slp_fourier_phase_def
    using u_limit by (intro AE_I2 tendsto_intros)
  have bound:
      "AE x in lborel. norm (slp_fourier_phase (u n) x * f x)
        \<le> norm (f x)" for n
    by (simp add: norm_mult)
  show "(\<lambda>n. slp_fourier_transform f (u n))
      \<longlonglongrightarrow> slp_fourier_transform f a"
    unfolding slp_fourier_transform_def
    by (rule integral_dominated_convergence[OF target_measurable
        sequence_measurable bound_integrable pointwise bound])
qed

lemma slp_center_average_continuous:
  fixes f :: slp_scalar_field
  assumes f_integrable: "integrable lborel f"
  shows "continuous_on UNIV (slp_center_average tau f)"
proof (rule continuous_on_sequentiallyI)
  fix u :: "nat \<Rightarrow> slp_point" and a :: slp_point
  assume u_in: "\<forall>n. u n \<in> UNIV" and a_in: "a \<in> UNIV"
    and u_limit: "u \<longlonglongrightarrow> a"
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_integrable by measurable
  have target_measurable:
      "(\<lambda>x. slp_center_kernel tau a x * f x) \<in> borel_measurable lborel"
    using f_measurable slp_center_kernel_measurable[of tau a] by measurable
  have sequence_measurable:
      "(\<lambda>x. slp_center_kernel tau (u n) x * f x) \<in> borel_measurable lborel" for n
    using f_measurable slp_center_kernel_measurable[of tau "u n"] by measurable
  have bound_integrable: "integrable lborel (\<lambda>x. norm (f x))"
    using f_integrable by simp
  have pointwise:
      "AE x in lborel. (\<lambda>n. slp_center_kernel tau (u n) x * f x)
        \<longlonglongrightarrow> slp_center_kernel tau a x * f x"
    unfolding slp_center_kernel_def slp_center_phase_def
    using u_limit by (intro AE_I2 tendsto_intros)
  have bound:
      "AE x in lborel. norm (slp_center_kernel tau (u n) x * f x)
        \<le> norm (f x)" for n
    unfolding slp_center_kernel_def
    by (simp add: norm_mult norm_exp_i_times)
  have integral_limit:
      "(\<lambda>n. integral\<^sup>L lborel (\<lambda>x. slp_center_kernel tau (u n) x * f x))
        \<longlonglongrightarrow> integral\<^sup>L lborel (\<lambda>x. slp_center_kernel tau a x * f x)"
    by (rule integral_dominated_convergence[OF target_measurable
        sequence_measurable bound_integrable pointwise bound])
  show "(\<lambda>n. slp_center_average tau f (u n))
      \<longlonglongrightarrow> slp_center_average tau f a"
    unfolding slp_center_average_def
    using integral_limit by (intro tendsto_intros)
qed

lemma slp_continuous_ae_eq:
  fixes f g :: slp_scalar_field
  assumes f_continuous: "continuous_on UNIV f"
    and g_continuous: "continuous_on UNIV g"
    and equality: "AE x in lborel. f x = g x"
  shows "f x = g x"
proof -
  have closed_equal: "closed {x. f x = g x}"
    by (rule closed_Collect_eq[OF f_continuous g_continuous])
  have almost_equal: "AE x in lebesgue. x \<in> {x. f x = g x}"
    using AE_completion[OF equality] by simp
  show ?thesis using mem_closed_if_AE_lebesgue[OF closed_equal almost_equal] by simp
qed

end
