theory Inverse_Schrodinger_Lp_Damped_Center_Average_Limit
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Damped_Center_Kernel_Limit"
begin

section \<open>Removal of damping from the physical center average\<close>

definition slp_damped_center_average ::
  "real \<Rightarrow> real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
    slp_point \<Rightarrow> complex"
where
  "slp_damped_center_average eps tau f c =
    of_real (tau / pi) *
      integral\<^sup>L lborel
        (\<lambda>z. slp_damped_center_kernel eps tau (z - c) * f z)"

lemma slp_damped_center_average_integrand_integrable:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes eps_nonnegative: "0 \<le> eps"
    and f_integrable: "integrable lborel f"
  shows "integrable lborel
    (\<lambda>z. slp_damped_center_kernel eps tau (z - c) * f z)"
proof (rule Bochner_Integration.integrable_bound[OF f_integrable])
  show "(\<lambda>z. slp_damped_center_kernel eps tau (z - c) * f z) \<in>
      borel_measurable lborel"
    using f_integrable by measurable
  show "AE z in lborel.
      norm_class.norm
        (slp_damped_center_kernel eps tau (z - c) * f z) \<le>
        norm_class.norm (f z)"
  proof (rule AE_I2)
    fix z
    have kernel_bound:
        "cmod (slp_damped_center_kernel eps tau (z - c)) \<le> 1"
      by (rule slp_damped_center_kernel_translate_norm_le_one[
            OF eps_nonnegative])
    show "norm_class.norm
        (slp_damped_center_kernel eps tau (z - c) * f z) \<le>
        norm_class.norm (f z)"
      unfolding norm_mult
      using mult_right_mono[
        OF kernel_bound norm_ge_zero[of "f z"]]
      by simp
  qed
qed

theorem slp_damped_center_average_tendsto:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
  shows "((\<lambda>eps :: real. slp_damped_center_average eps tau f c)
      \<longlongrightarrow> slp_center_average tau f c) (at_right 0)"
proof (rule tendsto_at_right_sequentially[where b = 1])
  show "(0 :: real) < 1"
    by simp
next
  fix S :: "nat \<Rightarrow> real"
  assume S_positive: "\<And>n. 0 < S n"
    and S_less_one: "\<And>n. S n < 1"
    and S_decreasing: "decseq S"
    and S_tendsto_zero: "S \<longlonglongrightarrow> 0"
  have S_at_right:
      "filterlim S (at_right (0 :: real)) sequentially"
  proof (rule tendsto_imp_filterlim_at_right)
    show "S \<longlonglongrightarrow> (0 :: real)"
      by (rule S_tendsto_zero)
    show "\<forall>\<^sub>F n in sequentially. S n > 0"
      using S_positive by simp
  qed
  have sequence_limit:
      "AE z in lborel.
        (\<lambda>n. slp_damped_center_kernel (S n) tau (z - c) * f z)
          \<longlonglongrightarrow> slp_center_kernel tau c z * f z"
  proof (rule AE_I2)
    fix z
    have kernel_limit:
        "(\<lambda>n. slp_damped_center_kernel (S n) tau (z - c))
          \<longlonglongrightarrow> slp_center_kernel tau c z"
      using slp_damped_center_kernel_translate_tendsto[of tau z c]
        S_at_right
      by (rule filterlim_compose)
    show "(\<lambda>n. slp_damped_center_kernel (S n) tau (z - c) * f z)
        \<longlonglongrightarrow> slp_center_kernel tau c z * f z"
      using kernel_limit by (intro tendsto_intros)
  qed
  have target_measurable:
      "(\<lambda>z. slp_center_kernel tau c z * f z) \<in>
        borel_measurable lborel"
    using slp_center_kernel_measurable[of tau c] f_integrable
    by measurable
  have sequence_measurable:
      "(\<lambda>z. slp_damped_center_kernel (S n) tau (z - c) * f z)
        \<in> borel_measurable lborel" for n
    using f_integrable by measurable
  have bound_integrable:
      "integrable lborel (\<lambda>z. norm_class.norm (f z))"
    using f_integrable by simp
  have sequence_bound:
      "\<And>n. AE z in lborel.
        norm_class.norm
          (slp_damped_center_kernel (S n) tau (z - c) * f z) \<le>
        norm_class.norm (f z)"
  proof -
    fix n
    show "AE z in lborel.
        norm_class.norm
          (slp_damped_center_kernel (S n) tau (z - c) * f z) \<le>
        norm_class.norm (f z)"
    proof (rule AE_I2)
      fix z
      have kernel_bound:
          "cmod (slp_damped_center_kernel (S n) tau (z - c)) \<le> 1"
        by (rule slp_damped_center_kernel_translate_norm_le_one)
          (use S_positive[of n] in simp)
      show "norm_class.norm
          (slp_damped_center_kernel (S n) tau (z - c) * f z) \<le>
          norm_class.norm (f z)"
        unfolding norm_mult
        using mult_right_mono[
          OF kernel_bound norm_ge_zero[of "f z"]]
        by simp
    qed
  qed
  have integral_limit:
      "(\<lambda>n. integral\<^sup>L lborel
          (\<lambda>z. slp_damped_center_kernel (S n) tau (z - c) * f z))
        \<longlonglongrightarrow>
        integral\<^sup>L lborel
          (\<lambda>z. slp_center_kernel tau c z * f z)"
    using Bochner_Integration.integral_dominated_convergence[
      OF target_measurable sequence_measurable bound_integrable
        sequence_limit sequence_bound] .
  have scaled_limit:
      "(\<lambda>n. of_real (tau / pi) *
          integral\<^sup>L lborel
            (\<lambda>z. slp_damped_center_kernel (S n) tau (z - c) * f z))
        \<longlonglongrightarrow>
        of_real (tau / pi) *
          integral\<^sup>L lborel
            (\<lambda>z. slp_center_kernel tau c z * f z)"
    by (rule tendsto_mult_left[OF integral_limit])
  show "(\<lambda>n. slp_damped_center_average (S n) tau f c)
      \<longlonglongrightarrow> slp_center_average tau f c"
    using scaled_limit
    by (simp only: slp_damped_center_average_def slp_center_average_def)
qed

end
