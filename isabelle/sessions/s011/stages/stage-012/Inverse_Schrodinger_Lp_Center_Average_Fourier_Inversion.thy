theory Inverse_Schrodinger_Lp_Center_Average_Fourier_Inversion
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Fourier_Pointwise_Inversion"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The physical center average as a Fourier multiplier\<close>

context hormander_euclidean_l2_fourier_plancherel
begin

lemma slp_damped_center_average_fourier_integrable:
  fixes f :: slp_scalar_field
  assumes eps_positive: "0 < eps" and tau_positive: "0 < tau"
    and f_integrable: "integrable lborel f"
    and fourier_integrable: "integrable lborel (slp_fourier_transform f)"
  shows "integrable lborel (slp_fourier_transform (slp_damped_center_average eps tau f))"
proof -
  let ?m = "\<lambda>xi. of_real (tau / pi) *
    slp_fourier_transform (slp_damped_center_kernel eps tau) xi"
  have kernel_integrable: "integrable lborel (slp_damped_center_kernel eps tau)"
    by (rule slp_damped_center_kernel_integrable[OF eps_positive])
  have kernel_measurable: "slp_damped_center_kernel eps tau \<in> borel_measurable lborel"
    using kernel_integrable by measurable
  have multiplier_measurable: "?m \<in> borel_measurable lborel"
    using slp_fourier_transform_measurable[OF kernel_measurable] by measurable
  have F_measurable: "slp_fourier_transform f \<in> borel_measurable lborel"
    using fourier_integrable by measurable
  have product_integrable:
      "integrable lborel (\<lambda>xi. ?m xi * slp_fourier_transform f xi)"
  proof (rule Bochner_Integration.integrable_bound[OF fourier_integrable])
    show "(\<lambda>xi. ?m xi * slp_fourier_transform f xi) \<in> borel_measurable lborel"
      using multiplier_measurable F_measurable by measurable
    show "AE xi in lborel. norm (?m xi * slp_fourier_transform f xi)
        \<le> norm (slp_fourier_transform f xi)"
    proof (rule AE_I2)
      fix xi
      have bound: "norm (?m xi) \<le> 1"
        by (rule slp_damped_center_fourier_multiplier_norm_le_one[OF
            eps_positive tau_positive])
      show "norm (?m xi * slp_fourier_transform f xi)
          \<le> norm (slp_fourier_transform f xi)"
        using mult_right_mono[OF bound norm_ge_zero[of "slp_fourier_transform f xi"]]
        by (simp only: norm_mult mult_1_left)
    qed
  qed
  have identity:
      "slp_fourier_transform (slp_damped_center_average eps tau f) =
        (\<lambda>xi. ?m xi * slp_fourier_transform f xi)"
    by (rule ext) (rule slp_damped_center_average_fourier_transform[OF
        eps_positive f_integrable])
  show ?thesis using product_integrable by (simp only: identity)
qed

lemma slp_center_fourier_product_integrable:
  fixes g :: slp_scalar_field
  assumes g_integrable: "integrable lborel g"
  shows "integrable lborel (\<lambda>xi. slp_center_fourier_multiplier tau xi * g xi)"
proof (rule Bochner_Integration.integrable_bound[OF g_integrable])
  show "(\<lambda>xi. slp_center_fourier_multiplier tau xi * g xi) \<in> borel_measurable lborel"
    using g_integrable slp_center_fourier_multiplier_measurable[of tau] by measurable
  show "AE xi in lborel. norm (slp_center_fourier_multiplier tau xi * g xi) \<le> norm (g xi)"
    by (simp add: norm_mult)
qed

lemma slp_damped_multiplier_fourier_tendsto:
  fixes g :: slp_scalar_field
  assumes tau_positive: "0 < tau" and g_integrable: "integrable lborel g"
  shows "((\<lambda>eps. slp_fourier_transform
      (\<lambda>xi. (of_real (tau / pi) *
        slp_fourier_transform (slp_damped_center_kernel eps tau) xi) * g xi) x)
    \<longlongrightarrow> slp_fourier_transform
      (\<lambda>xi. slp_center_fourier_multiplier tau xi * g xi) x) (at_right 0)"
proof (rule tendsto_at_right_sequentially[where b=1])
  show "(0::real) < 1" by simp
next
  fix S :: "nat \<Rightarrow> real"
  assume S_positive: "\<And>n. 0 < S n" and S_less_one: "\<And>n. S n < 1"
    and S_decreasing: "decseq S" and S_limit: "S \<longlonglongrightarrow> 0"
  let ?m = "\<lambda>eps xi. of_real (tau / pi) *
    slp_fourier_transform (slp_damped_center_kernel eps tau) xi"
  have S_filter: "filterlim S (at_right (0::real)) sequentially"
    by (rule tendsto_imp_filterlim_at_right[OF S_limit]) (use S_positive in simp)
  have g_measurable: "g \<in> borel_measurable lborel"
    using g_integrable by measurable
  have target_measurable:
      "(\<lambda>xi. slp_fourier_phase x xi *
        (slp_center_fourier_multiplier tau xi * g xi)) \<in> borel_measurable lborel"
    using g_measurable slp_fourier_phase_measurable[of x]
      slp_center_fourier_multiplier_measurable[of tau] by measurable
  have sequence_measurable:
      "(\<lambda>xi. slp_fourier_phase x xi * (?m (S n) xi * g xi))
        \<in> borel_measurable lborel" for n
  proof -
    have kernel_integrable: "integrable lborel (slp_damped_center_kernel (S n) tau)"
      by (rule slp_damped_center_kernel_integrable[OF S_positive])
    have kernel_measurable:
        "slp_damped_center_kernel (S n) tau \<in> borel_measurable lborel"
      using kernel_integrable by measurable
    show ?thesis using slp_fourier_transform_measurable[OF kernel_measurable]
      g_measurable slp_fourier_phase_measurable[of x] by measurable
  qed
  have bound_integrable: "integrable lborel (\<lambda>xi. norm (g xi))"
    using g_integrable by simp
  have pointwise:
      "AE xi in lborel. (\<lambda>n. slp_fourier_phase x xi * (?m (S n) xi * g xi))
        \<longlonglongrightarrow> slp_fourier_phase x xi *
          (slp_center_fourier_multiplier tau xi * g xi)"
  proof (rule AE_I2)
    fix xi
    have multiplier_limit: "(\<lambda>n. ?m (S n) xi)
        \<longlonglongrightarrow> slp_center_fourier_multiplier tau xi"
      using slp_damped_center_fourier_multiplier_tendsto[OF tau_positive, of xi]
        S_filter by (rule filterlim_compose)
    show "(\<lambda>n. slp_fourier_phase x xi * (?m (S n) xi * g xi))
        \<longlonglongrightarrow> slp_fourier_phase x xi *
          (slp_center_fourier_multiplier tau xi * g xi)"
      using multiplier_limit by (intro tendsto_intros)
  qed
  have bound:
      "AE xi in lborel. norm (slp_fourier_phase x xi * (?m (S n) xi * g xi))
        \<le> norm (g xi)" for n
  proof (rule AE_I2)
    fix xi
    have multiplier_bound: "norm (?m (S n) xi) \<le> 1"
      by (rule slp_damped_center_fourier_multiplier_norm_le_one[OF S_positive tau_positive])
    show "norm (slp_fourier_phase x xi * (?m (S n) xi * g xi)) \<le> norm (g xi)"
      using mult_right_mono[OF multiplier_bound norm_ge_zero[of "g xi"]]
      by (simp only: norm_mult slp_fourier_phase_norm mult_1_left)
  qed
  have integral_limit:
      "(\<lambda>n. integral\<^sup>L lborel
        (\<lambda>xi. slp_fourier_phase x xi * (?m (S n) xi * g xi)))
      \<longlonglongrightarrow> integral\<^sup>L lborel
        (\<lambda>xi. slp_fourier_phase x xi *
          (slp_center_fourier_multiplier tau xi * g xi))"
    by (rule integral_dominated_convergence[OF target_measurable
        sequence_measurable bound_integrable pointwise bound])
  show "(\<lambda>n. slp_fourier_transform (\<lambda>xi. ?m (S n) xi * g xi) x)
      \<longlonglongrightarrow> slp_fourier_transform
        (\<lambda>xi. slp_center_fourier_multiplier tau xi * g xi) x"
    using integral_limit by (simp only: slp_fourier_transform_def)
qed

theorem slp_center_average_fourier_inversion:
  fixes f :: slp_scalar_field
  assumes tau_positive: "0 < tau" and f_integrable: "integrable lborel f"
    and fourier_integrable: "integrable lborel (slp_fourier_transform f)"
  shows "slp_fourier_transform
      (\<lambda>xi. slp_center_fourier_multiplier tau xi * slp_fourier_transform f xi) x =
    of_real ((2 * pi) ^ 2) * slp_center_average tau f (-x)"
proof -
  let ?S = "\<lambda>n. inverse (real (Suc n))"
  let ?F = "slp_fourier_transform f"
  let ?C = "of_real ((2 * pi) ^ 2) :: complex"
  let ?m = "\<lambda>eps xi. of_real (tau / pi) *
    slp_fourier_transform (slp_damped_center_kernel eps tau) xi"
  let ?G = "slp_fourier_transform (\<lambda>xi. slp_center_fourier_multiplier tau xi * ?F xi)"
  have S_positive: "0 < ?S n" for n by simp
  have S_limit: "?S \<longlonglongrightarrow> 0" by (rule LIMSEQ_inverse_real_of_nat)
  have S_filter: "filterlim ?S (at_right (0::real)) sequentially"
    by (rule tendsto_imp_filterlim_at_right[OF S_limit]) simp
  have almost_each:
      "AE x in lborel. slp_fourier_transform (\<lambda>xi. ?m (?S n) xi * ?F xi) x =
        ?C * slp_damped_center_average (?S n) tau f (-x)" for n
  proof -
    have average_integrable: "integrable lborel (slp_damped_center_average (?S n) tau f)"
      by (rule slp_damped_center_average_integrable[OF S_positive f_integrable])
    have average_l2: "aim_complex_lp_on_plane 2 (slp_damped_center_average (?S n) tau f)"
      by (rule slp_damped_center_average_l2[OF S_positive f_integrable])
    have transform_integrable:
        "integrable lborel (slp_fourier_transform (slp_damped_center_average (?S n) tau f))"
      by (rule slp_damped_center_average_fourier_integrable[OF
          S_positive tau_positive f_integrable fourier_integrable])
    have identity:
        "slp_fourier_transform (slp_damped_center_average (?S n) tau f) =
          (\<lambda>xi. ?m (?S n) xi * ?F xi)"
      by (rule ext) (rule slp_damped_center_average_fourier_transform[OF
          S_positive f_integrable])
    show ?thesis
      using slp_fourier_l1_double_transform_ae[OF
        average_integrable average_l2 transform_integrable]
      by (simp only: identity)
  qed
  have almost_all:
      "AE x in lborel. \<forall>n. slp_fourier_transform (\<lambda>xi. ?m (?S n) xi * ?F xi) x =
        ?C * slp_damped_center_average (?S n) tau f (-x)"
    by (simp only: AE_all_countable; intro allI; rule almost_each)
  have almost_limit:
      "AE x in lborel. ?G x = ?C * slp_center_average tau f (-x)"
  proof (use almost_all in eventually_elim)
    fix x
    assume all: "\<forall>n. slp_fourier_transform (\<lambda>xi. ?m (?S n) xi * ?F xi) x =
      ?C * slp_damped_center_average (?S n) tau f (-x)"
    have frequency_limit:
        "(\<lambda>n. slp_fourier_transform (\<lambda>xi. ?m (?S n) xi * ?F xi) x)
          \<longlonglongrightarrow> ?G x"
      using slp_damped_multiplier_fourier_tendsto[OF tau_positive fourier_integrable, of x]
        S_filter by (rule filterlim_compose)
    have average_limit:
        "(\<lambda>n. slp_damped_center_average (?S n) tau f (-x))
          \<longlonglongrightarrow> slp_center_average tau f (-x)"
      using slp_damped_center_average_tendsto[OF f_integrable, of tau "-x"]
        S_filter by (rule filterlim_compose)
    have scaled_limit:
        "(\<lambda>n. ?C * slp_damped_center_average (?S n) tau f (-x))
          \<longlonglongrightarrow> ?C * slp_center_average tau f (-x)"
      using average_limit by (intro tendsto_intros)
    have identity:
        "(\<lambda>n. slp_fourier_transform (\<lambda>xi. ?m (?S n) xi * ?F xi) x) =
          (\<lambda>n. ?C * slp_damped_center_average (?S n) tau f (-x))"
      by (rule ext) (use all in blast)
    have second_limit:
        "(\<lambda>n. slp_fourier_transform (\<lambda>xi. ?m (?S n) xi * ?F xi) x)
          \<longlonglongrightarrow> ?C * slp_center_average tau f (-x)"
      by (simp only: identity scaled_limit)
    show "?G x = ?C * slp_center_average tau f (-x)"
      by (rule tendsto_unique[OF sequentially_bot frequency_limit second_limit])
  qed
  have product_integrable:
      "integrable lborel (\<lambda>xi. slp_center_fourier_multiplier tau xi * ?F xi)"
    by (rule slp_center_fourier_product_integrable[OF fourier_integrable])
  have left_continuous: "continuous_on UNIV ?G"
    by (rule slp_fourier_transform_continuous[OF product_integrable])
  have average_continuous: "continuous_on UNIV (slp_center_average tau f)"
    by (rule slp_center_average_continuous[OF f_integrable])
  have reflected_continuous: "continuous_on UNIV (\<lambda>x. slp_center_average tau f (-x))"
    by (rule continuous_on_compose2[OF average_continuous])
      (auto intro!: continuous_intros)
  have right_continuous: "continuous_on UNIV (\<lambda>x. ?C * slp_center_average tau f (-x))"
    using reflected_continuous by (intro continuous_intros)
  show ?thesis
    by (rule slp_continuous_ae_eq[OF left_continuous right_continuous almost_limit])
qed

end

end
