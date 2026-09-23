theory Inverse_Schrodinger_Lp_Center_Error_Fourier_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Center_Error_Fatou"
begin

section \<open>Fourier control of the undamped physical center error\<close>

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_center_average_error_nn_integral_le_fourier:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes tau: "0 < tau"
    and f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
  shows "(\<integral>\<^sup>+c. ennreal (cmod
      ((slp_center_average tau f c - f c) ^ 2)) \<partial>lborel) \<le>
    ennreal ((integral\<^sup>L lborel
      (\<lambda>xi. cmod (((slp_center_fourier_multiplier tau xi - 1) *
        slp_fourier_transform f xi) ^ 2))) / (2 * pi) ^ 2)"
proof -
  let ?S = "\<lambda>n. inverse (real (Suc n))"
  let ?C = "(2 * pi) ^ 2"
  let ?frequency = "\<lambda>eps. integral\<^sup>L lborel
    (\<lambda>xi. cmod
      (((of_real (tau / pi) *
          slp_fourier_transform
            (slp_damped_center_kernel eps tau) xi - 1) *
        slp_fourier_transform f xi) ^ 2))"
  let ?frequency_zero = "integral\<^sup>L lborel
    (\<lambda>xi. cmod
      (((slp_center_fourier_multiplier tau xi - 1) *
        slp_fourier_transform f xi) ^ 2))"
  let ?physical = "\<lambda>eps. integral\<^sup>L lborel
    (\<lambda>c. cmod
      ((slp_damped_center_average eps tau f c - f c) ^ 2))"
  let ?physical_nn = "\<lambda>eps. \<integral>\<^sup>+c. ennreal (cmod
      ((slp_damped_center_average eps tau f c - f c) ^ 2))
        \<partial>lborel"
  have S_positive: "0 < ?S n" for n
    by simp
  have S_tendsto_zero: "?S \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_inverse_real_of_nat)
  have S_at_right:
      "filterlim ?S (at_right (0 :: real)) sequentially"
  proof (rule tendsto_imp_filterlim_at_right)
    show "?S \<longlonglongrightarrow> (0 :: real)"
      by (rule S_tendsto_zero)
    show "\<forall>\<^sub>F n in sequentially. ?S n > 0"
      using S_positive by simp
  qed
  have fatou_bound:
      "(\<integral>\<^sup>+c. ennreal (cmod
          ((slp_center_average tau f c - f c) ^ 2)) \<partial>lborel) \<le>
        liminf (\<lambda>n. ?physical_nn (?S n))"
    by (rule slp_center_average_error_nn_integral_le_liminf[OF
          S_positive S_tendsto_zero f_integrable])
  have damped_average_l2:
      "aim_complex_lp_on_plane 2
        (slp_damped_center_average (?S n) tau f)" for n
    by (rule slp_damped_center_average_l2[OF
          S_positive f_integrable])
  have damped_error_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>c. slp_damped_center_average (?S n) tau f c - f c)" for n
    by (rule aim_complex_lp_on_plane_diff[OF
          zero_less_numeral damped_average_l2 f_l2])
  have physical_integrable:
      "integrable lborel
        (\<lambda>c. cmod
          ((slp_damped_center_average (?S n) tau f c - f c) ^ 2))"
      for n
  proof -
    have "integrable lborel
        (\<lambda>c. cmod
          (slp_damped_center_average (?S n) tau f c - f c) powr 2)"
      using damped_error_l2[of n]
      unfolding aim_complex_lp_on_plane_def by blast
    then show ?thesis
      by (simp only: norm_power powr_numeral norm_ge_zero)
  qed
  have physical_nn_eq:
      "?physical_nn (?S n) = ennreal (?physical (?S n))" for n
    by (rule nn_integral_eq_integral[OF physical_integrable]) simp
  have damped_plancherel:
      "?frequency (?S n) = ?C * ?physical (?S n)" for n
  proof -
    have raw:
        "integral\<^sup>L lborel
            (\<lambda>xi. cmod
              ((of_real (tau / pi) *
                    slp_fourier_transform
                      (slp_damped_center_kernel (?S n) tau) xi - 1) *
                  slp_fourier_transform f xi) ^ 2) =
          ?C * integral\<^sup>L lborel
            (\<lambda>c. cmod
              (slp_damped_center_average (?S n) tau f c - f c) ^ 2)"
    proof (rule slp_damped_center_error_plancherel[
        where eps="?S n" and tau=tau and f=f])
      show "0 < ?S n"
        by (rule S_positive)
      show "integrable lborel f"
        by (rule f_integrable)
      show "aim_complex_lp_on_plane 2 f"
        by (rule f_l2)
    qed
    show ?thesis
      using raw by (simp only: norm_power)
  qed
  have C_positive: "0 < ?C"
  proof -
    have base_positive: "0 < 2 * pi"
      by (rule mult_pos_pos) (simp_all add: pi_gt_zero)
    show ?thesis
      unfolding power2_eq_square
      by (rule mult_pos_pos[OF base_positive base_positive])
  qed
  have C_nonzero: "?C \<noteq> 0"
    using C_positive by simp
  have physical_eq:
      "?physical (?S n) = ?frequency (?S n) / ?C" for n
  proof -
    have "?physical (?S n) =
        (?C * ?physical (?S n)) / ?C"
      using C_nonzero by simp
    also have "... = ?frequency (?S n) / ?C"
      using damped_plancherel[of n] by simp
    finally show ?thesis .
  qed
  note frequency_raw =
    slp_damped_center_multiplier_l2_error_tendsto[
      where tau=tau and f=f, OF tau f_integrable f_l2]
  have frequency_at_right:
      "(?frequency \<longlongrightarrow> ?frequency_zero) (at_right 0)"
    using frequency_raw by (simp only: norm_power)
  have frequency_sequence_limit:
      "(\<lambda>n. ?frequency (?S n)) \<longlonglongrightarrow>
        ?frequency_zero"
    using frequency_at_right S_at_right
    by (rule filterlim_compose)
  have divided_limit:
      "(\<lambda>n. ?frequency (?S n) / ?C) \<longlonglongrightarrow>
        ?frequency_zero / ?C"
    using frequency_sequence_limit C_nonzero by (intro tendsto_intros)
  have physical_limit:
      "(\<lambda>n. ?physical (?S n)) \<longlonglongrightarrow>
        ?frequency_zero / ?C"
    using divided_limit by (simp only: physical_eq)
  have embedded_limit:
      "(\<lambda>n. ennreal (?physical (?S n))) \<longlonglongrightarrow>
        ennreal (?frequency_zero / ?C)"
    by (rule tendsto_ennrealI[OF physical_limit])
  have physical_nn_limit:
      "(\<lambda>n. ?physical_nn (?S n)) \<longlonglongrightarrow>
        ennreal (?frequency_zero / ?C)"
    using embedded_limit by (simp only: physical_nn_eq)
  have liminf_identity:
      "liminf (\<lambda>n. ?physical_nn (?S n)) =
        ennreal (?frequency_zero / ?C)"
    by (rule lim_imp_Liminf[OF
          trivial_limit_sequentially physical_nn_limit])
  show ?thesis
    using fatou_bound by (simp only: liminf_identity)
qed

end

end
