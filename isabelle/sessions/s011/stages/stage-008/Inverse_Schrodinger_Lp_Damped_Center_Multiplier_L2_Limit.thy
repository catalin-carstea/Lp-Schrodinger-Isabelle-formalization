theory Inverse_Schrodinger_Lp_Damped_Center_Multiplier_L2_Limit
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Damped_Center_Error_Plancherel"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Damped_Center_Multiplier_Limit"
begin

section \<open>Removal of damping in the planar Fourier error mass\<close>

context hormander_euclidean_l2_fourier_plancherel
begin

lemma slp_fourier_transform_l2_l1_l2:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_l2: "aim_complex_lp_on_plane 2 f"
    and f_integrable: "integrable lborel f"
  shows "aim_complex_lp_on_plane 2 (slp_fourier_transform f)"
proof -
  have selected_l2:
      "aim_complex_lp_on_plane 2 (slp_fourier_l2_transform f)"
    by (rule slp_fourier_l2_transform_l2[OF f_l2])
  have selected_square_integrable:
      "integrable lborel
        (\<lambda>xi. cmod (slp_fourier_l2_transform f xi) powr 2)"
    using selected_l2 unfolding aim_complex_lp_on_plane_def by blast
  have transform_measurable:
      "slp_fourier_transform f \<in> borel_measurable lborel"
    by (rule slp_fourier_transform_measurable)
      (use f_integrable in measurable)
  have transform_square_measurable:
      "(\<lambda>xi. cmod (slp_fourier_transform f xi) powr 2) \<in>
        borel_measurable lborel"
    using transform_measurable by measurable
  have selected_ae:
      "AE xi in lborel.
        slp_fourier_l2_transform f xi = slp_fourier_transform f xi"
    by (rule slp_fourier_l2_transform_ae_eq_l1[OF
          f_l2 f_integrable])
  have square_ae:
      "AE xi in lborel.
        cmod (slp_fourier_l2_transform f xi) powr 2 =
          cmod (slp_fourier_transform f xi) powr 2"
    using selected_ae by eventually_elim simp
  have transform_square_integrable:
      "integrable lborel
        (\<lambda>xi. cmod (slp_fourier_transform f xi) powr 2)"
    by (rule integrable_cong_AE_imp[OF
          selected_square_integrable transform_square_measurable square_ae])
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using transform_measurable transform_square_integrable by blast
qed

lemma slp_damped_center_fourier_multiplier_norm_le_one:
  assumes eps: "0 < eps"
    and tau: "0 < tau"
  shows "cmod (of_real (tau / pi) *
      slp_fourier_transform
        (slp_damped_center_kernel eps tau) xi) \<le> 1"
proof -
  let ?D = "eps ^ 2 + tau ^ 2"
  let ?Q = "(xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2"
  let ?E = "- eps * ?Q / (4 * ?D)"
  have eps_square_pos: "0 < eps ^ 2"
    using eps by simp
  have tau_square_nonneg: "0 \<le> tau ^ 2"
    by simp
  have D_pos: "0 < ?D"
    by (rule add_pos_nonneg[OF eps_square_pos tau_square_nonneg])
  have root_pos: "0 < sqrt ?D"
    by (rule real_sqrt_gt_zero[OF D_pos])
  have tau_le_root: "tau \<le> sqrt ?D"
    by (rule real_le_rsqrt) simp
  have Q_nonneg: "0 \<le> ?Q"
    by simp
  have numerator_nonpos: "- eps * ?Q \<le> 0"
    using eps Q_nonneg by (intro mult_nonpos_nonneg) simp
  have denominator_pos: "0 < 4 * ?D"
    using D_pos by simp
  have E_nonpos: "?E \<le> 0"
    by (rule divide_nonpos_pos[OF numerator_nonpos denominator_pos])
  have exp_le_one: "exp ?E \<le> 1"
    using E_nonpos by (simp only: exp_le_one_iff)
  have tau_pi_pos: "0 < tau / pi"
    using tau by simp
  have coefficient_pos: "0 < pi * exp ?E / sqrt ?D"
    using root_pos by simp
  have coefficient_regroup:
      "(tau / pi) * (pi * exp ?E / sqrt ?D) =
        tau * exp ?E / sqrt ?D"
    by simp
  have norm_eq:
      "cmod (of_real (tau / pi) *
          slp_fourier_transform
            (slp_damped_center_kernel eps tau) xi) =
        tau * exp ?E / sqrt ?D"
    using eps tau D_pos root_pos
    by (simp only:
        slp_damped_center_fourier_transform_closed[OF eps]
        norm_mult norm_of_real norm_exp_i_times
        abs_of_pos[OF tau_pi_pos] abs_of_pos[OF coefficient_pos]
        mult_1_right coefficient_regroup)
  have "tau * exp ?E / sqrt ?D \<le> tau / sqrt ?D"
    using tau exp_le_one root_pos
    by (intro divide_right_mono mult_left_mono) simp_all
  also have "... \<le> 1"
    using tau_le_root root_pos
    by (simp only: pos_divide_le_eq mult_1_left)
  finally show ?thesis
    using norm_eq by simp
qed

theorem slp_damped_center_multiplier_l2_error_tendsto:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes tau: "0 < tau"
    and f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
  shows "((\<lambda>eps :: real. integral\<^sup>L lborel
      (\<lambda>xi. cmod
        (((of_real (tau / pi) *
              slp_fourier_transform
                (slp_damped_center_kernel eps tau) xi) - 1) *
            slp_fourier_transform f xi) ^ 2)) \<longlongrightarrow>
    integral\<^sup>L lborel
      (\<lambda>xi. cmod
        (((slp_center_fourier_multiplier tau xi - 1) *
            slp_fourier_transform f xi) ^ 2))) (at_right 0)"
proof -
  have sequential_condition:
      "\<And>S :: nat \<Rightarrow> real.
        (\<And>n. 0 < S n) \<Longrightarrow>
        (\<And>n. S n < 1) \<Longrightarrow>
        decseq S \<Longrightarrow>
        S \<longlonglongrightarrow> 0 \<Longrightarrow>
        (\<lambda>n. integral\<^sup>L lborel
          (\<lambda>xi. cmod
            ((of_real (tau / pi) *
                  slp_fourier_transform
                    (slp_damped_center_kernel (S n) tau) xi - 1) *
                slp_fourier_transform f xi) ^ 2)) \<longlonglongrightarrow>
          integral\<^sup>L lborel
            (\<lambda>xi. cmod
              (((slp_center_fourier_multiplier tau xi - 1) *
                  slp_fourier_transform f xi) ^ 2))"
  proof -
    fix S :: "nat \<Rightarrow> real"
    assume S_positive: "\<And>n. 0 < S n"
      and S_less_one: "\<And>n. S n < 1"
      and S_decreasing: "decseq S"
      and S_tendsto_zero: "S \<longlonglongrightarrow> 0"
  let ?F = "slp_fourier_transform f"
  let ?m = "\<lambda>eps xi.
    of_real (tau / pi) *
      slp_fourier_transform (slp_damped_center_kernel eps tau) xi"
  let ?u = "\<lambda>n xi. cmod (((?m (S n) xi - 1) * ?F xi) ^ 2)"
  let ?v = "\<lambda>xi. cmod
    (((slp_center_fourier_multiplier tau xi - 1) * ?F xi) ^ 2)"
  let ?w = "\<lambda>xi. 4 * cmod (?F xi) ^ 2"
  have S_at_right:
      "filterlim S (at_right (0 :: real)) sequentially"
  proof (rule tendsto_imp_filterlim_at_right)
    show "S \<longlonglongrightarrow> (0 :: real)"
      by (rule S_tendsto_zero)
    show "\<forall>\<^sub>F n in sequentially. S n > 0"
      using S_positive by simp
  qed
  have F_l2: "aim_complex_lp_on_plane 2 ?F"
    by (rule slp_fourier_transform_l2_l1_l2[OF
          f_l2 f_integrable])
  have F_measurable: "?F \<in> borel_measurable lborel"
    using F_l2 unfolding aim_complex_lp_on_plane_def by blast
  have F_square_integrable:
      "integrable lborel (\<lambda>xi. cmod (?F xi) ^ 2)"
    using F_l2 unfolding aim_complex_lp_on_plane_def
    by (simp only: powr_numeral norm_ge_zero)
  have target_measurable: "?v \<in> borel_measurable lborel"
    using slp_center_fourier_multiplier_measurable[of tau] F_measurable
    by measurable
  have sequence_measurable: "?u n \<in> borel_measurable lborel" for n
  proof -
    have kernel_measurable:
        "slp_damped_center_kernel (S n) tau \<in>
          borel_measurable lborel"
      by (rule slp_damped_center_kernel_measurable)
    have kernel_transform_measurable:
        "slp_fourier_transform (slp_damped_center_kernel (S n) tau) \<in>
          borel_measurable lborel"
      by (rule slp_fourier_transform_measurable[OF kernel_measurable])
    show ?thesis
      using kernel_transform_measurable F_measurable by measurable
  qed
  have majorant_integrable: "integrable lborel ?w"
    using F_square_integrable by simp
  have sequence_limit: "AE xi in lborel. (\<lambda>n. ?u n xi) \<longlonglongrightarrow> ?v xi"
  proof (rule AE_I2)
    fix xi
    have multiplier_limit:
        "(\<lambda>n. ?m (S n) xi) \<longlonglongrightarrow>
          slp_center_fourier_multiplier tau xi"
      using slp_damped_center_fourier_multiplier_tendsto[OF tau, of xi]
        S_at_right
      by (rule filterlim_compose)
    have square_limit:
        "(\<lambda>n. (((?m (S n) xi - 1) * ?F xi) ^ 2)) \<longlonglongrightarrow>
          (((slp_center_fourier_multiplier tau xi - 1) * ?F xi) ^ 2)"
      using multiplier_limit by (intro tendsto_intros)
    show "(\<lambda>n. ?u n xi) \<longlonglongrightarrow> ?v xi"
      by (rule tendsto_norm[OF square_limit])
  qed
  have sequence_bound: "\<And>n. AE xi in lborel.
      Real_Vector_Spaces.norm (?u n xi) \<le> ?w xi"
  proof -
    fix n
    show "AE xi in lborel.
        Real_Vector_Spaces.norm (?u n xi) \<le> ?w xi"
    proof (rule AE_I2)
      fix xi
      have multiplier_bound: "cmod (?m (S n) xi) \<le> 1"
        by (rule slp_damped_center_fourier_multiplier_norm_le_one[OF
              S_positive tau])
      have difference_bound: "cmod (?m (S n) xi - 1) \<le> 2"
      proof -
        have "cmod (?m (S n) xi - 1) \<le>
            cmod (?m (S n) xi) + cmod (1 :: complex)"
          by (rule norm_triangle_ineq4)
        also have "... \<le> 2"
          using multiplier_bound by simp
        finally show ?thesis .
      qed
      have product_bound:
          "cmod ((?m (S n) xi - 1) * ?F xi) \<le>
            2 * cmod (?F xi)"
        unfolding norm_mult
        by (rule mult_right_mono[OF difference_bound]) simp
      have square_bound:
          "cmod ((?m (S n) xi - 1) * ?F xi) ^ 2 \<le>
            (2 * cmod (?F xi)) ^ 2"
        by (rule power_mono[OF product_bound]) simp
      have integrand_norm:
          "Real_Vector_Spaces.norm (?u n xi) =
            cmod ((?m (S n) xi - 1) * ?F xi) ^ 2"
        by (simp only: real_norm_def norm_power
            abs_of_nonneg[OF zero_le_power2])
      have majorant_form:
          "(2 * cmod (?F xi)) ^ 2 = ?w xi"
        by (simp only: power_mult_distrib) simp
      show "Real_Vector_Spaces.norm (?u n xi) \<le> ?w xi"
        using square_bound
        by (simp only: integrand_norm majorant_form)
    qed
  qed
  have dct_result:
      "(\<lambda>n. integral\<^sup>L lborel (?u n)) \<longlonglongrightarrow>
        integral\<^sup>L lborel ?v"
    using Bochner_Integration.integral_dominated_convergence[
      where M=lborel and f="?v" and s="?u" and w="?w",
      OF target_measurable sequence_measurable majorant_integrable
        sequence_limit sequence_bound]
    by simp
    have sequence_integral_form:
        "integral\<^sup>L lborel (?u n) =
          integral\<^sup>L lborel
            (\<lambda>xi. cmod
              ((of_real (tau / pi) *
                    slp_fourier_transform
                      (slp_damped_center_kernel (S n) tau) xi - 1) *
                  slp_fourier_transform f xi) ^ 2)" for n
      by (intro Bochner_Integration.integral_cong[OF refl])
        (simp only: norm_power)
    have normalized_result:
        "(\<lambda>n. integral\<^sup>L lborel
            (\<lambda>xi. cmod
              ((of_real (tau / pi) *
                    slp_fourier_transform
                      (slp_damped_center_kernel (S n) tau) xi - 1) *
                  slp_fourier_transform f xi) ^ 2)) \<longlonglongrightarrow>
          integral\<^sup>L lborel ?v"
      using dct_result by (simp only: sequence_integral_form)
    show "(\<lambda>n. integral\<^sup>L lborel
        (\<lambda>xi. cmod
          ((of_real (tau / pi) *
                slp_fourier_transform
                  (slp_damped_center_kernel (S n) tau) xi - 1) *
              slp_fourier_transform f xi) ^ 2)) \<longlonglongrightarrow>
        integral\<^sup>L lborel
          (\<lambda>xi. cmod
            (((slp_center_fourier_multiplier tau xi - 1) *
                slp_fourier_transform f xi) ^ 2))"
      by (rule normalized_result)
  qed
  show ?thesis
    by (rule tendsto_at_right_sequentially[
          where b="(1 :: real)", OF _ sequential_condition]) simp
qed

end

end
