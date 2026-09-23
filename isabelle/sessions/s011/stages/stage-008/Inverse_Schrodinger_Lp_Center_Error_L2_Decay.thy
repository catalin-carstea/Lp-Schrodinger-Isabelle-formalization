theory Inverse_Schrodinger_Lp_Center_Error_L2_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Center_Average_L2"
begin

section \<open>Strong planar L2 decay of the physical center error\<close>

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_center_average_error_square_nn_integral_tendsto_zero:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
  shows "((\<lambda>tau. \<integral>\<^sup>+x.
      ennreal (Real_Vector_Spaces.norm
        (slp_center_average tau f x - f x)) ^ 2 \<partial>lborel)
    \<longlongrightarrow> 0) at_top"
proof -
  let ?F = "slp_fourier_transform f"
  let ?C = "(2 * pi) ^ 2"
  let ?frequency = "\<lambda>tau. integral\<^sup>L lborel
    (\<lambda>xi. cmod
      (((slp_center_fourier_multiplier tau xi - 1) * ?F xi) ^ 2))"
  let ?physical = "\<lambda>tau. \<integral>\<^sup>+x.
    ennreal (Real_Vector_Spaces.norm
      (slp_center_average tau f x - f x)) ^ 2 \<partial>lborel"
  have transform_l2: "aim_complex_lp_on_plane 2 ?F"
    by (rule slp_fourier_transform_l2_l1_l2[OF f_l2 f_integrable])
  have frequency_limit: "(?frequency \<longlongrightarrow> 0) at_top"
  proof -
    note raw =
      slp_center_fourier_multiplier_l2_error_tendsto_zero(2)[OF
        transform_l2]
    show ?thesis
      using raw
      by (simp only: powr_numeral norm_ge_zero norm_power)
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
  have divided_limit:
      "((\<lambda>tau. ?frequency tau / ?C) \<longlongrightarrow> 0) at_top"
  proof -
    have divided_raw:
        "((\<lambda>tau. ?frequency tau / ?C) \<longlongrightarrow> 0 / ?C)
          at_top"
      using frequency_limit C_nonzero by (intro tendsto_intros)
    show ?thesis
      using divided_raw by simp
  qed
  have upper_limit:
      "((\<lambda>tau. ennreal (?frequency tau / ?C)) \<longlongrightarrow> 0)
        at_top"
  proof -
    have embedded:
        "((\<lambda>tau. ennreal (?frequency tau / ?C))
          \<longlongrightarrow> ennreal 0) at_top"
      by (rule tendsto_ennrealI[OF divided_limit])
    show ?thesis
      using embedded by simp
  qed
  have physical_identity:
      "?physical tau = (\<integral>\<^sup>+x. ennreal (cmod
        ((slp_center_average tau f x - f x) ^ 2)) \<partial>lborel)" for tau
  proof (rule nn_integral_cong)
    fix x :: slp_point
    show "ennreal (cmod (slp_center_average tau f x - f x)) ^ 2 =
        ennreal (cmod ((slp_center_average tau f x - f x) ^ 2))"
      apply (subst ennreal_power[OF norm_ge_zero])
      apply (simp only: norm_power)
      done
  qed
  have tau_positive:
      "eventually (\<lambda>tau :: real. 0 < tau) at_top"
    by simp
  have physical_bound:
      "eventually
        (\<lambda>tau. ?physical tau \<le> ennreal (?frequency tau / ?C))
        at_top"
    using tau_positive
  proof eventually_elim
    fix tau :: real
    assume tau: "0 < tau"
    note raw = slp_center_average_error_nn_integral_le_fourier[OF
      tau f_integrable f_l2]
    show "?physical tau \<le> ennreal (?frequency tau / ?C)"
      using raw by (simp only: physical_identity)
  qed
  show ?thesis
    by (rule tendsto_sandwich[
          where f="\<lambda>_. 0" and
            h="\<lambda>tau. ennreal (?frequency tau / ?C)"])
      (use physical_bound upper_limit in auto)
qed

end

end
