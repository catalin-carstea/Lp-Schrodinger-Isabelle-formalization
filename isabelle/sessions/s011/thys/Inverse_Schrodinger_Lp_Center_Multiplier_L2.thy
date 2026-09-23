theory Inverse_Schrodinger_Lp_Center_Multiplier_L2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_L2_Error_Decay"
begin

section \<open>The exact quadratic center multiplier on complex \(L^2\)\<close>

definition slp_center_fourier_multiplier ::
  "real \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_center_fourier_multiplier tau xi =
    exp (\<i> * of_real (- (slp_center_phase 0 xi / (4 * tau))))"

lemma slp_center_fourier_multiplier_measurable:
  "slp_center_fourier_multiplier tau \<in> borel_measurable lborel"
  unfolding slp_center_fourier_multiplier_def
  using slp_center_phase_measurable[of 0]
  by measurable

lemma slp_center_fourier_multiplier_norm [simp]:
  "cmod (slp_center_fourier_multiplier tau xi) = 1"
  unfolding slp_center_fourier_multiplier_def
  by (simp only: norm_exp_i_times)

lemma slp_center_fourier_multiplier_tendsto_one:
  "((\<lambda>tau. slp_center_fourier_multiplier tau xi) \<longlongrightarrow> 1) at_top"
proof -
  have inverse_limit:
      "((\<lambda>tau :: real. inverse tau) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_inverse_0_at_top) (rule filterlim_ident)
  have scalar_limit:
      "((\<lambda>tau :: real. - (slp_center_phase 0 xi / (4 * tau)))
        \<longlongrightarrow> 0) at_top"
  proof -
    have product_limit:
        "((\<lambda>tau. (- slp_center_phase 0 xi / 4) * inverse tau)
          \<longlongrightarrow> (- slp_center_phase 0 xi / 4) * 0) at_top"
      by (rule tendsto_mult[OF tendsto_const inverse_limit])
    have product_zero:
        "((\<lambda>tau. (- slp_center_phase 0 xi / 4) * inverse tau)
          \<longlongrightarrow> 0) at_top"
      using product_limit by simp
    have pointwise_identity:
        "- (slp_center_phase 0 xi / (4 * tau)) =
          (- slp_center_phase 0 xi / 4) * inverse tau" for tau :: real
      apply (simp only: divide_inverse inverse_mult_distrib)
      done
    have eventual_identity:
        "\<forall>\<^sub>F tau :: real in at_top.
          - (slp_center_phase 0 xi / (4 * tau)) =
            (- slp_center_phase 0 xi / 4) * inverse tau"
      by (rule always_eventually) (intro allI, rule pointwise_identity)
    show ?thesis
      using product_zero
      by (rule tendsto_cong[OF eventual_identity, THEN iffD2])
  qed
  have real_embedding_limit:
      "((\<lambda>tau. (of_real
          (- (slp_center_phase 0 xi / (4 * tau))) :: complex))
        \<longlongrightarrow> (of_real 0 :: complex)) at_top"
    by (rule tendsto_of_real_iff[where 'a=complex, THEN iffD2])
      (rule scalar_limit)
  have imaginary_limit:
      "((\<lambda>tau. \<i> *
          of_real (- (slp_center_phase 0 xi / (4 * tau))))
        \<longlongrightarrow> \<i> * of_real 0) at_top"
    by (rule tendsto_mult[OF tendsto_const real_embedding_limit])
  have exponential_limit:
      "((\<lambda>tau. exp (\<i> *
          of_real (- (slp_center_phase 0 xi / (4 * tau)))))
        \<longlongrightarrow> exp (\<i> * of_real 0)) at_top"
    by (rule tendsto_exp[OF imaginary_limit])
  show ?thesis
    unfolding slp_center_fourier_multiplier_def
    using exponential_limit by simp
qed

lemma slp_center_fourier_multiplier_l2_isometry:
  assumes f_l2: "aim_complex_lp_on_plane 2 f"
  shows
    "aim_complex_lp_on_plane 2
        (\<lambda>xi. slp_center_fourier_multiplier tau xi * f xi)"
    "integral\<^sup>L lborel
        (\<lambda>xi. cmod
          (slp_center_fourier_multiplier tau xi * f xi) powr 2) =
      integral\<^sup>L lborel (\<lambda>xi. cmod (f xi) powr 2)"
proof -
  show "aim_complex_lp_on_plane 2
      (\<lambda>xi. slp_center_fourier_multiplier tau xi * f xi)"
  proof (rule aim_complex_lp_on_plane_two_bounded_multiplier[
      OF slp_center_fourier_multiplier_measurable f_l2,
      where C=1])
    show "\<And>xi. cmod (slp_center_fourier_multiplier tau xi) \<le> 1"
      by simp
    show "0 \<le> (1 :: real)"
      by simp
  qed
  show "integral\<^sup>L lborel
        (\<lambda>xi. cmod
          (slp_center_fourier_multiplier tau xi * f xi) powr 2) =
      integral\<^sup>L lborel (\<lambda>xi. cmod (f xi) powr 2)"
    by (intro Bochner_Integration.integral_cong[OF refl])
      (simp only: norm_mult slp_center_fourier_multiplier_norm mult_1_left)
qed

theorem slp_center_fourier_multiplier_l2_error_tendsto_zero:
  assumes f_l2: "aim_complex_lp_on_plane 2 f"
  shows
    "\<forall>tau. aim_complex_lp_on_plane 2
      (\<lambda>xi. (slp_center_fourier_multiplier tau xi - 1) * f xi)"
    "((\<lambda>tau. integral\<^sup>L lborel
        (\<lambda>xi. cmod
          ((slp_center_fourier_multiplier tau xi - 1) * f xi) powr 2))
      \<longlongrightarrow> 0) at_top"
proof -
  have f_measurable: "f \<in> borel_measurable lborel"
    and f_square_integrable:
      "integrable lborel (\<lambda>xi. cmod (f xi) powr 2)"
    using f_l2 unfolding aim_complex_lp_on_plane_def by auto

  have error_multiplier_measurable:
      "(\<lambda>xi. slp_center_fourier_multiplier tau xi - 1) \<in>
        borel_measurable lborel" for tau
    using slp_center_fourier_multiplier_measurable[of tau]
    by measurable
  have error_multiplier_bound:
      "cmod (slp_center_fourier_multiplier tau xi - 1) \<le> 2"
      for tau xi
  proof -
    have "cmod (slp_center_fourier_multiplier tau xi - 1) \<le>
        cmod (slp_center_fourier_multiplier tau xi) + cmod (1 :: complex)"
      by (rule norm_triangle_ineq4)
    also have "... = 2"
      by simp
    finally show ?thesis .
  qed

  show "\<forall>tau. aim_complex_lp_on_plane 2
      (\<lambda>xi. (slp_center_fourier_multiplier tau xi - 1) * f xi)"
  proof
    fix tau :: real
    show "aim_complex_lp_on_plane 2
        (\<lambda>xi. (slp_center_fourier_multiplier tau xi - 1) * f xi)"
    proof (rule aim_complex_lp_on_plane_two_bounded_multiplier[
        OF error_multiplier_measurable f_l2, where C=2])
      show "\<And>xi. cmod (slp_center_fourier_multiplier tau xi - 1) \<le> 2"
        by (rule error_multiplier_bound)
      show "0 \<le> (2 :: real)"
        by simp
    qed
  qed

  let ?s = "\<lambda>tau xi.
    cmod ((slp_center_fourier_multiplier tau xi - 1) * f xi) powr 2"
  let ?w = "\<lambda>xi. 4 * (cmod (f xi) powr 2)"

  have zero_measurable:
      "(\<lambda>_ :: slp_point. (0 :: real)) \<in> borel_measurable lborel"
    by simp
  have error_square_measurable:
      "?s tau \<in> borel_measurable lborel" for tau
    using error_multiplier_measurable[of tau] f_measurable
    by measurable
  have majorant_integrable: "integrable lborel ?w"
    using f_square_integrable by simp

  have error_square_limit:
      "((\<lambda>tau. ?s tau xi) \<longlongrightarrow> 0) at_top" for xi
  proof -
    have multiplier_difference_limit_raw:
        "((\<lambda>tau. slp_center_fourier_multiplier tau xi -
            (1 :: complex)) \<longlongrightarrow> (1 :: complex) - 1) at_top"
      by (rule tendsto_diff[OF
          slp_center_fourier_multiplier_tendsto_one tendsto_const])
    have multiplier_difference_limit:
        "((\<lambda>tau. slp_center_fourier_multiplier tau xi - 1)
          \<longlongrightarrow> 0) at_top"
      using multiplier_difference_limit_raw by simp
    have product_limit:
        "((\<lambda>tau. (slp_center_fourier_multiplier tau xi - 1) * f xi)
          \<longlongrightarrow> 0) at_top"
      using tendsto_mult[OF multiplier_difference_limit tendsto_const]
      by simp
    have norm_limit:
        "((\<lambda>tau. cmod
          ((slp_center_fourier_multiplier tau xi - 1) * f xi))
          \<longlongrightarrow> 0) at_top"
      using tendsto_norm[OF product_limit] by simp
    have square_limit:
        "((\<lambda>tau. cmod
          ((slp_center_fourier_multiplier tau xi - 1) * f xi) ^ 2)
          \<longlongrightarrow> 0) at_top"
      unfolding power2_eq_square
      using tendsto_mult[OF norm_limit norm_limit] by simp
    show ?thesis
      using square_limit by (simp only: powr_numeral norm_ge_zero)
  qed
  have pointwise_limit:
      "AE xi in lborel. ((\<lambda>tau. ?s tau xi) \<longlongrightarrow> 0) at_top"
    by (rule AE_I2) (rule error_square_limit)

  have error_square_bound:
      "Real_Vector_Spaces.norm (?s tau xi) \<le> ?w xi" for tau xi
  proof -
    have product_bound:
        "cmod ((slp_center_fourier_multiplier tau xi - 1) * f xi) \<le>
          2 * cmod (f xi)"
      unfolding norm_mult
      by (rule mult_right_mono[OF error_multiplier_bound]) simp
    have square_bound:
        "cmod ((slp_center_fourier_multiplier tau xi - 1) * f xi) ^ 2 \<le>
          (2 * cmod (f xi)) ^ 2"
      by (rule power_mono[OF product_bound]) simp
    show ?thesis
      using square_bound
      by (simp add: powr_numeral power_mult_distrib)
  qed
  have bound_each:
      "AE xi in lborel. Real_Vector_Spaces.norm (?s tau xi) \<le> ?w xi"
      for tau
    by (rule AE_I2) (rule error_square_bound)
  have eventual_bound:
      "\<forall>\<^sub>F tau :: real in at_top.
        AE xi in lborel. Real_Vector_Spaces.norm (?s tau xi) \<le> ?w xi"
    by (rule always_eventually) (intro allI, rule bound_each)

  have integral_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (?s tau))
        \<longlongrightarrow> integral\<^sup>L lborel
          (\<lambda>_ :: slp_point. (0 :: real))) at_top"
    by (rule Bochner_Integration.integral_dominated_convergence_at_top[
        OF zero_measurable error_square_measurable majorant_integrable
          pointwise_limit eventual_bound])
  show "((\<lambda>tau. integral\<^sup>L lborel (?s tau)) \<longlongrightarrow> 0) at_top"
    using integral_limit by simp
qed

end
