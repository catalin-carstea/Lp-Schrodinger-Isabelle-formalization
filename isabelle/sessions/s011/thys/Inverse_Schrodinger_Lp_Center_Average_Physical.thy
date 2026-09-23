theory Inverse_Schrodinger_Lp_Center_Average_Physical
  imports Inverse_Schrodinger_Lp_Residual_Cartesian_Integrability
begin

section \<open>The physical quadratic center average\<close>

definition slp_center_phase :: "slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_center_phase c z =
    (z $ (0 :: 2) - c $ (0 :: 2)) ^ 2 -
    (z $ (1 :: 2) - c $ (1 :: 2)) ^ 2"

definition slp_center_kernel ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_center_kernel tau c z =
    exp (\<i> * of_real (tau * slp_center_phase c z))"

definition slp_center_average ::
  "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
    slp_point \<Rightarrow> complex"
where
  "slp_center_average tau f c =
    of_real (tau / pi) *
      integral\<^sup>L lborel (\<lambda>z. slp_center_kernel tau c z * f z)"

lemma slp_center_phase_symmetric:
  "slp_center_phase c z = slp_center_phase z c"
  unfolding slp_center_phase_def
  by (simp add: power2_eq_square algebra_simps)

lemma slp_center_kernel_symmetric:
  "slp_center_kernel tau c z = slp_center_kernel tau z c"
  by (simp only: slp_center_kernel_def slp_center_phase_symmetric)

lemma slp_center_phase_measurable:
  "slp_center_phase c \<in> borel_measurable lborel"
  unfolding slp_center_phase_def
  by measurable

lemma slp_center_kernel_measurable:
  "slp_center_kernel tau c \<in> borel_measurable lborel"
  unfolding slp_center_kernel_def
  using slp_center_phase_measurable[of c]
  by measurable

lemma slp_center_kernel_integrable_mult:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
  shows "integrable lborel (\<lambda>z. slp_center_kernel tau c z * f z)"
proof (rule Bochner_Integration.integrable_bound[OF f_integrable])
  show "(\<lambda>z. slp_center_kernel tau c z * f z) \<in>
      borel_measurable lborel"
    using slp_center_kernel_measurable[of tau c] f_integrable
    by measurable
  show "AE z in lborel.
      norm (slp_center_kernel tau c z * f z) \<le> norm (f z)"
    unfolding slp_center_kernel_def
    by (simp only: norm_mult norm_exp_i_times mult_1_left order_refl
        eventually_True)
qed

lemma slp_center_average_fixed_tau_bound:
  fixes f :: "slp_point \<Rightarrow> complex"
  shows
    "norm (slp_center_average tau f c) \<le>
      norm (of_real (tau / pi) :: complex) *
        integral\<^sup>L lborel (\<lambda>z. norm (f z))"
proof -
  have integral_bound:
    "norm (integral\<^sup>L lborel
        (\<lambda>z. slp_center_kernel tau c z * f z)) \<le>
      integral\<^sup>L lborel
        (\<lambda>z. norm (slp_center_kernel tau c z * f z))"
    by (rule Bochner_Integration.integral_norm_bound)
  have norm_identity:
    "integral\<^sup>L lborel
        (\<lambda>z. norm (slp_center_kernel tau c z * f z)) =
      integral\<^sup>L lborel (\<lambda>z. norm (f z))"
    unfolding slp_center_kernel_def
    by (intro Bochner_Integration.integral_cong[OF refl])
      (simp only: norm_mult norm_exp_i_times mult_1_left)
  have coefficient_nonnegative:
    "0 \<le> norm (of_real (tau / pi) :: complex)"
    by simp
  show ?thesis
    unfolding slp_center_average_def
  proof (subst norm_mult)
    show
      "norm (of_real (tau / pi) :: complex) *
          norm (integral\<^sup>L lborel
            (\<lambda>z. slp_center_kernel tau c z * f z))
        \<le> norm (of_real (tau / pi) :: complex) *
          integral\<^sup>L lborel (\<lambda>z. norm (f z))"
      using mult_left_mono[OF integral_bound coefficient_nonnegative]
      by (simp only: norm_identity)
  qed
qed

corollary slp_center_average_L1_Linfinity:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes tau_positive: "0 < tau"
  shows
    "norm (slp_center_average tau f c) \<le>
      (tau / pi) * integral\<^sup>L lborel (\<lambda>z. norm (f z))"
proof -
  have ratio_positive: "0 < tau / pi"
    using tau_positive pi_gt_zero by (rule divide_pos_pos)
  have coefficient_identity:
    "norm (of_real (tau / pi) :: complex) = tau / pi"
    apply (subst norm_of_real)
    using ratio_positive by (rule abs_of_pos)
  show ?thesis
    using slp_center_average_fixed_tau_bound[
      where tau=tau and f=f and c=c]
    by (simp only: coefficient_identity)
qed

lemma slp_separated_product_integrable:
  fixes f g :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
  shows
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
      (\<lambda>(c, z). f c * g z)"
proof -
  have product_measurable:
    "(\<lambda>(c, z). f c * g z) \<in>
      borel_measurable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))"
    using f_integrable g_integrable by measurable
  have f_norm_integrable:
    "integrable lborel (\<lambda>c. norm (f c))"
    using f_integrable by simp
  have scaled_norm_integrable:
    "integrable lborel
      (\<lambda>c. norm (f c) *
        integral\<^sup>L lborel (\<lambda>z. norm (g z)))"
  proof (rule Bochner_Integration.integrable_mult_left)
    assume "integral\<^sup>L lborel (\<lambda>z. norm (g z)) \<noteq> 0"
    show "integrable lborel (\<lambda>c. norm (f c))"
      by (rule f_norm_integrable)
  qed
  have outer_integrable:
    "integrable (lborel :: slp_point measure)
      (\<lambda>c. integral\<^sup>L lborel (\<lambda>z. norm (f c * g z)))"
  proof -
    have integrable_iff:
      "integrable lborel
          (\<lambda>c. integral\<^sup>L lborel (\<lambda>z. norm (f c * g z)))
        \<longleftrightarrow>
       integrable lborel
          (\<lambda>c. norm (f c) *
            integral\<^sup>L lborel (\<lambda>z. norm (g z)))"
    proof (rule Bochner_Integration.integrable_cong)
      show "lborel = (lborel :: slp_point measure)"
        by simp
      fix c :: slp_point
      assume "c \<in> space (lborel :: slp_point measure)"
      show
        "integral\<^sup>L lborel (\<lambda>z. norm (f c * g z)) =
          norm (f c) *
            integral\<^sup>L lborel (\<lambda>z. norm (g z))"
        by (simp only: norm_mult
            Bochner_Integration.integral_mult_right_zero)
    qed
    show ?thesis
      by (rule iffD2[OF integrable_iff scaled_norm_integrable])
  qed
  have inner_integrable_all:
    "\<forall>c. integrable lborel (\<lambda>z. f c * g z)"
  proof
    fix c
    show "integrable lborel (\<lambda>z. f c * g z)"
    proof (rule Bochner_Integration.integrable_mult_right)
      assume "f c \<noteq> 0"
      show "integrable lborel g"
        by (rule g_integrable)
    qed
  qed
  have inner_integrable:
    "AE c in (lborel :: slp_point measure).
      integrable lborel (\<lambda>z. f c * g z)"
    using inner_integrable_all by simp
  show ?thesis
    apply (rule lborel_pair.Fubini_integrable[
        where f="\<lambda>(c, z). f c * g z"])
    using product_measurable outer_integrable inner_integrable
    apply simp_all
    done
qed

lemma slp_center_product_integrable:
  fixes f g :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
  shows
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
      (\<lambda>(c, z).
        f c * (slp_center_kernel tau c z * g z))"
proof (rule Bochner_Integration.integrable_bound[
    OF slp_separated_product_integrable[OF f_integrable g_integrable]])
  show "(\<lambda>(c, z). f c * (slp_center_kernel tau c z * g z)) \<in>
      borel_measurable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))"
  proof -
    have f_measurable[measurable]:
      "f \<in> borel_measurable (lborel :: slp_point measure)"
      using f_integrable by measurable
    have g_measurable[measurable]:
      "g \<in> borel_measurable (lborel :: slp_point measure)"
      using g_integrable by measurable
    have f_fst_measurable[measurable]:
      "(\<lambda>p :: slp_point \<times> slp_point. f (fst p)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
      using measurable_fst''[
        OF f_measurable, where P="lborel :: slp_point measure"] .
    have g_snd_measurable[measurable]:
      "(\<lambda>p :: slp_point \<times> slp_point. g (snd p)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
      using measurable_snd''[
        OF g_measurable, where P="lborel :: slp_point measure"] .
    have phase_continuous:
      "continuous_on UNIV
        (\<lambda>p :: slp_point \<times> slp_point.
          slp_center_phase (fst p) (snd p))"
      unfolding slp_center_phase_def
      by (intro continuous_intros)
    have phase_raw:
      "(\<lambda>p :: slp_point \<times> slp_point.
          slp_center_phase (fst p) (snd p)) \<in>
        borel_measurable
          (lborel :: (slp_point \<times> slp_point) measure)"
      using borel_measurable_continuous_onI[OF phase_continuous]
      by simp
    have phase_measurable[measurable]:
      "(\<lambda>p :: slp_point \<times> slp_point.
          slp_center_phase (fst p) (snd p)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
      using phase_raw by (simp only: lborel_prod)
    show ?thesis
      unfolding slp_center_kernel_def
      by measurable
  qed
  show "AE p in
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: slp_point measure)).
      norm ((case p of (c, z) \<Rightarrow>
        f c * (slp_center_kernel tau c z * g z))) \<le>
      norm ((case p of (c, z) \<Rightarrow> f c * g z))"
    unfolding slp_center_kernel_def
    by (simp only: split_beta norm_mult norm_exp_i_times mult_1_left
        mult.assoc order_refl eventually_True)
qed

theorem slp_center_average_bilinear_transpose:
  fixes f g :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
  shows
    "integral\<^sup>L lborel
        (\<lambda>c. f c * slp_center_average tau g c) =
      integral\<^sup>L lborel
        (\<lambda>z. g z * slp_center_average tau f z)"
proof -
  let ?H = "\<lambda>c z.
    f c * (slp_center_kernel tau c z * g z)"
  have H_integrable:
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
      (case_prod ?H)"
    using slp_center_product_integrable[where tau=tau and f=f and g=g,
      OF f_integrable g_integrable]
    by simp
  have fubini:
    "integral\<^sup>L lborel
        (\<lambda>c. integral\<^sup>L lborel (\<lambda>z. ?H c z)) =
      integral\<^sup>L lborel
        (\<lambda>z. integral\<^sup>L lborel (\<lambda>c. ?H c z))"
    using lborel_pair.Fubini_integral[OF H_integrable, symmetric]
    by simp
  have left_identity:
    "integral\<^sup>L lborel
        (\<lambda>c. f c * slp_center_average tau g c) =
      of_real (tau / pi) *
        integral\<^sup>L lborel
          (\<lambda>c. integral\<^sup>L lborel (\<lambda>z. ?H c z))"
  proof -
    have inner_identity:
      "integral\<^sup>L lborel (\<lambda>z. ?H c z) =
        f c * integral\<^sup>L lborel
          (\<lambda>z. slp_center_kernel tau c z * g z)" for c
      by (simp only: Bochner_Integration.integral_mult_right_zero)
    show ?thesis
      unfolding slp_center_average_def
      by (simp only: inner_identity; simp add: algebra_simps)
  qed
  have right_identity:
    "integral\<^sup>L lborel
        (\<lambda>z. g z * slp_center_average tau f z) =
      of_real (tau / pi) *
        integral\<^sup>L lborel
          (\<lambda>z. integral\<^sup>L lborel (\<lambda>c. ?H c z))"
  proof -
    have inner_identity:
      "integral\<^sup>L lborel (\<lambda>c. ?H c z) =
        g z * integral\<^sup>L lborel
          (\<lambda>c. slp_center_kernel tau z c * f c)" for z
    proof -
      have pointwise:
        "?H c z =
          g z * (slp_center_kernel tau z c * f c)" for c
        by (simp only: slp_center_kernel_symmetric)
          (simp add: algebra_simps)
      show ?thesis
        by (simp only: pointwise Bochner_Integration.integral_mult_right_zero)
    qed
    show ?thesis
      unfolding slp_center_average_def
      by (simp only: inner_identity; simp add: algebra_simps)
  qed
  show ?thesis
    using left_identity right_identity fubini by simp
qed

end
