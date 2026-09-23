theory Inverse_Schrodinger_Lp_Complex_Convolution
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Covariance"
begin

section \<open>Complex L1 convolution and its Fourier transform\<close>

definition slp_complex_convolution ::
  "(slp_point \<Rightarrow> complex) \<Rightarrow>
    (slp_point \<Rightarrow> complex) \<Rightarrow>
    slp_point \<Rightarrow> complex"
where
  "slp_complex_convolution f g x =
    integral\<^sup>L lborel (\<lambda>y. f y * g (x - y))"

lemma slp_complex_convolution_integrable:
  fixes f g :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
  shows "integrable lborel (slp_complex_convolution f g)"
proof -
  let ?H = "\<lambda>y x. f y * g (x - y)"
  have H_measurable:
      "case_prod ?H \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    using f_integrable g_integrable by measurable
  have inner_integrable_all:
      "\<forall>y. integrable lborel (\<lambda>x. ?H y x)"
  proof
    fix y :: slp_point
    have translated_integrable:
        "integrable lborel (\<lambda>x. g (x - y))"
      by (rule slp_fourier_translate_integrable[OF g_integrable])
    show "integrable lborel (\<lambda>x. ?H y x)"
      by (rule Bochner_Integration.integrable_mult_right)
        (rule translated_integrable)
  qed
  have inner_integrable:
      "AE y in (lborel :: slp_point measure).
        integrable lborel (\<lambda>x. ?H y x)"
    using inner_integrable_all by simp
  have f_norm_integrable:
      "integrable lborel (\<lambda>y. norm_class.norm (f y))"
    using f_integrable by simp
  have g_norm_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (g x))"
    using g_integrable by simp
  have inner_norm_value:
      "integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (?H y x)) =
        norm_class.norm (f y) *
          integral\<^sup>L lborel
            (\<lambda>x. norm_class.norm (g x))"
      for y :: slp_point
  proof -
    have translated_norm:
        "integral\<^sup>L lborel
            (\<lambda>x. norm_class.norm (g (x - y))) =
          integral\<^sup>L lborel
            (\<lambda>x. norm_class.norm (g x))"
      using slp_lborel_integral_translate[
        where f="\<lambda>x. norm_class.norm (g x)" and a="-y",
        OF g_norm_integrable]
      by (simp only: add.commute diff_conv_add_uminus)
    show ?thesis
      by (simp only: norm_mult
          Bochner_Integration.integral_mult_right_zero translated_norm)
  qed
  have scaled_norm_integrable:
      "integrable lborel
        (\<lambda>y. norm_class.norm (f y) *
          integral\<^sup>L lborel
            (\<lambda>x. norm_class.norm (g x)))"
    by (rule Bochner_Integration.integrable_mult_left)
      (rule f_norm_integrable)
  have outer_integrable:
      "integrable lborel
        (\<lambda>y. integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (?H y x)))"
    by (simp only: inner_norm_value scaled_norm_integrable)
  have H_integrable:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))
        (case_prod ?H)"
    apply (rule lborel_pair.Fubini_integrable[
        where f="case_prod ?H"])
    using H_measurable outer_integrable inner_integrable
    apply simp_all
    done
  have iterated_integrable:
      "integrable lborel
        (\<lambda>x. integral\<^sup>L lborel (\<lambda>y. ?H y x))"
    by (rule lborel_pair.integrable_snd[OF H_integrable])
  show ?thesis
    unfolding slp_complex_convolution_def
    by (rule iterated_integrable)
qed

theorem slp_fourier_transform_complex_convolution:
  fixes f g :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
  shows
    "slp_fourier_transform (slp_complex_convolution f g) xi =
      slp_fourier_transform f xi * slp_fourier_transform g xi"
proof -
  let ?J =
    "\<lambda>y x. slp_fourier_phase xi x * (f y * g (x - y))"
  have phase_snd_measurable[measurable]:
      "(\<lambda>p :: slp_point \<times> slp_point.
          slp_fourier_phase xi (snd p)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    using measurable_snd''[
      OF slp_fourier_phase_measurable,
      where P="lborel :: slp_point measure"] .
  have convolution_joint_measurable[measurable]:
      "(\<lambda>p :: slp_point \<times> slp_point.
          f (fst p) * g (snd p - fst p)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    using f_integrable g_integrable by measurable
  have J_measurable:
      "case_prod ?J \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    using f_integrable g_integrable by measurable
  have J_inner_integrable_all:
      "\<forall>y. integrable lborel (\<lambda>x. ?J y x)"
  proof
    fix y :: slp_point
    have translated_integrable:
        "integrable lborel (\<lambda>x. g (x - y))"
      by (rule slp_fourier_translate_integrable[OF g_integrable])
    have phase_translated_integrable:
        "integrable lborel
          (\<lambda>x. slp_fourier_phase xi x * g (x - y))"
      by (rule slp_fourier_integrand_integrable[OF translated_integrable])
    have integrand_identity:
        "?J y x =
          f y * (slp_fourier_phase xi x * g (x - y))"
      for x :: slp_point
      by (simp only: mult.assoc mult.commute mult.left_commute)
    have scaled_integrable:
        "integrable lborel
          (\<lambda>x. f y *
            (slp_fourier_phase xi x * g (x - y)))"
      by (rule Bochner_Integration.integrable_mult_right)
        (rule phase_translated_integrable)
    show "integrable lborel (\<lambda>x. ?J y x)"
      by (simp only: integrand_identity scaled_integrable)
  qed
  have J_inner_integrable:
      "AE y in (lborel :: slp_point measure).
        integrable lborel (\<lambda>x. ?J y x)"
    using J_inner_integrable_all by simp
  have f_norm_integrable:
      "integrable lborel (\<lambda>y. norm_class.norm (f y))"
    using f_integrable by simp
  have g_norm_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (g x))"
    using g_integrable by simp
  have J_inner_norm_value:
      "integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (?J y x)) =
        norm_class.norm (f y) *
          integral\<^sup>L lborel
            (\<lambda>x. norm_class.norm (g x))"
      for y :: slp_point
  proof -
    have translated_norm:
        "integral\<^sup>L lborel
            (\<lambda>x. norm_class.norm (g (x - y))) =
          integral\<^sup>L lborel
            (\<lambda>x. norm_class.norm (g x))"
      using slp_lborel_integral_translate[
        where f="\<lambda>x. norm_class.norm (g x)" and a="-y",
        OF g_norm_integrable]
      by (simp only: add.commute diff_conv_add_uminus)
    show ?thesis
      by (simp only: norm_mult slp_fourier_phase_norm
          mult_1_left Bochner_Integration.integral_mult_right_zero
          translated_norm)
  qed
  have J_scaled_norm_integrable:
      "integrable lborel
        (\<lambda>y. norm_class.norm (f y) *
          integral\<^sup>L lborel
            (\<lambda>x. norm_class.norm (g x)))"
    by (rule Bochner_Integration.integrable_mult_left)
      (rule f_norm_integrable)
  have J_outer_integrable:
      "integrable lborel
        (\<lambda>y. integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (?J y x)))"
    by (simp only: J_inner_norm_value J_scaled_norm_integrable)
  have J_integrable:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))
        (case_prod ?J)"
    apply (rule lborel_pair.Fubini_integrable[
        where f="case_prod ?J"])
    using J_measurable J_outer_integrable J_inner_integrable
    apply simp_all
    done
  have left_identity:
      "slp_fourier_transform (slp_complex_convolution f g) xi =
        integral\<^sup>L lborel
          (\<lambda>x. integral\<^sup>L lborel (\<lambda>y. ?J y x))"
  proof -
    have integrand_identity:
        "slp_fourier_phase xi x * slp_complex_convolution f g x =
          integral\<^sup>L lborel (\<lambda>y. ?J y x)"
        for x :: slp_point
      unfolding slp_complex_convolution_def
      by (simp only: Bochner_Integration.integral_mult_right_zero
          mult.assoc)
    show ?thesis
      unfolding slp_fourier_transform_def
      by (rule Bochner_Integration.integral_cong[OF refl])
        (simp only: integrand_identity)
  qed
  have interchange:
      "integral\<^sup>L lborel
          (\<lambda>x. integral\<^sup>L lborel (\<lambda>y. ?J y x)) =
        integral\<^sup>L lborel
          (\<lambda>y. integral\<^sup>L lborel (\<lambda>x. ?J y x))"
    by (rule lborel_pair.Fubini_integral[OF J_integrable])
  have inner_value:
      "integral\<^sup>L lborel (\<lambda>x. ?J y x) =
        f y *
          (slp_fourier_phase xi y * slp_fourier_transform g xi)"
      for y :: slp_point
  proof -
    have covariance:
        "integral\<^sup>L lborel
            (\<lambda>x. slp_fourier_phase xi x * g (x - y)) =
          slp_fourier_phase xi y * slp_fourier_transform g xi"
      using slp_fourier_transform_translate[
        where f=g and a=y and xi=xi, OF g_integrable]
      unfolding slp_fourier_transform_def .
    have integrand_identity:
        "?J y x =
          f y * (slp_fourier_phase xi x * g (x - y))"
        for x :: slp_point
      by (simp only: mult.assoc mult.commute mult.left_commute)
    show ?thesis
      by (simp only: integrand_identity
          Bochner_Integration.integral_mult_right_zero covariance)
  qed
  have outer_value:
      "integral\<^sup>L lborel
          (\<lambda>y. integral\<^sup>L lborel (\<lambda>x. ?J y x)) =
        slp_fourier_transform f xi * slp_fourier_transform g xi"
  proof -
    have integrand_identity:
        "f y * (slp_fourier_phase xi y * slp_fourier_transform g xi) =
          (slp_fourier_phase xi y * f y) *
            slp_fourier_transform g xi"
        for y :: slp_point
      by (simp only: mult.assoc mult.commute mult.left_commute)
    have outer_integrand:
        "integral\<^sup>L lborel (\<lambda>x. ?J y x) =
          (slp_fourier_phase xi y * f y) *
            slp_fourier_transform g xi"
        for y :: slp_point
    proof -
      have
          "integral\<^sup>L lborel (\<lambda>x. ?J y x) =
            f y *
              (slp_fourier_phase xi y *
                slp_fourier_transform g xi)"
        by (rule inner_value)
      also have "... =
          (slp_fourier_phase xi y * f y) *
            slp_fourier_transform g xi"
        by (rule integrand_identity)
      finally show ?thesis .
    qed
    show ?thesis
      by (simp only: outer_integrand
          Bochner_Integration.integral_mult_left_zero
          slp_fourier_transform_def)
  qed
  show ?thesis
    using left_identity interchange outer_value by simp
qed

end
