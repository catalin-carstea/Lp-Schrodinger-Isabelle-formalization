theory Inverse_Schrodinger_Lp_Fourier_L1
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Center_Multiplier_L2"
begin

section \<open>The planar Fourier transform on integrable complex fields\<close>

definition slp_fourier_phase ::
  "slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_fourier_phase xi x =
    exp (\<i> * of_real (- inner x xi))"

definition slp_fourier_transform ::
  "(slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_fourier_transform f xi =
    integral\<^sup>L lborel (\<lambda>x. slp_fourier_phase xi x * f x)"

lemma slp_fourier_phase_measurable:
  "slp_fourier_phase xi \<in> borel_measurable lborel"
  unfolding slp_fourier_phase_def
  by measurable

lemma slp_fourier_phase_joint_measurable:
  "(\<lambda>p :: slp_point \<times> slp_point.
      slp_fourier_phase (fst p) (snd p)) \<in>
    borel_measurable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))"
proof -
  have phase_continuous:
      "continuous_on UNIV
        (\<lambda>p :: slp_point \<times> slp_point.
          slp_fourier_phase (fst p) (snd p))"
    unfolding slp_fourier_phase_def
    by (intro continuous_intros)
  have phase_raw:
      "(\<lambda>p :: slp_point \<times> slp_point.
          slp_fourier_phase (fst p) (snd p)) \<in>
        borel_measurable
          (lborel :: (slp_point \<times> slp_point) measure)"
    using borel_measurable_continuous_onI[OF phase_continuous]
    by simp
  show ?thesis
    using phase_raw by (simp only: lborel_prod)
qed

lemma slp_fourier_phase_norm [simp]:
  "cmod (slp_fourier_phase xi x) = 1"
  unfolding slp_fourier_phase_def
  by (simp only: norm_exp_i_times)

lemma slp_fourier_integrand_integrable:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
  shows "integrable lborel (\<lambda>x. slp_fourier_phase xi x * f x)"
proof (rule Bochner_Integration.integrable_bound[OF f_integrable])
  show "(\<lambda>x. slp_fourier_phase xi x * f x) \<in>
      borel_measurable lborel"
    using slp_fourier_phase_measurable[of xi] f_integrable
    by measurable
  show "AE x in lborel.
      Real_Vector_Spaces.norm (slp_fourier_phase xi x * f x) \<le>
        Real_Vector_Spaces.norm (f x)"
    by (simp only: norm_mult slp_fourier_phase_norm mult_1_left
        order_refl eventually_True)
qed

lemma slp_fourier_transform_measurable:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_fourier_transform f \<in> borel_measurable lborel"
proof -
  have f_snd_measurable[measurable]:
      "(\<lambda>p :: slp_point \<times> slp_point. f (snd p)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    using measurable_snd''[
      OF f_measurable,
      where P="lborel :: slp_point measure"] .
  have phase_measurable[measurable]:
      "(\<lambda>p :: slp_point \<times> slp_point.
          slp_fourier_phase (fst p) (snd p)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    using slp_fourier_phase_joint_measurable by simp
  have joint_integrand_measurable:
      "(\<lambda>p :: slp_point \<times> slp_point.
          slp_fourier_phase (fst p) (snd p) * f (snd p)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    by measurable
  have parameter_integral_measurable:
      "(\<lambda>xi. integral\<^sup>L lborel
          (\<lambda>x. slp_fourier_phase xi x * f x)) \<in>
        borel_measurable (lborel :: slp_point measure)"
    by (rule lborel.borel_measurable_lebesgue_integral[
        where f="\<lambda>xi x. slp_fourier_phase xi x * f x"])
      (use joint_integrand_measurable in simp)
  show ?thesis
    unfolding slp_fourier_transform_def
    using parameter_integral_measurable .
qed

lemma slp_fourier_transform_norm_bound:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
  shows "cmod (slp_fourier_transform f xi) \<le>
    integral\<^sup>L lborel (\<lambda>x. cmod (f x))"
proof -
  have integral_bound:
      "cmod (integral\<^sup>L lborel
          (\<lambda>x. slp_fourier_phase xi x * f x)) \<le>
        integral\<^sup>L lborel
          (\<lambda>x. cmod (slp_fourier_phase xi x * f x))"
    by (rule Bochner_Integration.integral_norm_bound)
  have norm_identity:
      "integral\<^sup>L lborel
          (\<lambda>x. cmod (slp_fourier_phase xi x * f x)) =
        integral\<^sup>L lborel (\<lambda>x. cmod (f x))"
    by (intro Bochner_Integration.integral_cong[OF refl])
      (simp only: norm_mult slp_fourier_phase_norm mult_1_left)
  show ?thesis
    unfolding slp_fourier_transform_def
    using integral_bound norm_identity by simp
qed

lemma slp_fourier_transform_zero [simp]:
  "slp_fourier_transform (\<lambda>_ :: slp_point. 0) xi = 0"
  unfolding slp_fourier_transform_def by simp

lemma slp_fourier_transform_add:
  fixes f g :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
  shows "slp_fourier_transform (\<lambda>x. f x + g x) xi =
    slp_fourier_transform f xi + slp_fourier_transform g xi"
proof -
  have f_phase_integrable:
      "integrable lborel (\<lambda>x. slp_fourier_phase xi x * f x)"
    by (rule slp_fourier_integrand_integrable[OF f_integrable])
  have g_phase_integrable:
      "integrable lborel (\<lambda>x. slp_fourier_phase xi x * g x)"
    by (rule slp_fourier_integrand_integrable[OF g_integrable])
  show ?thesis
    unfolding slp_fourier_transform_def
    by (simp only: distrib_left
        Bochner_Integration.integral_add[OF
          f_phase_integrable g_phase_integrable])
qed

lemma slp_fourier_transform_mult:
  fixes f :: "slp_point \<Rightarrow> complex"
    and a :: complex
  assumes f_integrable: "integrable lborel f"
  shows "slp_fourier_transform (\<lambda>x. a * f x) xi =
    a * slp_fourier_transform f xi"
proof -
  have phase_integrable:
      "integrable lborel (\<lambda>x. slp_fourier_phase xi x * f x)"
    by (rule slp_fourier_integrand_integrable[OF f_integrable])
  have integrand_identity:
      "(\<lambda>x. slp_fourier_phase xi x * (a * f x)) =
        (\<lambda>x. a * (slp_fourier_phase xi x * f x))"
    by (rule ext) (simp add: algebra_simps)
  show ?thesis
    unfolding slp_fourier_transform_def
    unfolding integrand_identity
    by (rule Bochner_Integration.integral_mult_right[OF phase_integrable])
qed

end
