theory Inverse_Schrodinger_Lp_Fourier_Covariance
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_L1"
begin

section \<open>Translation and modulation covariance of the planar Fourier transform\<close>

lemma slp_fourier_phase_spatial_add:
  "slp_fourier_phase xi (x + a) =
    slp_fourier_phase xi a * slp_fourier_phase xi x"
proof -
  have exponent_identity:
      "\<i> * of_real (- inner (x + a) xi) =
        \<i> * of_real (- inner a xi) +
          \<i> * of_real (- inner x xi)"
    by (simp add: inner_add_left algebra_simps)
  show ?thesis
    unfolding slp_fourier_phase_def exponent_identity
    by (rule exp_add)
qed

lemma slp_fourier_phase_frequency_add:
  "slp_fourier_phase (xi + eta) x =
    slp_fourier_phase eta x * slp_fourier_phase xi x"
proof -
  have exponent_identity:
      "\<i> * of_real (- inner x (xi + eta)) =
        \<i> * of_real (- inner x eta) +
          \<i> * of_real (- inner x xi)"
    by (simp add: inner_add_right algebra_simps)
  show ?thesis
    unfolding slp_fourier_phase_def exponent_identity
    by (rule exp_add)
qed

lemma slp_fourier_translate_integrable:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
  shows "integrable lborel (\<lambda>x. f (x - a))"
proof -
  have translated:
      "integrable lborel (\<lambda>x. f (-a + x))"
    by (rule slp_lborel_integrable_translate[OF f_integrable])
  show ?thesis
    using translated by (simp only: add.commute diff_conv_add_uminus)
qed

lemma slp_fourier_transform_translate:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
  shows "slp_fourier_transform (\<lambda>x. f (x - a)) xi =
    slp_fourier_phase xi a * slp_fourier_transform f xi"
proof -
  have phase_f_integrable:
      "integrable lborel (\<lambda>x. slp_fourier_phase xi x * f x)"
    by (rule slp_fourier_integrand_integrable[OF f_integrable])
  have shifted_integrable:
      "integrable lborel
        (\<lambda>x. slp_fourier_phase xi (a + x) * f x)"
  proof -
    have integrand_identity:
        "(\<lambda>x. slp_fourier_phase xi (a + x) * f x) =
          (\<lambda>x. slp_fourier_phase xi a *
            (slp_fourier_phase xi x * f x))"
      by (rule ext)
        (simp only: slp_fourier_phase_spatial_add mult.assoc
          mult.commute mult.left_commute)
    show ?thesis
      unfolding integrand_identity
      by (rule Bochner_Integration.integrable_mult_right)
        (rule phase_f_integrable)
  qed
  have translated_integral:
      "integral\<^sup>L lborel
          (\<lambda>x. slp_fourier_phase xi x * f (x - a)) =
        integral\<^sup>L lborel
          (\<lambda>x. slp_fourier_phase xi (a + x) * f x)"
  proof -
    have translation:
        "integral\<^sup>L lborel
            (\<lambda>x. slp_fourier_phase xi (a + (-a + x)) * f (-a + x)) =
          integral\<^sup>L lborel
            (\<lambda>x. slp_fourier_phase xi (a + x) * f x)"
      by (rule slp_lborel_integral_translate[OF shifted_integrable])
    show ?thesis
      using translation by (simp add: algebra_simps)
  qed
  have scalar_integral:
      "integral\<^sup>L lborel
          (\<lambda>x. slp_fourier_phase xi (a + x) * f x) =
        slp_fourier_phase xi a *
          integral\<^sup>L lborel
            (\<lambda>x. slp_fourier_phase xi x * f x)"
  proof -
    have integrand_identity:
        "(\<lambda>x. slp_fourier_phase xi (a + x) * f x) =
          (\<lambda>x. slp_fourier_phase xi a *
            (slp_fourier_phase xi x * f x))"
      by (rule ext)
        (simp only: slp_fourier_phase_spatial_add mult.assoc
          mult.commute mult.left_commute)
    show ?thesis
      unfolding integrand_identity
      by (rule Bochner_Integration.integral_mult_right[OF phase_f_integrable])
  qed
  show ?thesis
    unfolding slp_fourier_transform_def
    using translated_integral scalar_integral by simp
qed

lemma slp_fourier_modulate_integrable:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
  shows "integrable lborel (\<lambda>x. slp_fourier_phase eta x * f x)"
  by (rule slp_fourier_integrand_integrable[OF f_integrable])

lemma slp_fourier_transform_modulate:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
  shows "slp_fourier_transform
      (\<lambda>x. slp_fourier_phase eta x * f x) xi =
    slp_fourier_transform f (xi + eta)"
proof -
  have integrand_identity:
      "(\<lambda>x. slp_fourier_phase xi x *
          (slp_fourier_phase eta x * f x)) =
        (\<lambda>x. slp_fourier_phase (xi + eta) x * f x)"
    by (rule ext)
      (simp only: slp_fourier_phase_frequency_add mult.assoc
        mult.commute mult.left_commute)
  show ?thesis
    unfolding slp_fourier_transform_def
    unfolding integrand_identity
    by simp
qed

end
