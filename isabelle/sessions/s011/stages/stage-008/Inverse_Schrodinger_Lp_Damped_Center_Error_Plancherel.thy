theory Inverse_Schrodinger_Lp_Damped_Center_Error_Plancherel
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Damped_Center_Average_Fourier"
begin

section \<open>The damped physical center error in the dense Plancherel class\<close>

lemma slp_damped_center_average_norm_bound:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes eps_nonnegative: "0 \<le> eps"
    and f_integrable: "integrable lborel f"
  shows "cmod (slp_damped_center_average eps tau f c) \<le>
    cmod (of_real (tau / pi) :: complex) *
      integral\<^sup>L lborel (\<lambda>z. cmod (f z))"
proof -
  have integrand_integrable:
      "integrable lborel
        (\<lambda>z. slp_damped_center_kernel eps tau (z - c) * f z)"
    by (rule slp_damped_center_average_integrand_integrable[OF
          eps_nonnegative f_integrable])
  have integrand_norm_integrable:
      "integrable lborel
        (\<lambda>z. cmod
          (slp_damped_center_kernel eps tau (z - c) * f z))"
    using integrand_integrable by simp
  have f_norm_integrable:
      "integrable lborel (\<lambda>z. cmod (f z))"
    using f_integrable by simp
  have integral_norm_bound:
      "cmod (integral\<^sup>L lborel
          (\<lambda>z. slp_damped_center_kernel eps tau (z - c) * f z)) \<le>
        integral\<^sup>L lborel
          (\<lambda>z. cmod
            (slp_damped_center_kernel eps tau (z - c) * f z))"
    by (rule Bochner_Integration.integral_norm_bound)
  have norm_integral_le:
      "integral\<^sup>L lborel
          (\<lambda>z. cmod
            (slp_damped_center_kernel eps tau (z - c) * f z)) \<le>
        integral\<^sup>L lborel (\<lambda>z. cmod (f z))"
  proof (rule Bochner_Integration.integral_mono[OF
      integrand_norm_integrable f_norm_integrable])
    fix z :: slp_point
    assume "z \<in> space lborel"
    have kernel_bound:
        "cmod (slp_damped_center_kernel eps tau (z - c)) \<le> 1"
      by (rule slp_damped_center_kernel_translate_norm_le_one[OF
            eps_nonnegative])
    show "cmod
        (slp_damped_center_kernel eps tau (z - c) * f z) \<le>
      cmod (f z)"
      unfolding norm_mult
      using mult_right_mono[OF kernel_bound norm_ge_zero[of "f z"]]
      by simp
  qed
  have coefficient_nonnegative:
      "0 \<le> cmod (of_real (tau / pi) :: complex)"
    by simp
  show ?thesis
    unfolding slp_damped_center_average_def
  proof (subst norm_mult)
    show "cmod (of_real (tau / pi) :: complex) *
          cmod (integral\<^sup>L lborel
            (\<lambda>z. slp_damped_center_kernel eps tau (z - c) * f z)) \<le>
        cmod (of_real (tau / pi) :: complex) *
          integral\<^sup>L lborel (\<lambda>z. cmod (f z))"
      by (rule mult_left_mono[OF
            order_trans[OF integral_norm_bound norm_integral_le]
            coefficient_nonnegative])
  qed
qed

lemma slp_damped_center_average_l2:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes eps: "0 < eps"
    and f_integrable: "integrable lborel f"
  shows "aim_complex_lp_on_plane 2
    (slp_damped_center_average eps tau f)"
proof -
  let ?A = "slp_damped_center_average eps tau f"
  let ?M = "cmod (of_real (tau / pi) :: complex) *
    integral\<^sup>L lborel (\<lambda>z. cmod (f z))"
  have eps_nonnegative: "0 \<le> eps"
    using eps by simp
  have A_integrable: "integrable lborel ?A"
    by (rule slp_damped_center_average_integrable[OF eps f_integrable])
  have A_measurable: "?A \<in> borel_measurable lborel"
    using A_integrable by measurable
  have A_norm_integrable:
      "integrable lborel (\<lambda>c. cmod (?A c))"
    using A_integrable by simp
  have M_nonnegative: "0 \<le> ?M"
    by simp
  have majorant_integrable:
      "integrable lborel (\<lambda>c. ?M * cmod (?A c))"
    using A_norm_integrable by simp
  have A_bound: "cmod (?A c) \<le> ?M" for c
    by (rule slp_damped_center_average_norm_bound[OF
          eps_nonnegative f_integrable])
  have square_bound:
      "cmod (?A c) powr 2 \<le> ?M * cmod (?A c)" for c
  proof -
    have product_bound:
        "cmod (?A c) * cmod (?A c) \<le> ?M * cmod (?A c)"
      by (rule mult_right_mono[OF A_bound]) simp
    show ?thesis
      using product_bound
      by (simp only: powr_numeral norm_ge_zero power2_eq_square)
  qed
  have square_measurable:
      "(\<lambda>c. cmod (?A c) powr 2) \<in> borel_measurable lborel"
    using A_measurable by measurable
  have square_integrable:
      "integrable lborel (\<lambda>c. cmod (?A c) powr 2)"
  proof (rule Bochner_Integration.integrable_bound[OF
      majorant_integrable square_measurable])
    show "AE c in lborel.
        Real_Vector_Spaces.norm (cmod (?A c) powr 2) \<le>
          Real_Vector_Spaces.norm (?M * cmod (?A c))"
    proof (rule AE_I2)
      fix c
      have left_nonnegative: "0 \<le> cmod (?A c) powr 2"
        by simp
      have right_nonnegative: "0 \<le> ?M * cmod (?A c)"
        by (rule mult_nonneg_nonneg[OF M_nonnegative]) simp
      show "Real_Vector_Spaces.norm (cmod (?A c) powr 2) \<le>
          Real_Vector_Spaces.norm (?M * cmod (?A c))"
        using square_bound[of c] left_nonnegative right_nonnegative by simp
    qed
  qed
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using A_measurable square_integrable by blast
qed

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_damped_center_error_plancherel:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes eps: "0 < eps"
    and f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
  shows "integral\<^sup>L lborel
      (\<lambda>xi. cmod
        ((of_real (tau / pi) *
            slp_fourier_transform
              (slp_damped_center_kernel eps tau) xi - 1) *
          slp_fourier_transform f xi) ^ 2) =
    (2 * pi) ^ 2 * integral\<^sup>L lborel
      (\<lambda>c. cmod
        (slp_damped_center_average eps tau f c - f c) ^ 2)"
proof -
  let ?A = "slp_damped_center_average eps tau f"
  have A_integrable: "integrable lborel ?A"
    by (rule slp_damped_center_average_integrable[OF eps f_integrable])
  have A_l2: "aim_complex_lp_on_plane 2 ?A"
    by (rule slp_damped_center_average_l2[OF eps f_integrable])
  have error_integrable:
      "integrable lborel (\<lambda>c. ?A c - f c)"
    by (rule Bochner_Integration.integrable_diff[OF
          A_integrable f_integrable])
  have error_l2:
      "aim_complex_lp_on_plane 2 (\<lambda>c. ?A c - f c)"
    by (rule aim_complex_lp_on_plane_diff[OF
          zero_less_numeral A_l2 f_l2])
  have minus_f_integrable:
      "integrable lborel (\<lambda>c. - f c)"
    using f_integrable by simp
  have fourier_difference:
      "slp_fourier_transform (\<lambda>c. ?A c - f c) xi =
        slp_fourier_transform ?A xi - slp_fourier_transform f xi"
      for xi
  proof -
    have fourier_add:
        "slp_fourier_transform (\<lambda>c. ?A c + (- f c)) xi =
          slp_fourier_transform ?A xi +
            slp_fourier_transform (\<lambda>c. - f c) xi"
      by (rule slp_fourier_transform_add[OF
            A_integrable minus_f_integrable])
    have fourier_minus:
        "slp_fourier_transform (\<lambda>c. - f c) xi =
          - slp_fourier_transform f xi"
    proof -
      have "slp_fourier_transform (\<lambda>c. (-1) * f c) xi =
          (-1) * slp_fourier_transform f xi"
        by (rule slp_fourier_transform_mult[OF f_integrable])
      then show ?thesis by simp
    qed
    show ?thesis
      using fourier_add fourier_minus by simp
  qed
  have fourier_error:
      "slp_fourier_transform (\<lambda>c. ?A c - f c) xi =
        (of_real (tau / pi) *
            slp_fourier_transform
              (slp_damped_center_kernel eps tau) xi - 1) *
          slp_fourier_transform f xi"
      for xi
  proof -
    have average_transform:
        "slp_fourier_transform ?A xi =
          (of_real (tau / pi) *
            slp_fourier_transform
              (slp_damped_center_kernel eps tau) xi) *
            slp_fourier_transform f xi"
      by (rule slp_damped_center_average_fourier_transform[OF
            eps f_integrable])
    show ?thesis
      using fourier_difference[of xi] average_transform
      by (simp add: algebra_simps)
  qed
  have frequency_integral_identity:
      "integral\<^sup>L lborel
          (\<lambda>xi. cmod
            (slp_fourier_transform (\<lambda>c. ?A c - f c) xi) ^ 2) =
        integral\<^sup>L lborel
          (\<lambda>xi. cmod
            ((of_real (tau / pi) *
                slp_fourier_transform
                  (slp_damped_center_kernel eps tau) xi - 1) *
              slp_fourier_transform f xi) ^ 2)"
    by (intro Bochner_Integration.integral_cong[OF refl])
      (simp only: fourier_error)
  have dense_plancherel:
      "integral\<^sup>L lborel
          (\<lambda>xi. cmod
            (slp_fourier_transform (\<lambda>c. ?A c - f c) xi) ^ 2) =
        (2 * pi) ^ 2 * integral\<^sup>L lborel
          (\<lambda>c. cmod (?A c - f c) ^ 2)"
    by (rule slp_fourier_l1_plancherel_l1_l2[OF
          error_l2 error_integrable])
  show ?thesis
    using frequency_integral_identity dense_plancherel by simp
qed

end

end
