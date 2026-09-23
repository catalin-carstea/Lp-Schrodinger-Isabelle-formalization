theory Inverse_Schrodinger_Lp_Damped_Center_Average_Fourier
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Fourier_L2_Dense_Plancherel"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Complex_Convolution"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Damped_Center_Average_Limit"
begin

section \<open>The damped physical center average as an L1 convolution\<close>

lemma slp_damped_center_average_convolution:
  fixes f :: "slp_point \<Rightarrow> complex"
  shows "slp_damped_center_average eps tau f c =
    of_real (tau / pi) *
      slp_complex_convolution f (slp_damped_center_kernel eps tau) c"
proof -
  have kernel_even:
      "slp_damped_center_kernel eps tau (- x) =
        slp_damped_center_kernel eps tau x"
      for x :: slp_point
    unfolding slp_damped_center_kernel_factor
    by simp
  have kernel_difference:
      "slp_damped_center_kernel eps tau (z - c) =
        slp_damped_center_kernel eps tau (c - z)"
      for z c :: slp_point
  proof -
    have "z - c = - (c - z)"
      by simp
    then show ?thesis
      by (simp only: kernel_even)
  qed
  show ?thesis
    unfolding slp_damped_center_average_def slp_complex_convolution_def
    by (simp only: kernel_difference mult.commute)
qed

lemma slp_damped_center_average_integrable:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes eps: "0 < eps"
    and f_integrable: "integrable lborel f"
  shows "integrable lborel (slp_damped_center_average eps tau f)"
proof -
  have kernel_integrable:
      "integrable lborel (slp_damped_center_kernel eps tau)"
    by (rule slp_damped_center_kernel_integrable[OF eps])
  have convolution_integrable:
      "integrable lborel
        (slp_complex_convolution f (slp_damped_center_kernel eps tau))"
    by (rule slp_complex_convolution_integrable[OF
          f_integrable kernel_integrable])
  have scaled_integrable:
      "integrable lborel
        (\<lambda>c. of_real (tau / pi) *
          slp_complex_convolution f
            (slp_damped_center_kernel eps tau) c)"
    by (rule Bochner_Integration.integrable_mult_right)
      (rule convolution_integrable)
  have average_identity:
      "slp_damped_center_average eps tau f =
        (\<lambda>c. of_real (tau / pi) *
          slp_complex_convolution f
            (slp_damped_center_kernel eps tau) c)"
    by (rule ext) (rule slp_damped_center_average_convolution)
  show ?thesis
    by (simp only: average_identity scaled_integrable)
qed

theorem slp_damped_center_average_fourier_transform:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes eps: "0 < eps"
    and f_integrable: "integrable lborel f"
  shows "slp_fourier_transform
      (slp_damped_center_average eps tau f) xi =
    (of_real (tau / pi) *
      slp_fourier_transform (slp_damped_center_kernel eps tau) xi) *
      slp_fourier_transform f xi"
proof -
  have kernel_integrable:
      "integrable lborel (slp_damped_center_kernel eps tau)"
    by (rule slp_damped_center_kernel_integrable[OF eps])
  have convolution_integrable:
      "integrable lborel
        (slp_complex_convolution f (slp_damped_center_kernel eps tau))"
    by (rule slp_complex_convolution_integrable[OF
          f_integrable kernel_integrable])
  have average_identity:
      "slp_damped_center_average eps tau f =
        (\<lambda>c. of_real (tau / pi) *
          slp_complex_convolution f
            (slp_damped_center_kernel eps tau) c)"
    by (rule ext) (rule slp_damped_center_average_convolution)
  have "slp_fourier_transform
      (slp_damped_center_average eps tau f) xi =
      slp_fourier_transform
        (\<lambda>c. of_real (tau / pi) *
          slp_complex_convolution f
            (slp_damped_center_kernel eps tau) c) xi"
    by (simp only: average_identity)
  also have "... = of_real (tau / pi) *
      slp_fourier_transform
        (slp_complex_convolution f
          (slp_damped_center_kernel eps tau)) xi"
    by (rule slp_fourier_transform_mult[OF convolution_integrable])
  also have "... = of_real (tau / pi) *
      (slp_fourier_transform f xi *
        slp_fourier_transform (slp_damped_center_kernel eps tau) xi)"
    by (simp only: slp_fourier_transform_complex_convolution[OF
          f_integrable kernel_integrable])
  also have "... =
      (of_real (tau / pi) *
        slp_fourier_transform (slp_damped_center_kernel eps tau) xi) *
        slp_fourier_transform f xi"
    by (simp only: mult_ac)
  finally show ?thesis .
qed

end
