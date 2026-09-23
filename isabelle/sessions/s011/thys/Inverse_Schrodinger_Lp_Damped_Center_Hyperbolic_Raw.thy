theory Inverse_Schrodinger_Lp_Damped_Center_Hyperbolic_Raw
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Damped_Center_Hyperbolic_Fubini"
begin

section \<open>The raw closed damped hyperbolic transform\<close>

lemma slp_damped_center_fourier_transform_hyperbolic_raw:
  assumes eps: "0 < eps"
  shows "slp_fourier_transform
      (slp_damped_center_kernel eps tau) xi =
    (1 / 2) *\<^sub>R
      ((of_real
        (sqrt (2 * pi) *
          exp (- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
            (2 * (eps ^ 2 + tau ^ 2))))) /\<^sub>R sqrt eps) *
      (exp (\<i> * of_real
        (- slp_hyperbolic_freq_minus xi *
          slp_hyperbolic_second_center eps tau xi)) *
        (of_real
          (sqrt (2 * pi) *
            exp (- ((slp_hyperbolic_freq_minus xi /
              sqrt (slp_hyperbolic_second_scale eps tau)) ^ 2) / 2)) /\<^sub>R
          sqrt (slp_hyperbolic_second_scale eps tau))))"
  using slp_damped_center_fourier_transform_hyperbolic_fubini[OF eps]
    slp_hyperbolic_post_first_integral[OF eps]
  by simp

end
