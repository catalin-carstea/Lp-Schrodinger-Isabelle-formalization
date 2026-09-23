theory Inverse_Schrodinger_Lp_Fourier_Hyperbolic_Iterated_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Hyperbolic_Second_Fiber"
begin

section \<open>The exact iterated hyperbolic integral\<close>

lemma slp_hyperbolic_post_first_integrable:
  assumes eps: "0 < eps"
  shows "integrable lborel (slp_hyperbolic_post_first eps tau xi)"
proof -
  let ?coefficient =
    "of_real
      (sqrt (2 * pi) *
        exp (- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
          (2 * (eps ^ 2 + tau ^ 2))))) /\<^sub>R sqrt eps"
  have fiber_integrable:
      "integrable lborel (slp_hyperbolic_second_fiber eps tau xi)"
    by (rule slp_hyperbolic_second_fiber_integrable[OF eps])
  have factorization:
      "slp_hyperbolic_post_first eps tau xi =
        (\<lambda>v. ?coefficient *
          slp_hyperbolic_second_fiber eps tau xi v)"
    by (rule ext, rule slp_hyperbolic_post_first_factor[OF eps])
  show ?thesis
    unfolding factorization
    by (rule Bochner_Integration.integrable_mult_right)
      (simp only: fiber_integrable)
qed

lemma slp_hyperbolic_post_first_integral:
  assumes eps: "0 < eps"
  shows "integral\<^sup>L lborel (slp_hyperbolic_post_first eps tau xi) =
    (of_real
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
        sqrt (slp_hyperbolic_second_scale eps tau)))"
proof -
  let ?coefficient =
    "of_real
      (sqrt (2 * pi) *
        exp (- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
          (2 * (eps ^ 2 + tau ^ 2))))) /\<^sub>R sqrt eps"
  have fiber_integrable:
      "integrable lborel (slp_hyperbolic_second_fiber eps tau xi)"
    by (rule slp_hyperbolic_second_fiber_integrable[OF eps])
  have factorization:
      "slp_hyperbolic_post_first eps tau xi =
        (\<lambda>v. ?coefficient *
          slp_hyperbolic_second_fiber eps tau xi v)"
    by (rule ext, rule slp_hyperbolic_post_first_factor[OF eps])
  have integral_extraction:
      "integral\<^sup>L lborel
          (\<lambda>v. ?coefficient *
            slp_hyperbolic_second_fiber eps tau xi v) =
        ?coefficient *
          integral\<^sup>L lborel
            (slp_hyperbolic_second_fiber eps tau xi)"
    by (rule Bochner_Integration.integral_mult_right)
      (simp only: fiber_integrable)
  show ?thesis
    unfolding factorization
    using integral_extraction slp_hyperbolic_second_fiber_integral[OF eps]
    by simp
qed

end
