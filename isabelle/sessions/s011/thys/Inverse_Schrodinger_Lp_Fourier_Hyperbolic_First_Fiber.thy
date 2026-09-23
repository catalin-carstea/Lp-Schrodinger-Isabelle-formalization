theory Inverse_Schrodinger_Lp_Fourier_Hyperbolic_First_Fiber
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Hyperbolic_Mix"
begin

section \<open>The first real-Gaussian fiber in hyperbolic coordinates\<close>

definition slp_hyperbolic_freq_plus :: "slp_point \<Rightarrow> real"
where
  "slp_hyperbolic_freq_plus xi = (xi $ 0 + xi $ 1) / 2"

definition slp_hyperbolic_freq_minus :: "slp_point \<Rightarrow> real"
where
  "slp_hyperbolic_freq_minus xi = (xi $ 0 - xi $ 1) / 2"

definition slp_hyperbolic_first_fiber ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex"
where
  "slp_hyperbolic_first_fiber eps tau xi v u =
    exp (\<i> * of_real
      (- (slp_hyperbolic_freq_plus xi - tau * v) * u)) *
    slp_scaled_gaussian eps u"

definition slp_hyperbolic_outer_factor ::
  "real \<Rightarrow> slp_point \<Rightarrow> real \<Rightarrow> complex"
where
  "slp_hyperbolic_outer_factor eps xi v =
    exp (\<i> * of_real (- slp_hyperbolic_freq_minus xi * v)) *
    slp_scaled_gaussian eps v"

lemma slp_hyperbolic_pulled_integrand_factor:
  "slp_fourier_phase xi (slp_hyperbolic_mix u) *
      slp_damped_center_kernel eps tau (slp_hyperbolic_mix u) =
    slp_hyperbolic_first_fiber eps tau xi (u $ 1) (u $ 0) *
      slp_hyperbolic_outer_factor eps xi (u $ 1)"
proof -
  have chirp:
      "((slp_hyperbolic_mix u) $ (0 :: 2)) ^ 2 -
          ((slp_hyperbolic_mix u) $ (1 :: 2)) ^ 2 =
        (u $ 0) * (u $ 1)"
    using slp_hyperbolic_mix_center_phase[of u]
    by (simp add: slp_center_phase_def zero_vec_def)
  have gaussian_exponent:
      "- eps * (((u $ 0) ^ 2 + (u $ 1) ^ 2) / 2) =
        (- eps * (u $ 0) ^ 2 / 2) +
          (- eps * (u $ 1) ^ 2 / 2)"
    by (simp add: divide_simps algebra_simps)
  have gaussian:
      "of_real
          (exp (- eps *
            (Real_Vector_Spaces.norm (slp_hyperbolic_mix u)) ^ 2)) =
        slp_scaled_gaussian eps (u $ 0) *
          slp_scaled_gaussian eps (u $ 1)"
    unfolding slp_hyperbolic_mix_norm_square gaussian_exponent
      slp_scaled_gaussian_def
    by (simp only: exp_add of_real_mult)
  have real_phase:
      "- inner (slp_hyperbolic_mix u) xi +
          tau * (((slp_hyperbolic_mix u) $ (0 :: 2)) ^ 2 -
            ((slp_hyperbolic_mix u) $ (1 :: 2)) ^ 2) =
        - (slp_hyperbolic_freq_plus xi - tau * (u $ 1)) *
            (u $ 0) +
          - slp_hyperbolic_freq_minus xi * (u $ 1)"
    unfolding slp_hyperbolic_mix_inner chirp
      slp_hyperbolic_freq_plus_def slp_hyperbolic_freq_minus_def
    by (simp add: divide_simps algebra_simps)
  have lifted_phase:
      "of_real
          (- inner (slp_hyperbolic_mix u) xi +
            tau * (((slp_hyperbolic_mix u) $ (0 :: 2)) ^ 2 -
              ((slp_hyperbolic_mix u) $ (1 :: 2)) ^ 2)) =
        of_real
          (- (slp_hyperbolic_freq_plus xi - tau * (u $ 1)) *
              (u $ 0) +
            - slp_hyperbolic_freq_minus xi * (u $ 1))"
    by (rule arg_cong[OF real_phase])
  have scaled_phase:
      "\<i> * of_real
          (- inner (slp_hyperbolic_mix u) xi +
            tau * (((slp_hyperbolic_mix u) $ (0 :: 2)) ^ 2 -
              ((slp_hyperbolic_mix u) $ (1 :: 2)) ^ 2)) =
        \<i> * of_real
          (- (slp_hyperbolic_freq_plus xi - tau * (u $ 1)) *
              (u $ 0) +
            - slp_hyperbolic_freq_minus xi * (u $ 1))"
    by (rule arg_cong[OF lifted_phase,
          where f="\<lambda>z::complex. \<i> * z"])
  have complex_phase:
      "\<i> * of_real (- inner (slp_hyperbolic_mix u) xi) +
          \<i> * of_real
            (tau * (((slp_hyperbolic_mix u) $ (0 :: 2)) ^ 2 -
              ((slp_hyperbolic_mix u) $ (1 :: 2)) ^ 2)) =
        \<i> * of_real
            (- (slp_hyperbolic_freq_plus xi - tau * (u $ 1)) *
              (u $ 0)) +
          \<i> * of_real
            (- slp_hyperbolic_freq_minus xi * (u $ 1))"
    using scaled_phase
    by (simp only: of_real_add distrib_left)
  have phase:
      "exp (\<i> * of_real (- inner (slp_hyperbolic_mix u) xi)) *
          exp (\<i> * of_real
            (tau * (((slp_hyperbolic_mix u) $ (0 :: 2)) ^ 2 -
              ((slp_hyperbolic_mix u) $ (1 :: 2)) ^ 2))) =
        exp (\<i> * of_real
            (- (slp_hyperbolic_freq_plus xi - tau * (u $ 1)) *
              (u $ 0))) *
          exp (\<i> * of_real
            (- slp_hyperbolic_freq_minus xi * (u $ 1)))"
    by (simp only: exp_add[symmetric] complex_phase)
  show ?thesis
    unfolding slp_fourier_phase_def slp_damped_center_kernel_factor
      slp_hyperbolic_first_fiber_def slp_hyperbolic_outer_factor_def
    using gaussian phase
    by (simp only: mult_ac)
qed

lemma slp_hyperbolic_first_fiber_measurable:
  "slp_hyperbolic_first_fiber eps tau xi v \<in>
    borel_measurable lborel"
  unfolding slp_hyperbolic_first_fiber_def by measurable

declare slp_hyperbolic_first_fiber_measurable[measurable]

lemma slp_hyperbolic_first_fiber_integrable:
  assumes eps: "0 < eps"
  shows "integrable lborel
    (slp_hyperbolic_first_fiber eps tau xi v)"
  unfolding slp_hyperbolic_first_fiber_def
  by (rule slp_scaled_gaussian_fourier_integrable[OF eps])

lemma slp_hyperbolic_first_fiber_integral:
  assumes eps: "0 < eps"
  shows "integral\<^sup>L lborel
      (slp_hyperbolic_first_fiber eps tau xi v) =
    of_real
      (sqrt (2 * pi) *
        exp (- (((slp_hyperbolic_freq_plus xi - tau * v) /
          sqrt eps) ^ 2) / 2)) /\<^sub>R sqrt eps"
  unfolding slp_hyperbolic_first_fiber_def
  by (rule slp_scaled_gaussian_fourier_integral[OF eps])

end
