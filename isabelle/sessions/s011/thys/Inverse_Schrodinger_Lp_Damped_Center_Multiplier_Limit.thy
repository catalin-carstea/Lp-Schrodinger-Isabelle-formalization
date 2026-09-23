theory Inverse_Schrodinger_Lp_Damped_Center_Multiplier_Limit
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Damped_Center_Fourier_Closed"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Center_Multiplier_L2"
begin

section \<open>Removal of the Gaussian damping at the multiplier level\<close>

lemma slp_damped_center_real_coefficient_tendsto:
  assumes tau: "0 < tau"
  shows "((\<lambda>eps :: real.
      (tau / pi) *
        (pi * exp (- eps *
          ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) /
          (4 * (eps ^ 2 + tau ^ 2))) /
          sqrt (eps ^ 2 + tau ^ 2))) \<longlongrightarrow> 1) (at_right 0)"
proof -
  have raw_limit:
      "((\<lambda>eps :: real.
        (tau / pi) *
          (pi * exp (- eps *
            ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) /
            (4 * (eps ^ 2 + tau ^ 2))) /
            sqrt (eps ^ 2 + tau ^ 2))) \<longlongrightarrow>
        (tau / pi) *
          (pi * exp (- 0 *
            ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) /
            (4 * (0 ^ 2 + tau ^ 2))) /
            sqrt (0 ^ 2 + tau ^ 2))) (at_right 0)"
    using tau
    by (intro tendsto_intros) simp_all
  have limit_value:
      "(tau / pi) *
          (pi * exp (- 0 *
            ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) /
            (4 * (0 ^ 2 + tau ^ 2))) /
            sqrt (0 ^ 2 + tau ^ 2)) = 1"
    using tau by simp
  show ?thesis
    using raw_limit by (simp only: limit_value)
qed

lemma slp_damped_center_phase_argument_tendsto:
  assumes tau: "0 < tau"
  shows "((\<lambda>eps :: real.
      - (tau * slp_center_phase 0 xi /
        (4 * (eps ^ 2 + tau ^ 2)))) \<longlongrightarrow>
      - (slp_center_phase 0 xi / (4 * tau))) (at_right 0)"
proof -
  have raw_limit:
      "((\<lambda>eps :: real.
        - (tau * slp_center_phase 0 xi /
          (4 * (eps ^ 2 + tau ^ 2)))) \<longlongrightarrow>
        - (tau * slp_center_phase 0 xi /
          (4 * (0 ^ 2 + tau ^ 2)))) (at_right 0)"
    using tau
    by (intro tendsto_intros) simp_all
  have limit_value:
      "- (tau * slp_center_phase 0 xi /
          (4 * (0 ^ 2 + tau ^ 2))) =
        - (slp_center_phase 0 xi / (4 * tau))"
    using tau by (simp add: power2_eq_square)
  show ?thesis
    using raw_limit by (simp only: limit_value)
qed

theorem slp_damped_center_fourier_multiplier_tendsto:
  assumes tau: "0 < tau"
  shows "((\<lambda>eps :: real.
      of_real (tau / pi) *
        slp_fourier_transform
          (slp_damped_center_kernel eps tau) xi) \<longlongrightarrow>
      slp_center_fourier_multiplier tau xi) (at_right 0)"
proof -
  let ?C = "\<lambda>eps :: real.
    (tau / pi) *
      (pi * exp (- eps *
        ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) /
        (4 * (eps ^ 2 + tau ^ 2))) /
        sqrt (eps ^ 2 + tau ^ 2))"
  let ?phase_arg = "\<lambda>eps :: real.
    - (tau * slp_center_phase 0 xi /
      (4 * (eps ^ 2 + tau ^ 2)))"
  let ?phase_zero = "- (slp_center_phase 0 xi / (4 * tau))"
  have coefficient_real: "(?C \<longlongrightarrow> 1) (at_right 0)"
    by (rule slp_damped_center_real_coefficient_tendsto[OF tau])
  have coefficient_complex:
      "((\<lambda>eps. (of_real (?C eps) :: complex)) \<longlongrightarrow>
        of_real 1) (at_right 0)"
    by (rule tendsto_of_real_iff[where 'a=complex, THEN iffD2])
      (rule coefficient_real)
  have phase_real: "(?phase_arg \<longlongrightarrow> ?phase_zero) (at_right 0)"
    by (rule slp_damped_center_phase_argument_tendsto[OF tau])
  have phase_complex:
      "((\<lambda>eps. (of_real (?phase_arg eps) :: complex)) \<longlongrightarrow>
        of_real ?phase_zero) (at_right 0)"
    by (rule tendsto_of_real_iff[where 'a=complex, THEN iffD2])
      (rule phase_real)
  have imaginary_phase:
      "((\<lambda>eps. \<i> * of_real (?phase_arg eps)) \<longlongrightarrow>
        \<i> * of_real ?phase_zero) (at_right 0)"
    by (rule tendsto_mult[OF tendsto_const phase_complex])
  have exponential_phase:
      "((\<lambda>eps. exp (\<i> * of_real (?phase_arg eps))) \<longlongrightarrow>
        exp (\<i> * of_real ?phase_zero)) (at_right 0)"
    by (rule tendsto_exp[OF imaginary_phase])
  have closed_limit:
      "((\<lambda>eps. of_real (?C eps) *
          exp (\<i> * of_real (?phase_arg eps))) \<longlongrightarrow>
        of_real 1 * exp (\<i> * of_real ?phase_zero)) (at_right 0)"
    by (rule tendsto_mult[OF coefficient_complex exponential_phase])
  have eps_positive:
      "\<forall>\<^sub>F eps :: real in at_right 0. 0 < eps"
    by (rule eventually_at_rightI[where b=1]) simp_all
  have eventual_identity:
      "\<forall>\<^sub>F eps :: real in at_right 0.
        of_real (tau / pi) *
            slp_fourier_transform
              (slp_damped_center_kernel eps tau) xi =
          of_real (?C eps) * exp (\<i> * of_real (?phase_arg eps))"
  proof (rule eventually_mono[OF eps_positive])
    fix eps :: real
    assume eps: "0 < eps"
    show "of_real (tau / pi) *
            slp_fourier_transform
              (slp_damped_center_kernel eps tau) xi =
          of_real (?C eps) * exp (\<i> * of_real (?phase_arg eps))"
      by (simp only:
          slp_damped_center_fourier_transform_closed[OF eps]
          of_real_mult mult.assoc)
  qed
  have physical_limit:
      "((\<lambda>eps :: real.
        of_real (tau / pi) *
          slp_fourier_transform
            (slp_damped_center_kernel eps tau) xi) \<longlongrightarrow>
        of_real 1 * exp (\<i> * of_real ?phase_zero)) (at_right 0)"
    using closed_limit
    by (rule tendsto_cong[OF eventual_identity, THEN iffD2])
  show ?thesis
    unfolding slp_center_fourier_multiplier_def
    using physical_limit by simp
qed

end
