theory Inverse_Schrodinger_Lp_Center_Kernel_Derivative
  imports Inverse_Schrodinger_Lp_Center_Phase_Derivative
begin

section \<open>Differential identities for the oscillatory center kernel\<close>

definition slp_center_kernel_derivative ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> complex"
where
  "slp_center_kernel_derivative tau c z h =
    slp_center_kernel tau c z *
      (\<i> * of_real (tau * slp_center_phase_derivative c z h))"

definition slp_center_kernel_partial ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_center_kernel_partial tau c z =
    slp_complex_wirtinger_partial
      (slp_center_kernel_derivative tau c z)"

lemma slp_center_kernel_has_derivative:
  "((slp_center_kernel tau c) has_derivative
      slp_center_kernel_derivative tau c z) (at z)"
proof -
  have inner:
    "((\<lambda>w. \<i> * of_real (tau * slp_center_phase c w))
      has_derivative
        (\<lambda>h. \<i> * of_real
          (tau * slp_center_phase_derivative c z h))) (at z)"
    using slp_center_phase_has_derivative[of c z]
    by (auto intro!: derivative_eq_intros)
  have exp_at:
    "(exp has_derivative
      (\<lambda>h. exp
        (\<i> * of_real (tau * slp_center_phase c z)) * h))
      (at (\<i> * of_real (tau * slp_center_phase c z)))"
    by (rule DERIV_exp[unfolded has_field_derivative_def])
  have exponential:
    "((\<lambda>w. exp (\<i> * of_real (tau * slp_center_phase c w)))
      has_derivative
        (\<lambda>h. exp (\<i> * of_real (tau * slp_center_phase c z)) *
          (\<i> * of_real
            (tau * slp_center_phase_derivative c z h)))) (at z)"
    by (rule has_derivative_compose[OF inner exp_at])
  show ?thesis
    unfolding slp_center_kernel_def slp_center_kernel_derivative_def
    by (rule exponential)
qed

lemma slp_center_kernel_derivative_first_axis [simp]:
  "slp_center_kernel_derivative tau c z (axis (0 :: 2) 1) =
    slp_center_kernel tau c z *
      (\<i> * of_real
        (tau * (2 * (z $ (0 :: 2) - c $ (0 :: 2)))))"
  unfolding slp_center_kernel_derivative_def by simp

lemma slp_center_kernel_derivative_second_axis [simp]:
  "slp_center_kernel_derivative tau c z (axis (1 :: 2) 1) =
    slp_center_kernel tau c z *
      (\<i> * of_real
        (tau * (- 2 * (z $ (1 :: 2) - c $ (1 :: 2)))))"
  unfolding slp_center_kernel_derivative_def by simp

lemma slp_complex_wirtinger_partial_real_multiplier:
  "slp_complex_wirtinger_partial (\<lambda>h. k * of_real (D h)) =
    k * slp_real_wirtinger_partial D"
  unfolding slp_complex_wirtinger_partial_def
    slp_real_wirtinger_partial_def
  by (simp add: algebra_simps)

lemma slp_center_kernel_partial_eq:
  "slp_center_kernel_partial tau c z =
    \<i> * of_real tau * slp_point_as_complex (z - c) *
      slp_center_kernel tau c z"
proof -
  have derivative_form:
    "slp_center_kernel_derivative tau c z =
      (\<lambda>h. (slp_center_kernel tau c z * (\<i> * of_real tau)) *
        of_real (slp_center_phase_derivative c z h))"
    by (rule ext)
      (simp add: slp_center_kernel_derivative_def of_real_mult
        algebra_simps)
  show ?thesis
    unfolding slp_center_kernel_partial_def derivative_form
    unfolding slp_complex_wirtinger_partial_real_multiplier
    unfolding slp_center_phase_partial_def[symmetric]
    unfolding slp_center_phase_partial_eq_difference
    by (simp add: algebra_simps)
qed

end
