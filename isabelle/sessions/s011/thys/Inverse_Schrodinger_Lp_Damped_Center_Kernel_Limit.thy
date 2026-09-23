theory Inverse_Schrodinger_Lp_Damped_Center_Kernel_Limit
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Damped_Center_Multiplier_Limit"
begin

section \<open>Pointwise removal of damping from the translated center kernel\<close>

lemma slp_damped_center_kernel_translate_norm_le_one:
  assumes eps: "0 \<le> eps"
  shows "cmod (slp_damped_center_kernel eps tau (z - c)) \<le> 1"
  unfolding slp_damped_center_kernel_norm
  using eps by simp

lemma slp_damped_center_kernel_translate_tendsto:
  "((\<lambda>eps :: real. slp_damped_center_kernel eps tau (z - c))
      \<longlongrightarrow> slp_center_kernel tau c z) (at_right 0)"
proof -
  have phase_identity:
      "((z - c) $ (0 :: 2)) ^ 2 - ((z - c) $ (1 :: 2)) ^ 2 =
        slp_center_phase c z"
    unfolding slp_center_phase_def by simp
  have raw_limit:
      "((\<lambda>eps :: real.
        of_real
          (exp (- eps * (Real_Vector_Spaces.norm (z - c)) ^ 2)) *
        exp (\<i> * of_real (tau * slp_center_phase c z))) \<longlongrightarrow>
        of_real
          (exp (- 0 * (Real_Vector_Spaces.norm (z - c)) ^ 2)) *
        exp (\<i> * of_real (tau * slp_center_phase c z))) (at_right 0)"
    by (intro tendsto_intros)
  have target_limit:
      "((\<lambda>eps :: real.
        of_real
          (exp (- eps * (Real_Vector_Spaces.norm (z - c)) ^ 2)) *
        exp (\<i> * of_real (tau * slp_center_phase c z))) \<longlongrightarrow>
        slp_center_kernel tau c z) (at_right 0)"
    unfolding slp_center_kernel_def
    using raw_limit by simp
  have eventual_identity:
      "\<forall>\<^sub>F eps :: real in at_right 0.
        slp_damped_center_kernel eps tau (z - c) =
          of_real
            (exp (- eps * (Real_Vector_Spaces.norm (z - c)) ^ 2)) *
          exp (\<i> * of_real (tau * slp_center_phase c z))"
    by (rule always_eventually)
      (intro allI, simp only:
        slp_damped_center_kernel_factor phase_identity)
  from target_limit show ?thesis
    by (rule tendsto_cong[OF eventual_identity, THEN iffD2])
qed

end
