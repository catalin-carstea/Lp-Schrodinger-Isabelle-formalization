theory Inverse_Schrodinger_Lp_Quadratic_Phase_Multipliers
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_H1_Zero_Target_Limit"
begin

section \<open>Individual quadratic phase multipliers\<close>

definition slp_holomorphic_quadratic_phase_multiplier ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_holomorphic_quadratic_phase_multiplier tau c z =
    exp (\<i> * of_real (tau / 2) *
      (slp_point_as_complex (z - c)) ^ 2)"

definition slp_antiholomorphic_quadratic_phase_multiplier ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_antiholomorphic_quadratic_phase_multiplier tau c z =
    exp (\<i> * of_real (tau / 2) *
      cnj ((slp_point_as_complex (z - c)) ^ 2))"

lemma slp_quadratic_phase_multipliers_product:
  "slp_holomorphic_quadratic_phase_multiplier tau c z *
      slp_antiholomorphic_quadratic_phase_multiplier tau c z =
    slp_center_kernel tau c z"
proof -
  have phase:
      "slp_center_phase c z =
        Re ((slp_point_as_complex (z - c)) ^ 2)"
    unfolding slp_center_phase_def slp_point_as_complex_def
    by (simp only: Re_power2 complex.sel vector_minus_component)
  have square_sum:
      "(slp_point_as_complex (z - c)) ^ 2 +
          cnj ((slp_point_as_complex (z - c)) ^ 2) =
        of_real (2 * slp_center_phase c z)"
    using phase
    by (simp only: complex_add_cnj)
  have scalar_product:
      "(tau / 2) * (2 * slp_center_phase c z) =
        tau * slp_center_phase c z"
    by (simp add: divide_simps algebra_simps)
  have exponent_sum:
      "\<i> * of_real (tau / 2) *
          (slp_point_as_complex (z - c)) ^ 2 +
        \<i> * of_real (tau / 2) *
          cnj ((slp_point_as_complex (z - c)) ^ 2) =
        \<i> * of_real (tau * slp_center_phase c z)"
  proof -
    have
      "\<i> * of_real (tau / 2) *
          (slp_point_as_complex (z - c)) ^ 2 +
        \<i> * of_real (tau / 2) *
          cnj ((slp_point_as_complex (z - c)) ^ 2) =
        \<i> * of_real (tau / 2) *
          ((slp_point_as_complex (z - c)) ^ 2 +
            cnj ((slp_point_as_complex (z - c)) ^ 2))"
      by (simp only: distrib_left)
    also have "... =
        \<i> * of_real (tau / 2) *
          of_real (2 * slp_center_phase c z)"
      by (simp only: square_sum)
    also have "... =
        \<i> * of_real
          ((tau / 2) * (2 * slp_center_phase c z))"
      by (simp only: of_real_mult mult.assoc)
    also have "... =
        \<i> * of_real (tau * slp_center_phase c z)"
      by (simp only: scalar_product)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding slp_holomorphic_quadratic_phase_multiplier_def
      slp_antiholomorphic_quadratic_phase_multiplier_def
      slp_center_kernel_def
    by (simp only: exp_add[symmetric] exponent_sum)
qed

end
