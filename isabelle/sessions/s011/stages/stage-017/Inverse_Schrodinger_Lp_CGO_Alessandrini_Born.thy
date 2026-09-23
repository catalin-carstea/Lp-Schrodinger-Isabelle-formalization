theory Inverse_Schrodinger_Lp_CGO_Alessandrini_Born
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Weak_Solution"
    "Paper_Inverse_Schrodinger_Lp_Alessandrini_Statement_V2.Inverse_Schrodinger_Lp_Alessandrini_Statement_v2"
begin

section \<open>Literal CGO product decomposition\<close>

lemma slp_left_right_cgo_product_born_decomposition:
  "slp_left_cgo_field tau c W_left z *
      slp_right_cgo_field tau c W_right z =
    slp_center_kernel tau c z + W_left z + W_right z +
      slp_center_kernel (- tau) c z * W_left z * W_right z"
proof -
  have left_factorized:
      "slp_left_cgo_field tau c W_left z =
        slp_holomorphic_quadratic_phase_multiplier tau c z *
          (1 + slp_center_kernel (- tau) c z * W_left z)"
    using slp_cgo_fields_factorized by blast
  have right_factorized:
      "slp_right_cgo_field tau c W_right z =
        slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          (1 + slp_center_kernel (- tau) c z * W_right z)"
    using slp_cgo_fields_factorized by blast
  have leading_phase:
      "slp_holomorphic_quadratic_phase_multiplier tau c z *
          slp_antiholomorphic_quadratic_phase_multiplier tau c z =
        slp_center_kernel tau c z"
    by (rule slp_quadratic_phase_multipliers_product)
  have leading_phase_reversed:
      "slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          slp_holomorphic_quadratic_phase_multiplier tau c z =
        slp_center_kernel tau c z"
    by (rule trans[OF mult.commute leading_phase])
  have single_phase_cancel:
      "slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          (slp_holomorphic_quadratic_phase_multiplier tau c z *
            slp_center_kernel (- tau) c z) = 1"
    by (simp only: mult.assoc[symmetric] leading_phase_reversed
          slp_center_kernel_product_opposite)
  have double_phase_cancel:
      "slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          (slp_holomorphic_quadratic_phase_multiplier tau c z *
            (slp_center_kernel (- tau) c z *
              slp_center_kernel (- tau) c z)) =
        slp_center_kernel (- tau) c z"
    by (simp only: mult.assoc[symmetric] leading_phase_reversed
          slp_center_kernel_product_opposite mult.left_neutral)
  show ?thesis
    unfolding left_factorized right_factorized
    by (simp add: leading_phase leading_phase_reversed single_phase_cancel
          double_phase_cancel algebra_simps)
qed

section \<open>Frozen universal orthogonality on a literal CGO pair\<close>

theorem slp_alessandrini_literal_cgo_born_identity:
  fixes Omega :: "slp_point set"
    and V V_tilde W_left W_right :: slp_scalar_field
    and D_left D_right :: slp_gradient_field
    and tau :: real
    and c :: slp_point
  assumes orthogonality:
      "slp_alessandrini_orthogonality Omega V V_tilde"
    and left_solution:
      "slp_weak_solution Omega V
        (slp_left_cgo_field tau c W_left, D_left)"
    and right_solution:
      "slp_weak_solution Omega V_tilde
        (slp_right_cgo_field tau c W_right, D_right)"
  shows
    "set_integrable lborel Omega
        (\<lambda>x. (V x - V_tilde x) *
          (slp_center_kernel tau c x + W_left x + W_right x +
            slp_center_kernel (- tau) c x * W_left x * W_right x))
      \<and>
      set_lebesgue_integral lborel Omega
        (\<lambda>x. (V x - V_tilde x) *
          (slp_center_kernel tau c x + W_left x + W_right x +
            slp_center_kernel (- tau) c x * W_left x * W_right x)) = 0"
proof -
  let ?F = "(slp_left_cgo_field tau c W_left, D_left)"
  let ?G = "(slp_right_cgo_field tau c W_right, D_right)"
  have raw_identity:
      "set_integrable lborel Omega
          (\<lambda>x. (V x - V_tilde x) * fst ?F x * fst ?G x)
        \<and>
        set_lebesgue_integral lborel Omega
          (\<lambda>x. (V x - V_tilde x) * fst ?F x * fst ?G x) = 0"
    using orthogonality left_solution right_solution
    unfolding slp_alessandrini_orthogonality_def by blast
  have integrand_presentation:
      "(\<lambda>x. (V x - V_tilde x) * fst ?F x * fst ?G x) =
        (\<lambda>x. (V x - V_tilde x) *
          (slp_center_kernel tau c x + W_left x + W_right x +
            slp_center_kernel (- tau) c x * W_left x * W_right x))"
  proof (rule ext)
    fix x
    show "(V x - V_tilde x) * fst ?F x * fst ?G x =
        (V x - V_tilde x) *
          (slp_center_kernel tau c x + W_left x + W_right x +
            slp_center_kernel (- tau) c x * W_left x * W_right x)"
      by (simp only: fst_conv mult.assoc
            slp_left_right_cgo_product_born_decomposition)
  qed
  show ?thesis
    using raw_identity unfolding integrand_presentation .
qed

end
