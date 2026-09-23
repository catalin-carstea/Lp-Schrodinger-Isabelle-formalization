theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Quadratic_Form
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Oscillatory_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Residual_Matrix_QRL"
begin

section \<open>Affine-quadratic form of the active mixed residual\<close>

definition slp_mixed_center_finite_active_hessian ::
    "real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
      \<times> bool)^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)"
where
  "slp_mixed_center_finite_active_hessian =
    slp_signed_active_hessian
      (slp_mixed_combined_sign ::
        (unit + (unit + ((('i + 'i) + unit) + ('j + 'j)))) \<Rightarrow> real)"

definition slp_mixed_center_finite_active_linear ::
    "slp_point \<Rightarrow>
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool)"
where
  "slp_mixed_center_finite_active_linear center =
    slp_signed_passive_coefficient
      (slp_mixed_combined_sign ::
        (unit + (unit + ((('i + 'i) + unit) + ('j + 'j)))) \<Rightarrow> real)
      (slp_complex_coordinate_pack (slp_point_as_complex center))"

definition slp_mixed_center_finite_active_constant ::
    "'i::finite itself \<Rightarrow> 'j::finite itself \<Rightarrow>
      slp_point \<Rightarrow> real"
where
  "slp_mixed_center_finite_active_constant TYPE('i) TYPE('j) center =
    slp_signed_passive_constant
      (slp_mixed_combined_sign ::
        (unit + (unit + ((('i::finite + 'i) + unit) +
          ('j::finite + 'j)))) \<Rightarrow> real)
      (slp_complex_coordinate_pack (slp_point_as_complex center))"

theorem slp_mixed_center_finite_active_residual_quadratic_form:
  fixes x ::
    "real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
      \<times> bool)"
  shows
    "slp_mixed_center_finite_active_residual center x =
      inner x (slp_mixed_center_finite_active_hessian *v x) / 2 +
        inner (slp_mixed_center_finite_active_linear center) x +
        slp_mixed_center_finite_active_constant TYPE('i) TYPE('j) center"
proof -
  have distinguished_sign:
      "(slp_mixed_combined_sign ::
          (unit + (unit + ((('i + 'i) + unit) + ('j + 'j)))) \<Rightarrow> real)
          (Inl ()) = -1 \<or>
        slp_mixed_combined_sign (Inl ()) = 1"
    by (simp add: slp_mixed_combined_sign_def)
  note raw = slp_signed_residual_product_phase[
    where epsilon =
      "slp_mixed_combined_sign ::
        (unit + (unit + ((('i + 'i) + unit) + ('j + 'j)))) \<Rightarrow> real"
      and c = "slp_complex_coordinate_pack (slp_point_as_complex center)"
      and u = x, OF distinguished_sign]
  show ?thesis
    using raw
    unfolding slp_mixed_center_finite_active_residual_def
      slp_mixed_center_finite_active_hessian_def
      slp_mixed_center_finite_active_linear_def
      slp_mixed_center_finite_active_constant_def
    by (simp only: slp_complex_coordinate_unpack_pack)
qed

theorem slp_mixed_center_finite_active_hessian_symmetric:
  "hormander_real_symmetric_matrix
    (slp_mixed_center_finite_active_hessian ::
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool)^((unit + ((('i + 'i) + unit) + ('j + 'j)))
          \<times> bool))"
  unfolding slp_mixed_center_finite_active_hessian_def
  by (rule slp_signed_active_hessian_symmetric)
    (simp add: slp_mixed_combined_sign_def)

theorem slp_mixed_center_finite_active_hessian_nondegenerate:
  "hormander_real_nondegenerate_matrix
    (slp_mixed_center_finite_active_hessian ::
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool)^((unit + ((('i + 'i) + unit) + ('j + 'j)))
          \<times> bool))"
  unfolding slp_mixed_center_finite_active_hessian_def
  by (rule slp_signed_active_hessian_nondegenerate[
        OF slp_mixed_combined_sign_values slp_mixed_combined_signed_sum])

end
