theory Inverse_Schrodinger_Lp_Common_CGO_Literal_Majorant_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Scalar_Center_Integral_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Tested_Majorant_Integrable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Literal common-CGO tested-majorant decay\<close>

lemma slp_common_cgo_born_geometric_majorant_as_scalar_center_majorant:
  fixes N M :: nat
    and p epsilon C_left CV_left C_right CV_right tau :: real
    and coefficient coefficient_tilde phi :: slp_scalar_field
  shows
    "(\<lambda>c. norm (phi c) *
        slp_common_cgo_born_geometric_majorant
          N M p epsilon C_left CV_left C_right CV_right tau
          coefficient coefficient_tilde c) =
      slp_common_cgo_scalar_center_majorant
        N M (1 - 1 / p - epsilon) C_left CV_left C_right CV_right
        (\<lambda>c. norm (phi c))
        (\<lambda>c. aim_complex_lp_norm p coefficient +
          norm (slp_dbar_inverse coefficient c))
        (\<lambda>c. aim_complex_lp_norm p coefficient_tilde +
          norm (slp_partial_inverse coefficient_tilde c))
        tau"
  unfolding slp_common_cgo_born_geometric_majorant_def
    slp_common_cgo_scalar_center_majorant_def
    slp_common_cgo_scalar_tail_def slp_common_cgo_scalar_prefix_def
  by (simp add: fun_eq_iff divide_inverse algebra_simps)

context aim_planar_hls_cauchy
begin

theorem slp_common_cgo_born_tested_geometric_majorant_tendsto_zero:
  fixes p epsilon C_left CV_left C_right CV_right :: real
    and coefficient coefficient_tilde phi :: slp_scalar_field
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and loss_positive: "0 < epsilon"
    and loss_upper: "epsilon < 1 - 1 / p"
    and CV_left_nonnegative: "0 \<le> CV_left"
    and CV_right_nonnegative: "0 \<le> CV_right"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_tilde_lp:
      "aim_complex_lp_on_plane p coefficient_tilde"
    and phi_test: "slp_test_function_on UNIV phi"
  defines
    "N \<equiv> nat
      (slp_tail_cutoff1 (1 - 1 / p - epsilon) (1 - 1 / p - epsilon))"
  shows
    "((\<lambda>tau :: real.
        tau * integral\<^sup>L lborel (\<lambda>c. norm (phi c) *
          slp_common_cgo_born_geometric_majorant
            N N p epsilon C_left CV_left C_right CV_right tau
            coefficient coefficient_tilde c))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?alpha = "1 - 1 / p - epsilon"
  let ?left_factor =
    "\<lambda>c. aim_complex_lp_norm p coefficient +
      norm (slp_dbar_inverse coefficient c)"
  let ?right_factor =
    "\<lambda>c. aim_complex_lp_norm p coefficient_tilde +
      norm (slp_partial_inverse coefficient_tilde c)"
  have p_positive: "0 < p"
    using p_lower by linarith
  have inverse_positive: "0 < 1 / p"
    using p_positive by simp
  have alpha_positive: "0 < ?alpha"
    using loss_upper by linarith
  have alpha_at_most_one: "?alpha \<le> 1"
    using inverse_positive loss_positive by linarith
  note left_raw = slp_test_two_cauchy_three_component_majorant_integrable[
    where q=coefficient and qt=coefficient_tilde and phi=phi
      and lo=SLP_Dbar_Inverse and ro=SLP_Partial_Inverse
      and a="aim_complex_lp_norm p coefficient"
      and b="aim_complex_lp_norm p coefficient_tilde"
      and k_left=1 and k_right=0 and k_cross=0,
    OF p_lower p_upper coefficient_lp coefficient_tilde_lp phi_test]
  have left_integrable:
      "integrable lborel (\<lambda>c. norm (phi c) * ?left_factor c)"
    using left_raw by simp
  note right_raw = slp_test_two_cauchy_three_component_majorant_integrable[
    where q=coefficient and qt=coefficient_tilde and phi=phi
      and lo=SLP_Dbar_Inverse and ro=SLP_Partial_Inverse
      and a="aim_complex_lp_norm p coefficient"
      and b="aim_complex_lp_norm p coefficient_tilde"
      and k_left=0 and k_right=1 and k_cross=0,
    OF p_lower p_upper coefficient_lp coefficient_tilde_lp phi_test]
  have right_integrable:
      "integrable lborel (\<lambda>c. norm (phi c) * ?right_factor c)"
    using right_raw by simp
  have cross_integrable:
      "integrable lborel
        (\<lambda>c. norm (phi c) * ?left_factor c * ?right_factor c)"
    by (rule slp_test_two_cauchy_affine_norm_product_integrable[
      where q=coefficient and qt=coefficient_tilde and phi=phi
        and lo=SLP_Dbar_Inverse and ro=SLP_Partial_Inverse
        and a="aim_complex_lp_norm p coefficient"
        and b="aim_complex_lp_norm p coefficient_tilde",
      OF p_lower p_upper coefficient_lp coefficient_tilde_lp phi_test])
  have scalar_limit:
      "((\<lambda>tau :: real.
          tau * integral\<^sup>L lborel
            (slp_common_cgo_scalar_center_majorant
              N N ?alpha C_left CV_left C_right CV_right
              (\<lambda>c. norm (phi c)) ?left_factor ?right_factor tau))
        \<longlongrightarrow> 0) at_top"
    unfolding N_def
    by (rule slp_common_cgo_outer_scalar_center_integral_tendsto_zero[
      OF alpha_positive alpha_at_most_one CV_left_nonnegative
        CV_right_nonnegative left_integrable right_integrable
        cross_integrable])
  have integrand_identity:
      "(\<lambda>c. norm (phi c) *
          slp_common_cgo_born_geometric_majorant
            N N p epsilon C_left CV_left C_right CV_right tau
            coefficient coefficient_tilde c) =
        slp_common_cgo_scalar_center_majorant
          N N ?alpha C_left CV_left C_right CV_right
          (\<lambda>c. norm (phi c)) ?left_factor ?right_factor tau"
    for tau
    by (rule
      slp_common_cgo_born_geometric_majorant_as_scalar_center_majorant)
  have limit_identity:
      "(\<lambda>tau :: real.
          tau * integral\<^sup>L lborel (\<lambda>c. norm (phi c) *
            slp_common_cgo_born_geometric_majorant
              N N p epsilon C_left CV_left C_right CV_right tau
              coefficient coefficient_tilde c)) =
        (\<lambda>tau :: real.
          tau * integral\<^sup>L lborel
            (slp_common_cgo_scalar_center_majorant
              N N ?alpha C_left CV_left C_right CV_right
              (\<lambda>c. norm (phi c)) ?left_factor ?right_factor tau))"
    apply (simp only: fun_eq_iff integrand_identity)
    apply (rule allI)
    apply (rule refl)
    done
  show ?thesis
    unfolding limit_identity
    by (rule scalar_limit)
qed

end

end
