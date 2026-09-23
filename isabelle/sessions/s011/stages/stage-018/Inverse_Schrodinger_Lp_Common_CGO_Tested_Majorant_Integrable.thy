theory Inverse_Schrodinger_Lp_Common_CGO_Tested_Majorant_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Two_Cauchy_Three_Component_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Common_CGO_Born_Remainder_Bound"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Integrability of the literal common-CGO tested majorant\<close>

context aim_planar_hls_cauchy
begin

theorem slp_common_cgo_born_tested_geometric_majorant_integrable:
  fixes N M :: nat
    and p epsilon C_left CV_left C_right CV_right tau :: real
    and coefficient coefficient_tilde phi :: slp_scalar_field
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_tilde_lp:
      "aim_complex_lp_on_plane p coefficient_tilde"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "integrable lborel (\<lambda>c. norm (phi c) *
      ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient c))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon)) +
       (C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde c))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)) +
       ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient c))) /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde c))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
       ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient c))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde c))) /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
       ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient c))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde c))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)))))"
proof -
  let ?e = "tau powr (-(1 - 1 / p) + epsilon)"
  let ?rho_left = "CV_left * ?e"
  let ?rho_right = "CV_right * ?e"
  let ?A = "slp_dbar_inverse coefficient"
  let ?B = "slp_partial_inverse coefficient_tilde"
  let ?a = "aim_complex_lp_norm p coefficient"
  let ?b = "aim_complex_lp_norm p coefficient_tilde"
  let ?k_left = "C_left * ?e * ?rho_left ^ N / (1 - ?rho_left)"
  let ?k_right = "C_right * ?e * ?rho_right ^ M / (1 - ?rho_right)"
  let ?k_cross =
    "(C_left * ?e / (1 - ?rho_left)) *
       (C_right * ?e * ?rho_right ^ M / (1 - ?rho_right)) +
     (C_left * ?e * ?rho_left ^ N / (1 - ?rho_left)) *
       (C_right * ?e / (1 - ?rho_right)) +
     (C_left * ?e * ?rho_left ^ N / (1 - ?rho_left)) *
       (C_right * ?e * ?rho_right ^ M / (1 - ?rho_right))"
  note raw = slp_test_two_cauchy_three_component_majorant_integrable[
    where q = coefficient and qt = coefficient_tilde and phi = phi
      and lo = SLP_Dbar_Inverse and ro = SLP_Partial_Inverse
      and a = ?a and b = ?b and k_left = ?k_left and k_right = ?k_right
      and k_cross = ?k_cross,
    OF p_lower p_upper coefficient_lp coefficient_tilde_lp phi_test]
  have grouped:
      "integrable lborel (\<lambda>c. norm (phi c) *
        (?k_left * (?a + norm (?A c)) +
         ?k_right * (?b + norm (?B c)) +
         ?k_cross * (?a + norm (?A c)) * (?b + norm (?B c))))"
    by (rule raw)
  have left_shape:
      "(C_left * ?e * X) * ?rho_left ^ N / (1 - ?rho_left) =
       ?k_left * X"
    for X :: real
    by (simp only: divide_inverse mult_ac)
  have right_shape:
      "(C_right * ?e * Y) * ?rho_right ^ M / (1 - ?rho_right) =
       ?k_right * Y"
    for Y :: real
    by (simp only: divide_inverse mult_ac)
  have first_cross_shape:
      "((C_left * ?e * X) / (1 - ?rho_left)) *
         ((C_right * ?e * Y) * ?rho_right ^ M / (1 - ?rho_right)) =
       ((C_left * ?e / (1 - ?rho_left)) *
         (C_right * ?e * ?rho_right ^ M / (1 - ?rho_right))) * X * Y"
    for X Y :: real
    by (simp only: divide_inverse mult_ac)
  have second_cross_shape:
      "((C_left * ?e * X) * ?rho_left ^ N / (1 - ?rho_left)) *
         ((C_right * ?e * Y) / (1 - ?rho_right)) =
       ((C_left * ?e * ?rho_left ^ N / (1 - ?rho_left)) *
         (C_right * ?e / (1 - ?rho_right))) * X * Y"
    for X Y :: real
    by (simp only: divide_inverse mult_ac)
  have third_cross_shape:
      "((C_left * ?e * X) * ?rho_left ^ N / (1 - ?rho_left)) *
         ((C_right * ?e * Y) * ?rho_right ^ M / (1 - ?rho_right)) =
       ((C_left * ?e * ?rho_left ^ N / (1 - ?rho_left)) *
         (C_right * ?e * ?rho_right ^ M / (1 - ?rho_right))) * X * Y"
    for X Y :: real
    by (simp only: divide_inverse mult_ac)
  have five_term_regroup:
      "L + R + K1 * X * Y + K2 * X * Y + K3 * X * Y =
       L + R + (K1 + K2 + K3) * X * Y"
    for L R K1 K2 K3 X Y :: real
    by (simp only: distrib_right add.assoc)
  have presentation:
      "(\<lambda>c. norm (phi c) *
        ((C_left * ?e * (?a + norm (?A c))) * ?rho_left ^ N /
            (1 - ?rho_left) +
         (C_right * ?e * (?b + norm (?B c))) * ?rho_right ^ M /
            (1 - ?rho_right) +
         ((C_left * ?e * (?a + norm (?A c))) / (1 - ?rho_left)) *
           ((C_right * ?e * (?b + norm (?B c))) * ?rho_right ^ M /
             (1 - ?rho_right)) +
         ((C_left * ?e * (?a + norm (?A c))) * ?rho_left ^ N /
             (1 - ?rho_left)) *
           ((C_right * ?e * (?b + norm (?B c))) / (1 - ?rho_right)) +
         ((C_left * ?e * (?a + norm (?A c))) * ?rho_left ^ N /
             (1 - ?rho_left)) *
           ((C_right * ?e * (?b + norm (?B c))) * ?rho_right ^ M /
             (1 - ?rho_right)))) =
       (\<lambda>c. norm (phi c) *
        (?k_left * (?a + norm (?A c)) +
         ?k_right * (?b + norm (?B c)) +
         ?k_cross * (?a + norm (?A c)) * (?b + norm (?B c))))"
    apply (simp only: fun_eq_iff first_cross_shape second_cross_shape
        third_cross_shape)
    apply (simp only: left_shape right_shape five_term_regroup)
    apply (rule allI)
    apply (rule refl)
    done
  show ?thesis using grouped by (simp only: presentation)
qed

end

end
