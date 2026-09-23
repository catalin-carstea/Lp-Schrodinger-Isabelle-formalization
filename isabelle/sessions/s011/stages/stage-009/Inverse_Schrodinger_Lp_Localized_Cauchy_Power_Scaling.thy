theory Inverse_Schrodinger_Lp_Localized_Cauchy_Power_Scaling
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Localized_Cauchy_Scaling"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Localized_Cauchy_Kernel_Lp"
begin

section \<open>Power scaling of the localized Cauchy kernel\<close>

theorem slp_localized_cauchy_kernel_power_integral_scale:
  assumes radius_positive: "0 < R"
    and exponent_lower: "1 \<le> s"
    and exponent_upper: "s < 2"
  shows "integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s) =
    R powr (2 - s) *
      integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s)"
proof -
  let ?g = "(*\<^sub>R) R :: slp_point \<Rightarrow> slp_point"
  have scale_linear: "linear ?g"
    by (rule bounded_linear.linear[OF bounded_linear_scaleR_right])
  have scale_injective: "inj ?g"
  proof (rule injI)
    fix x y :: slp_point
    assume "R *\<^sub>R x = R *\<^sub>R y"
    with radius_positive show "x = y" by simp
  qed
  have target_integrable:
    "integrable lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s)"
    by (rule slp_localized_cauchy_kernel_power_integrable[
          OF exponent_lower exponent_upper])
  have jacobian:
    "integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s) =
      \<bar>det (matrix ?g)\<bar> *\<^sub>R
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R (?g x)) powr s)"
    by (rule slp_lborel_linear_pullback(2)[OF scale_linear
          scale_injective target_integrable])
  have determinant: "\<bar>det (matrix ?g)\<bar> = R ^ 2"
    using radius_positive by simp
  have pullback_eq:
    "(\<lambda>x. abs (slp_localized_cauchy_kernel R (?g x)) powr s) =
      (\<lambda>x. R powr (-s) *
        abs (slp_localized_cauchy_kernel 1 x) powr s)"
  proof (rule ext)
    fix x :: slp_point
    have kernel_scale:
      "slp_localized_cauchy_kernel R (?g x) =
        inverse R * slp_localized_cauchy_kernel 1 x"
      by (rule slp_localized_cauchy_kernel_scale[OF radius_positive])
    show "abs (slp_localized_cauchy_kernel R (?g x)) powr s =
        R powr (-s) * abs (slp_localized_cauchy_kernel 1 x) powr s"
      unfolding kernel_scale
      using radius_positive
      by (simp add: abs_mult inverse_powr powr_minus powr_mult)
  qed
  have pulled_integral:
    "integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R (?g x)) powr s) =
      R powr (-s) *
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s)"
    by (simp only: pullback_eq
          Bochner_Integration.integral_mult_right_zero)
  have square_as_powr: "R ^ 2 = R powr (real 2)"
    by (rule sym, rule powr_realpow[OF radius_positive])
  have exponent_notation: "(real 2 - s :: real) = 2 - s"
    by simp
  have scale_factor:
    "R ^ 2 * R powr (-s) = R powr (2 - s)"
    using square_as_powr
    by (simp only: square_as_powr powr_add[symmetric]
          add_uminus_conv_diff exponent_notation)
  have expanded:
    "integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s) =
      R ^ 2 *
        (R powr (-s) *
          integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s))"
    using jacobian determinant pulled_integral
    by (simp only: real_scaleR_def)
  have reassociated:
    "R ^ 2 *
        (R powr (-s) *
          integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s)) =
      (R ^ 2 * R powr (-s)) *
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s)"
    by (simp only: mult.assoc[symmetric])
  have normalized:
    "(R ^ 2 * R powr (-s)) *
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s) =
      R powr (2 - s) *
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s)"
    by (simp only: scale_factor)
  have expanded_reassociated:
    "integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s) =
      (R ^ 2 * R powr (-s)) *
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s)"
    by (rule trans[OF expanded reassociated])
  show ?thesis
    by (rule trans[OF expanded_reassociated normalized])
qed

theorem slp_localized_cauchy_kernel_power_root_scale:
  assumes radius_positive: "0 < R"
    and exponent_lower: "1 \<le> s"
    and exponent_upper: "s < 2"
  shows
    "(integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s))
        powr (1 / s) =
      R powr (2 / s - 1) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s))
          powr (1 / s)"
proof -
  have exponent_positive: "0 < s"
    using exponent_lower by linarith
  have exponent_nonzero: "s \<noteq> 0"
    using exponent_positive by simp
  have exponent_identity:
    "(2 - s) * (1 / s) = 2 / s - 1"
    using exponent_nonzero by (simp add: field_simps)
  have integral_scale:
    "integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s) =
      R powr (2 - s) *
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s)"
    by (rule slp_localized_cauchy_kernel_power_integral_scale[
          OF radius_positive exponent_lower exponent_upper])
  have lifted_scale:
    "(integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s))
        powr (1 / s) =
      (R powr (2 - s) *
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s))
        powr (1 / s)"
    by (simp only: integral_scale)
  have product_power:
    "(R powr (2 - s) *
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s))
        powr (1 / s) =
      (R powr (2 - s)) powr (1 / s) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s))
          powr (1 / s)"
    by (rule powr_mult)
  have root_scale:
    "(R powr (2 - s)) powr (1 / s) =
      R powr (2 / s - 1)"
    by (simp only: powr_powr exponent_identity)
  have normalized:
    "(R powr (2 - s)) powr (1 / s) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s))
          powr (1 / s) =
      R powr (2 / s - 1) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s))
          powr (1 / s)"
    by (simp only: root_scale)
  have lifted_product:
    "(integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s))
        powr (1 / s) =
      (R powr (2 - s)) powr (1 / s) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr s))
          powr (1 / s)"
    by (rule trans[OF lifted_scale product_power])
  show ?thesis
    by (rule trans[OF lifted_product normalized])
qed

end
