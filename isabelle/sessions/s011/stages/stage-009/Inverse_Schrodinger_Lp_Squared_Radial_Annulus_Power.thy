theory Inverse_Schrodinger_Lp_Squared_Radial_Annulus_Power
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Squared_Radial_Annulus"
begin

section \<open>Real powers of the squared inverse-radius annulus\<close>

definition slp_squared_radial_annulus_power ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_squared_radial_annulus_power s delta R y =
    slp_squared_radial_annulus delta R y powr s"

lemma slp_squared_radial_annulus_power_borel_measurable[measurable]:
  "slp_squared_radial_annulus_power s delta R
    \<in> borel_measurable lborel"
  unfolding slp_squared_radial_annulus_power_def by measurable

lemma slp_squared_radial_annulus_power_nonnegative[simp]:
  "0 \<le> slp_squared_radial_annulus_power s delta R y"
  unfolding slp_squared_radial_annulus_power_def by simp

lemma slp_squared_radial_annulus_pointwise_upper:
  assumes delta_positive: "0 < delta"
  shows "slp_squared_radial_annulus delta R y \<le> 1 / delta ^ 2"
proof (cases "delta \<le> norm y \<and> norm y \<le> R")
  case True
  have radial_bound:
    "slp_radial_inverse_square y \<le> 1 / delta ^ 2"
    by (rule slp_radial_inverse_square_bound[OF delta_positive])
      (use True in simp)
  show ?thesis
    using True radial_bound
    by (simp add: slp_squared_radial_annulus_def)
next
  case False
  show ?thesis
    using delta_positive
    by (simp add: slp_squared_radial_annulus_def False)
qed

lemma slp_squared_radial_annulus_power_pointwise_majorant:
  assumes delta_positive: "0 < delta"
    and exponent_lower: "1 \<le> s"
  shows
    "slp_squared_radial_annulus_power s delta R y \<le>
      (1 / delta ^ 2) powr (s - 1) *
        slp_squared_radial_annulus delta R y"
proof -
  let ?A = "slp_squared_radial_annulus delta R y"
  have exponent_nonnegative: "0 \<le> s - 1"
    using exponent_lower by linarith
  have annulus_nonnegative: "0 \<le> ?A"
    by simp
  have annulus_upper: "?A \<le> 1 / delta ^ 2"
    by (rule slp_squared_radial_annulus_pointwise_upper[
          OF delta_positive])
  have factor_bound:
    "?A powr (s - 1) \<le> (1 / delta ^ 2) powr (s - 1)"
    by (rule powr_mono2[OF exponent_nonnegative annulus_nonnegative
          annulus_upper])
  have split_power:
    "slp_squared_radial_annulus_power s delta R y =
      ?A * ?A powr (s - 1)"
  proof -
    have multiply_power:
      "?A * ?A powr (s - 1) = ?A powr (1 + (s - 1))"
      by (rule powr_mult_base[OF annulus_nonnegative])
    show ?thesis
      unfolding slp_squared_radial_annulus_power_def
      using multiply_power by simp
  qed
  have multiplied:
    "?A * ?A powr (s - 1) \<le>
      ?A * (1 / delta ^ 2) powr (s - 1)"
    by (rule mult_left_mono[OF factor_bound annulus_nonnegative])
  show ?thesis
    using split_power multiplied by (simp add: mult.commute)
qed

theorem slp_squared_radial_annulus_power_integrable:
  assumes delta_positive: "0 < delta"
    and exponent_lower: "1 \<le> s"
  shows "integrable lborel
    (slp_squared_radial_annulus_power s delta R)"
proof -
  let ?c = "(1 / delta ^ 2) powr (s - 1)"
  let ?majorant =
    "\<lambda>y. ?c * slp_squared_radial_annulus delta R y"
  have annulus_integrable:
    "integrable lborel (slp_squared_radial_annulus delta R)"
    by (rule slp_squared_radial_annulus_integrable[OF delta_positive])
  have majorant_integrable: "integrable lborel ?majorant"
    using annulus_integrable by (rule integrable_mult_right)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_squared_radial_annulus_power s delta R
        \<in> borel_measurable lborel"
      by (rule slp_squared_radial_annulus_power_borel_measurable)
    show "AE y in lborel.
        norm (slp_squared_radial_annulus_power s delta R y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have domination:
        "slp_squared_radial_annulus_power s delta R y \<le>
          ?majorant y"
        by (rule slp_squared_radial_annulus_power_pointwise_majorant[
              OF delta_positive exponent_lower])
      have majorant_nonnegative: "0 \<le> ?majorant y"
        by simp
      show "norm (slp_squared_radial_annulus_power s delta R y) \<le>
          norm (?majorant y)"
        using domination majorant_nonnegative by simp
    qed
  qed
qed

lemma slp_squared_radial_annulus_power_scale:
  assumes scale_positive: "0 < a"
  shows
    "slp_squared_radial_annulus_power s (a * delta) (a * R)
        (a *\<^sub>R y) =
      a powr (-2 * s) *
        slp_squared_radial_annulus_power s delta R y"
proof -
  have base_scale:
    "slp_squared_radial_annulus (a * delta) (a * R)
        (a *\<^sub>R y) =
      inverse (a ^ 2) * slp_squared_radial_annulus delta R y"
    by (rule slp_squared_radial_annulus_scale[OF scale_positive])
  have square_as_powr: "a ^ 2 = a powr (real 2)"
    by (rule sym, rule powr_realpow[OF scale_positive])
  have inverse_square: "inverse (a ^ 2) = a powr (- real 2)"
    by (simp only: square_as_powr powr_minus)
  have coefficient_exponent:
    "(- real 2) * s = (-2 * s :: real)"
    by simp
  have coefficient_power:
    "(inverse (a ^ 2)) powr s = a powr (-2 * s)"
    by (simp only: inverse_square powr_powr coefficient_exponent)
  have product_power:
    "(inverse (a ^ 2) * slp_squared_radial_annulus delta R y)
        powr s =
      (inverse (a ^ 2)) powr s *
        slp_squared_radial_annulus delta R y powr s"
    by (rule powr_mult)
  show ?thesis
    unfolding slp_squared_radial_annulus_power_def
    by (simp only: base_scale product_power coefficient_power)
qed

theorem slp_squared_radial_annulus_power_integral_scale:
  assumes scale_positive: "0 < a"
    and delta_positive: "0 < delta"
    and exponent_lower: "1 \<le> s"
  shows
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s (a * delta) (a * R)) =
      a powr (2 - 2 * s) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s delta R)"
proof -
  let ?g = "(*\<^sub>R) a :: slp_point \<Rightarrow> slp_point"
  have scale_linear: "linear ?g"
    by (rule bounded_linear.linear[OF bounded_linear_scaleR_right])
  have scale_injective: "inj ?g"
  proof (rule injI)
    fix x y :: slp_point
    assume "a *\<^sub>R x = a *\<^sub>R y"
    with scale_positive show "x = y" by simp
  qed
  have scaled_delta_positive: "0 < a * delta"
    using scale_positive delta_positive by simp
  have target_integrable:
    "integrable lborel
      (slp_squared_radial_annulus_power s (a * delta) (a * R))"
    by (rule slp_squared_radial_annulus_power_integrable[
          OF scaled_delta_positive exponent_lower])
  have jacobian:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s (a * delta) (a * R)) =
      \<bar>det (matrix ?g)\<bar> *\<^sub>R
        integral\<^sup>L lborel
          (\<lambda>y. slp_squared_radial_annulus_power
            s (a * delta) (a * R) (?g y))"
    by (rule slp_lborel_linear_pullback(2)[OF scale_linear
          scale_injective target_integrable])
  have determinant: "\<bar>det (matrix ?g)\<bar> = a ^ 2"
    using scale_positive by simp
  have pullback_eq:
    "(\<lambda>y. slp_squared_radial_annulus_power
        s (a * delta) (a * R) (?g y)) =
      (\<lambda>y. a powr (-2 * s) *
        slp_squared_radial_annulus_power s delta R y)"
    by (rule ext)
      (rule slp_squared_radial_annulus_power_scale[OF scale_positive])
  have pulled_integral:
    "integral\<^sup>L lborel
        (\<lambda>y. slp_squared_radial_annulus_power
          s (a * delta) (a * R) (?g y)) =
      a powr (-2 * s) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s delta R)"
    by (simp only: pullback_eq
          Bochner_Integration.integral_mult_right_zero)
  have square_as_powr: "a ^ 2 = a powr (real 2)"
    by (rule sym, rule powr_realpow[OF scale_positive])
  have exponent_notation:
    "(real 2 + (-2 * s) :: real) = 2 - 2 * s"
    by simp
  have scale_factor:
    "a ^ 2 * a powr (-2 * s) = a powr (2 - 2 * s)"
    by (simp only: square_as_powr powr_add[symmetric]
          exponent_notation)
  have expanded:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s (a * delta) (a * R)) =
      a ^ 2 *
        (a powr (-2 * s) *
          integral\<^sup>L lborel
            (slp_squared_radial_annulus_power s delta R))"
    using jacobian determinant pulled_integral
    by (simp only: real_scaleR_def)
  have reassociated:
    "a ^ 2 *
        (a powr (-2 * s) *
          integral\<^sup>L lborel
            (slp_squared_radial_annulus_power s delta R)) =
      (a ^ 2 * a powr (-2 * s)) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s delta R)"
    by (simp only: mult.assoc[symmetric])
  have normalized:
    "(a ^ 2 * a powr (-2 * s)) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s delta R) =
      a powr (2 - 2 * s) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s delta R)"
    by (simp only: scale_factor)
  have expanded_reassociated:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s (a * delta) (a * R)) =
      (a ^ 2 * a powr (-2 * s)) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s delta R)"
    by (rule trans[OF expanded reassociated])
  show ?thesis
    by (rule trans[OF expanded_reassociated normalized])
qed

end
