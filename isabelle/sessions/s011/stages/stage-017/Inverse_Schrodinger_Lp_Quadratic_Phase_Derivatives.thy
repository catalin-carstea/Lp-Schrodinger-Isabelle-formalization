theory Inverse_Schrodinger_Lp_Quadratic_Phase_Derivatives
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Quadratic_Phase_Multipliers"
begin

section \<open>Smooth complex exponential composition\<close>

lemma slp_smooth_on_complex_exp:
  fixes f :: "'a::euclidean_space \<Rightarrow> complex"
  assumes f_smooth: "smooth_on UNIV f"
  shows "smooth_on UNIV (\<lambda>x. exp (f x))"
proof -
  have higher_exp:
      "higher_differentiable_on UNIV (\<lambda>x. exp (g x)) n"
    if g_higher: "higher_differentiable_on UNIV g n"
    for g :: "'a \<Rightarrow> complex" and n
    using g_higher
  proof (induction n arbitrary: g)
    case 0
    then show ?case
      by (auto simp: higher_differentiable_on.simps
          intro!: continuous_intros)
  next
    case (Suc n)
    have g_lower: "higher_differentiable_on UNIV g n"
      by (rule higher_differentiable_on_SucD[OF Suc.prems])
    have exp_lower:
        "higher_differentiable_on UNIV (\<lambda>x. exp (g x)) n"
      by (rule Suc.IH[OF g_lower])
    have g_differentiable: "g differentiable (at x)" for x
      using Suc.prems by (simp add: higher_differentiable_on.simps)
    have exp_differentiable: "exp differentiable (at (g x))" for x
      using DERIV_exp[of "g x"] unfolding has_field_derivative_def
      by (rule differentiableI)
    have composite_differentiable:
        "(\<lambda>x. exp (g x)) differentiable (at x)" for x
      using differentiable_chain_at[OF g_differentiable
          exp_differentiable]
      by (simp only: o_def)
    have derivative_eq:
        "frechet_derivative (\<lambda>y. exp (g y)) (at x) v =
          exp (g x) * frechet_derivative g (at x) v"
      for x v
    proof -
      have g_derivative:
          "(g has_derivative frechet_derivative g (at x)) (at x)"
        using g_differentiable
        by (simp only: frechet_derivative_works)
      have exp_derivative:
          "(exp has_derivative (\<lambda>h. exp (g x) * h)) (at (g x))"
        using DERIV_exp[of "g x"]
        unfolding has_field_derivative_def .
      have composed:
          "((\<lambda>y. exp (g y)) has_derivative
            (\<lambda>h. exp (g x) * frechet_derivative g (at x) h))
            (at x)"
        by (rule has_derivative_compose[OF g_derivative exp_derivative])
      have maps_equal:
          "(\<lambda>h. exp (g x) * frechet_derivative g (at x) h) =
            frechet_derivative (\<lambda>y. exp (g y)) (at x)"
        by (rule frechet_derivative_at[OF composed])
      show ?thesis
        using fun_cong[OF maps_equal, of v] by simp
    qed
    have derivative_higher:
        "higher_differentiable_on UNIV
          (\<lambda>x. frechet_derivative g (at x) v) n" for v
      using Suc.prems by (simp add: higher_differentiable_on.simps)
    have product_higher:
        "higher_differentiable_on UNIV
          (\<lambda>x. exp (g x) * frechet_derivative g (at x) v) n"
      for v
      by (rule higher_differentiable_on_mult[OF exp_lower
            derivative_higher open_UNIV])
    show ?case
      unfolding higher_differentiable_on.simps
    proof (intro conjI)
      show "\<forall>x\<in>UNIV. (\<lambda>x. exp (g x)) differentiable (at x)"
        using composite_differentiable by blast
      show "\<forall>v. higher_differentiable_on UNIV
          (\<lambda>x. frechet_derivative (\<lambda>y. exp (g y)) (at x) v) n"
      proof
        fix v
        show "higher_differentiable_on UNIV
            (\<lambda>x. frechet_derivative (\<lambda>y. exp (g y))
              (at x) v) n"
          by (rule higher_differentiable_on_congI[OF open_UNIV
                product_higher])
             (simp only: derivative_eq)
      qed
    qed
  qed
  show ?thesis
    using f_smooth higher_exp unfolding smooth_on_def by blast
qed

section \<open>Exact individual quadratic-phase differentials\<close>

lemma slp_holomorphic_quadratic_phase_multiplier_has_derivative:
  shows
    "((slp_holomorphic_quadratic_phase_multiplier tau c) has_derivative
      (\<lambda>h. slp_holomorphic_quadratic_phase_multiplier tau c z *
        (\<i> * of_real tau * slp_point_as_complex (z - c) *
          slp_point_as_complex h))) (at z)"
    "smooth_on UNIV (slp_holomorphic_quadratic_phase_multiplier tau c)"
proof -
  have shifted:
      "((\<lambda>y :: slp_point. slp_point_as_complex (y - c)) has_derivative
        slp_point_as_complex) (at z)"
  proof -
    have shift:
        "((\<lambda>y :: slp_point. y - c) has_derivative id) (at z)"
      by (auto intro!: derivative_eq_intros)
    have coordinate:
        "(slp_point_as_complex has_derivative slp_point_as_complex)
          (at (z - c))"
      using bounded_linear.has_derivative[OF
          slp_point_as_complex_bounded_linear has_derivative_id]
      by (simp only: id_apply)
    show ?thesis
      using has_derivative_compose[OF shift coordinate]
      by (simp only: id_apply)
  qed
  have square:
      "((\<lambda>y :: slp_point.
          (slp_point_as_complex (y - c)) ^ 2) has_derivative
        (\<lambda>h. (of_nat 2 :: complex) * slp_point_as_complex h *
          slp_point_as_complex (z - c) ^ (2 - 1))) (at z)"
    by (rule has_derivative_power[OF shifted])
  have scaled:
      "((\<lambda>u :: complex. \<i> * of_real (tau / 2) * u) has_derivative
        (\<lambda>h. \<i> * of_real (tau / 2) * h))
        (at ((slp_point_as_complex (z - c)) ^ 2))"
    using bounded_linear.has_derivative[OF
        bounded_linear_mult_right has_derivative_id]
    by (simp only: id_apply)
  have scalar_identity:
      "\<i> * of_real (tau / 2) *
          ((of_nat 2 :: complex) * q * w ^ (2 - 1)) =
        \<i> * of_real tau * w * q" for w q :: complex
    by (simp add: of_real_divide divide_simps algebra_simps)
  have inner_native:
      "((\<lambda>y :: slp_point.
          \<i> * of_real (tau / 2) *
            (slp_point_as_complex (y - c)) ^ 2) has_derivative
        (\<lambda>h. \<i> * of_real (tau / 2) *
          ((of_nat 2 :: complex) * slp_point_as_complex h *
            slp_point_as_complex (z - c) ^ (2 - 1))))
        (at z)"
    by (rule has_derivative_compose[OF square scaled])
  have inner:
      "((\<lambda>y :: slp_point.
          \<i> * of_real (tau / 2) *
            (slp_point_as_complex (y - c)) ^ 2) has_derivative
        (\<lambda>h. \<i> * of_real tau *
          slp_point_as_complex (z - c) * slp_point_as_complex h))
        (at z)"
    by (rule has_derivative_eq_rhs[OF inner_native])
       (rule ext, simp only: scalar_identity)
  have exp_at:
      "(exp has_derivative
        (\<lambda>h. exp (\<i> * of_real (tau / 2) *
          (slp_point_as_complex (z - c)) ^ 2) * h))
        (at (\<i> * of_real (tau / 2) *
          (slp_point_as_complex (z - c)) ^ 2))"
    by (rule DERIV_exp[unfolded has_field_derivative_def])
  have exponential:
      "((\<lambda>y :: slp_point. exp (\<i> * of_real (tau / 2) *
          (slp_point_as_complex (y - c)) ^ 2)) has_derivative
        (\<lambda>h. exp (\<i> * of_real (tau / 2) *
            (slp_point_as_complex (z - c)) ^ 2) *
          (\<i> * of_real tau * slp_point_as_complex (z - c) *
            slp_point_as_complex h))) (at z)"
    by (rule has_derivative_compose[OF inner exp_at])
  show "((slp_holomorphic_quadratic_phase_multiplier tau c)
      has_derivative
      (\<lambda>h. slp_holomorphic_quadratic_phase_multiplier tau c z *
        (\<i> * of_real tau * slp_point_as_complex (z - c) *
          slp_point_as_complex h))) (at z)"
    unfolding slp_holomorphic_quadratic_phase_multiplier_def
    by (rule exponential)

  have shifted_smooth:
      "smooth_on UNIV
        (\<lambda>y :: slp_point. slp_point_as_complex (y - c))"
    by (rule slp_shifted_point_as_complex_smooth)
  have square_smooth:
      "smooth_on UNIV
        (\<lambda>y :: slp_point. (slp_point_as_complex (y - c)) ^ 2)"
    using smooth_on_mult[OF shifted_smooth shifted_smooth open_UNIV]
    by (simp only: power2_eq_square)
  have inner_smooth:
      "smooth_on UNIV
        (\<lambda>y :: slp_point. \<i> * of_real (tau / 2) *
          (slp_point_as_complex (y - c)) ^ 2)"
    by (rule smooth_on_mult[OF smooth_on_const square_smooth open_UNIV])
  show "smooth_on UNIV
      (slp_holomorphic_quadratic_phase_multiplier tau c)"
    unfolding slp_holomorphic_quadratic_phase_multiplier_def
    by (rule slp_smooth_on_complex_exp[OF inner_smooth])
qed

lemma slp_antiholomorphic_quadratic_phase_multiplier_has_derivative:
  shows
    "((slp_antiholomorphic_quadratic_phase_multiplier tau c) has_derivative
      (\<lambda>h. slp_antiholomorphic_quadratic_phase_multiplier tau c z *
        (\<i> * of_real tau * cnj (slp_point_as_complex (z - c)) *
          cnj (slp_point_as_complex h)))) (at z)"
    "smooth_on UNIV
      (slp_antiholomorphic_quadratic_phase_multiplier tau c)"
proof -
  have shifted:
      "((\<lambda>y :: slp_point. slp_point_as_complex (y - c)) has_derivative
        slp_point_as_complex) (at z)"
  proof -
    have shift:
        "((\<lambda>y :: slp_point. y - c) has_derivative id) (at z)"
      by (auto intro!: derivative_eq_intros)
    have coordinate:
        "(slp_point_as_complex has_derivative slp_point_as_complex)
          (at (z - c))"
      using bounded_linear.has_derivative[OF
          slp_point_as_complex_bounded_linear has_derivative_id]
      by (simp only: id_apply)
    show ?thesis
      using has_derivative_compose[OF shift coordinate]
      by (simp only: id_apply)
  qed
  have square:
      "((\<lambda>y :: slp_point.
          (slp_point_as_complex (y - c)) ^ 2) has_derivative
        (\<lambda>h. (of_nat 2 :: complex) * slp_point_as_complex h *
          slp_point_as_complex (z - c) ^ (2 - 1))) (at z)"
    by (rule has_derivative_power[OF shifted])
  have conjugated_square:
      "((\<lambda>y :: slp_point.
          cnj ((slp_point_as_complex (y - c)) ^ 2)) has_derivative
        (\<lambda>h. cnj ((of_nat 2 :: complex) * slp_point_as_complex h *
          slp_point_as_complex (z - c) ^ (2 - 1)))) (at z)"
    by (rule has_derivative_cnj[OF square])
  have scaled:
      "((\<lambda>u :: complex. \<i> * of_real (tau / 2) * u) has_derivative
        (\<lambda>h. \<i> * of_real (tau / 2) * h))
        (at (cnj ((slp_point_as_complex (z - c)) ^ 2)))"
    using bounded_linear.has_derivative[OF
        bounded_linear_mult_right has_derivative_id]
    by (simp only: id_apply)
  have scalar_identity:
      "\<i> * of_real (tau / 2) *
          cnj ((of_nat 2 :: complex) * q * w ^ (2 - 1)) =
        \<i> * of_real tau * cnj w * cnj q" for w q :: complex
    by (simp add: of_real_divide divide_simps algebra_simps)
  have inner_native:
      "((\<lambda>y :: slp_point.
          \<i> * of_real (tau / 2) *
            cnj ((slp_point_as_complex (y - c)) ^ 2)) has_derivative
        (\<lambda>h. \<i> * of_real (tau / 2) *
          cnj ((of_nat 2 :: complex) * slp_point_as_complex h *
            slp_point_as_complex (z - c) ^ (2 - 1))))
        (at z)"
    by (rule has_derivative_compose[OF conjugated_square scaled])
  have inner:
      "((\<lambda>y :: slp_point.
          \<i> * of_real (tau / 2) *
            cnj ((slp_point_as_complex (y - c)) ^ 2)) has_derivative
        (\<lambda>h. \<i> * of_real tau *
          cnj (slp_point_as_complex (z - c)) *
            cnj (slp_point_as_complex h))) (at z)"
    by (rule has_derivative_eq_rhs[OF inner_native])
       (rule ext, simp only: scalar_identity)
  have exp_at:
      "(exp has_derivative
        (\<lambda>h. exp (\<i> * of_real (tau / 2) *
          cnj ((slp_point_as_complex (z - c)) ^ 2)) * h))
        (at (\<i> * of_real (tau / 2) *
          cnj ((slp_point_as_complex (z - c)) ^ 2)))"
    by (rule DERIV_exp[unfolded has_field_derivative_def])
  have exponential:
      "((\<lambda>y :: slp_point. exp (\<i> * of_real (tau / 2) *
          cnj ((slp_point_as_complex (y - c)) ^ 2))) has_derivative
        (\<lambda>h. exp (\<i> * of_real (tau / 2) *
            cnj ((slp_point_as_complex (z - c)) ^ 2)) *
          (\<i> * of_real tau * cnj (slp_point_as_complex (z - c)) *
            cnj (slp_point_as_complex h)))) (at z)"
    by (rule has_derivative_compose[OF inner exp_at])
  show "((slp_antiholomorphic_quadratic_phase_multiplier tau c)
      has_derivative
      (\<lambda>h. slp_antiholomorphic_quadratic_phase_multiplier tau c z *
        (\<i> * of_real tau * cnj (slp_point_as_complex (z - c)) *
          cnj (slp_point_as_complex h)))) (at z)"
    unfolding slp_antiholomorphic_quadratic_phase_multiplier_def
    by (rule exponential)

  have shifted_smooth:
      "smooth_on UNIV
        (\<lambda>y :: slp_point. slp_point_as_complex (y - c))"
    by (rule slp_shifted_point_as_complex_smooth)
  have square_smooth:
      "smooth_on UNIV
        (\<lambda>y :: slp_point. (slp_point_as_complex (y - c)) ^ 2)"
    using smooth_on_mult[OF shifted_smooth shifted_smooth open_UNIV]
    by (simp only: power2_eq_square)
  have cnj_smooth: "smooth_on UNIV cnj"
    by (rule bounded_linear.smooth_on[OF bounded_linear_cnj])
  have composed_cnj_smooth:
      "smooth_on UNIV
        (cnj \<circ> (\<lambda>y :: slp_point.
          (slp_point_as_complex (y - c)) ^ 2))"
    by (rule smooth_on_compose[OF cnj_smooth square_smooth
          open_UNIV open_UNIV])
       (rule subset_UNIV)
  have conjugated_square_smooth:
      "smooth_on UNIV
        (\<lambda>y :: slp_point. cnj ((slp_point_as_complex (y - c)) ^ 2))"
    using composed_cnj_smooth
    by (simp only: o_def)
  have inner_smooth:
      "smooth_on UNIV
        (\<lambda>y :: slp_point. \<i> * of_real (tau / 2) *
          cnj ((slp_point_as_complex (y - c)) ^ 2))"
    by (rule smooth_on_mult[OF smooth_on_const
          conjugated_square_smooth open_UNIV])
  show "smooth_on UNIV
      (slp_antiholomorphic_quadratic_phase_multiplier tau c)"
    unfolding slp_antiholomorphic_quadratic_phase_multiplier_def
    by (rule slp_smooth_on_complex_exp[OF inner_smooth])
qed

end
