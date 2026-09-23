theory Inverse_Schrodinger_Lp_CGO_Field_H1
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Quadratic_Phase_H1_Algebra"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Affine_Fixed_Point_H1"
begin

section \<open>Literal left and right CGO fields\<close>

definition slp_left_cgo_field ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field"
where
  "slp_left_cgo_field tau c W z =
    slp_holomorphic_quadratic_phase_multiplier tau c z +
    slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z * W z"

definition slp_left_cgo_gradient ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_gradient_field \<Rightarrow> slp_gradient_field"
where
  "slp_left_cgo_gradient tau c W DW z =
    (\<chi> i.
      slp_holomorphic_quadratic_phase_multiplier tau c z *
        (\<i> * of_real tau * slp_point_as_complex (z - c) *
          slp_point_as_complex (axis i 1))) +
    (\<chi> i.
      slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z * DW z $ i +
      W z * (slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z *
        (\<i> * of_real (- tau) * cnj (slp_point_as_complex (z - c)) *
          cnj (slp_point_as_complex (axis i 1)))))"

definition slp_right_cgo_field ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field"
where
  "slp_right_cgo_field tau c W z =
    slp_antiholomorphic_quadratic_phase_multiplier tau c z +
    slp_holomorphic_quadratic_phase_multiplier (- tau) c z * W z"

definition slp_right_cgo_gradient ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_gradient_field \<Rightarrow> slp_gradient_field"
where
  "slp_right_cgo_gradient tau c W DW z =
    (\<chi> i.
      slp_antiholomorphic_quadratic_phase_multiplier tau c z *
        (\<i> * of_real tau * cnj (slp_point_as_complex (z - c)) *
          cnj (slp_point_as_complex (axis i 1)))) +
    (\<chi> i.
      slp_holomorphic_quadratic_phase_multiplier (- tau) c z * DW z $ i +
      W z * (slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
        (\<i> * of_real (- tau) * slp_point_as_complex (z - c) *
          slp_point_as_complex (axis i 1))))"

lemma slp_cgo_fields_factorized:
  "slp_left_cgo_field tau c W z =
      slp_holomorphic_quadratic_phase_multiplier tau c z *
        (1 + slp_center_kernel (- tau) c z * W z)
    \<and>
    slp_right_cgo_field tau c Wtilde z =
      slp_antiholomorphic_quadratic_phase_multiplier tau c z *
        (1 + slp_center_kernel (- tau) c z * Wtilde z)"
proof -
  have holo_cancel:
      "slp_holomorphic_quadratic_phase_multiplier tau c z *
          slp_holomorphic_quadratic_phase_multiplier (- tau) c z = 1"
  proof -
    have negative_exponent:
        "\<i> * of_real ((- tau) / 2) *
            (slp_point_as_complex (z - c)) ^ 2 =
          - (\<i> * of_real (tau / 2) *
            (slp_point_as_complex (z - c)) ^ 2)"
      by (simp only: minus_divide_left[symmetric] of_real_minus
            mult_minus_right minus_mult_left)
    have exponent_cancel:
        "\<i> * of_real (tau / 2) *
            (slp_point_as_complex (z - c)) ^ 2 +
          \<i> * of_real ((- tau) / 2) *
            (slp_point_as_complex (z - c)) ^ 2 = 0"
      by (simp only: negative_exponent add.right_inverse)
    show ?thesis
      unfolding slp_holomorphic_quadratic_phase_multiplier_def
      by (simp only: exp_add[symmetric] exponent_cancel exp_zero)
  qed
  have anti_cancel:
      "slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z = 1"
  proof -
    have negative_exponent:
        "\<i> * of_real ((- tau) / 2) *
            cnj ((slp_point_as_complex (z - c)) ^ 2) =
          - (\<i> * of_real (tau / 2) *
            cnj ((slp_point_as_complex (z - c)) ^ 2))"
      by (simp only: minus_divide_left[symmetric] of_real_minus
            mult_minus_right minus_mult_left)
    have exponent_cancel:
        "\<i> * of_real (tau / 2) *
            cnj ((slp_point_as_complex (z - c)) ^ 2) +
          \<i> * of_real ((- tau) / 2) *
            cnj ((slp_point_as_complex (z - c)) ^ 2) = 0"
      by (simp only: negative_exponent add.right_inverse)
    show ?thesis
      unfolding slp_antiholomorphic_quadratic_phase_multiplier_def
      by (simp only: exp_add[symmetric] exponent_cancel exp_zero)
  qed
  have left_phase:
      "slp_holomorphic_quadratic_phase_multiplier tau c z *
          slp_center_kernel (- tau) c z =
        slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z"
  proof -
    have kernel:
        "slp_center_kernel (- tau) c z =
          slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
          slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z"
      by (rule sym, rule slp_quadratic_phase_multipliers_product)
    show ?thesis
      by (simp only: kernel mult.assoc[symmetric] holo_cancel
            mult.left_neutral)
  qed
  have right_phase:
      "slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          slp_center_kernel (- tau) c z =
        slp_holomorphic_quadratic_phase_multiplier (- tau) c z"
  proof -
    have kernel:
        "slp_center_kernel (- tau) c z =
          slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
          slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z"
      by (rule sym, rule slp_quadratic_phase_multipliers_product)
    have rearrange:
        "slp_antiholomorphic_quadratic_phase_multiplier tau c z *
            (slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
              slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z) =
          (slp_antiholomorphic_quadratic_phase_multiplier tau c z *
              slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z) *
              slp_holomorphic_quadratic_phase_multiplier (- tau) c z"
      by (simp only: ac_simps)
    show ?thesis
      by (simp only: kernel rearrange anti_cancel mult.left_neutral)
  qed
  have left_correction:
      "slp_holomorphic_quadratic_phase_multiplier tau c z *
          (slp_center_kernel (- tau) c z * W z) =
        slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z * W z"
    by (simp only: mult.assoc[symmetric] left_phase)
  have right_correction:
      "slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          (slp_center_kernel (- tau) c z * Wtilde z) =
        slp_holomorphic_quadratic_phase_multiplier (- tau) c z * Wtilde z"
    by (simp only: mult.assoc[symmetric] right_phase)
  have left_factorized:
      "slp_holomorphic_quadratic_phase_multiplier tau c z *
          (1 + slp_center_kernel (- tau) c z * W z) =
        slp_holomorphic_quadratic_phase_multiplier tau c z +
          slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z * W z"
    by (simp only: distrib_left mult.right_neutral left_correction)
  have right_factorized:
      "slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          (1 + slp_center_kernel (- tau) c z * Wtilde z) =
        slp_antiholomorphic_quadratic_phase_multiplier tau c z +
          slp_holomorphic_quadratic_phase_multiplier (- tau) c z * Wtilde z"
    by (simp only: distrib_left mult.right_neutral right_correction)
  have left_result:
      "slp_left_cgo_field tau c W z =
        slp_holomorphic_quadratic_phase_multiplier tau c z *
          (1 + slp_center_kernel (- tau) c z * W z)"
    unfolding slp_left_cgo_field_def
    by (rule sym, rule left_factorized)
  have right_result:
      "slp_right_cgo_field tau c Wtilde z =
        slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          (1 + slp_center_kernel (- tau) c z * Wtilde z)"
    unfolding slp_right_cgo_field_def
    by (rule sym, rule right_factorized)
  show ?thesis
    by (rule conjI[OF left_result right_result])
qed

section \<open>Affine fixed-point CGO fields in project H1\<close>

context slp_cauchy_outer_fixed_point
begin

theorem slp_both_affine_fixed_point_cgo_fields_h1:
  fixes p M_left M_right tau :: real
    and c :: slp_point
    and X :: "slp_point set"
    and cutoff coefficient W_left W_right :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and left_admissible:
      "slp_ae_bounded_measurable lborel M_left W_left"
    and right_admissible:
      "slp_ae_bounded_measurable lborel M_right W_right"
    and left_fixed:
      "AE z in lborel.
        W_left z =
          slp_restrict_field X
            (slp_left_neumann_base tau c cutoff coefficient
              SLP_Dbar_Inverse) z +
          slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient W_left) z"
    and right_fixed:
      "AE z in lborel.
        W_right z =
          slp_restrict_field X
            (slp_right_neumann_base tau c cutoff coefficient
              SLP_Partial_Inverse) z +
          slp_restrict_field X
            (slp_right_neumann_step tau c cutoff coefficient W_right) z"
  shows
    "slp_h1_pair_on X
        (slp_left_cgo_field tau c W_left)
        (slp_left_cgo_gradient tau c W_left
          (slp_left_outer_conjugated_gradient
            tau c cutoff coefficient W_left))
      \<and>
      slp_h1_pair_on X
        (slp_right_cgo_field tau c W_right)
        (slp_right_cgo_gradient tau c W_right
          (slp_right_outer_conjugated_gradient
            tau c cutoff coefficient W_right))"
proof -
  have X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    using X_open by simp
  note fixed_points = slp_both_affine_fixed_points_h1[OF
    exponent_lower exponent_upper X_open X_bounded cutoff_test coefficient_lp
    coefficient_support left_admissible right_admissible left_fixed right_fixed]
  note left_fixed_h1 = conjunct1[OF fixed_points]
  note right_fixed_h1 = conjunct2[OF fixed_points]

  have left_leading:
      "slp_h1_pair_on X
        (slp_holomorphic_quadratic_phase_multiplier tau c)
        (\<lambda>z. \<chi> i.
          slp_holomorphic_quadratic_phase_multiplier tau c z *
            (\<i> * of_real tau * slp_point_as_complex (z - c) *
              slp_point_as_complex (axis i 1)))"
    by (rule slp_h1_pair_on_holomorphic_quadratic_phase[OF
          X_measurable X_bounded])
  have left_correction:
      "slp_h1_pair_on X
        (\<lambda>z.
          slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z *
            W_left z)
        (\<lambda>z. \<chi> i.
          slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z *
              slp_left_outer_conjugated_gradient
                tau c cutoff coefficient W_left z $ i +
          W_left z *
            (slp_antiholomorphic_quadratic_phase_multiplier (- tau) c z *
              (\<i> * of_real (- tau) *
                cnj (slp_point_as_complex (z - c)) *
                cnj (slp_point_as_complex (axis i 1)))))"
    by (rule
          slp_h1_pair_on_antiholomorphic_quadratic_phase_multiplier[OF
            X_measurable X_bounded left_fixed_h1])
  have left_sum:
      "slp_h1_pair_on X
        (slp_left_cgo_field tau c W_left)
        (slp_left_cgo_gradient tau c W_left
          (slp_left_outer_conjugated_gradient
            tau c cutoff coefficient W_left))"
    unfolding slp_left_cgo_field_def slp_left_cgo_gradient_def
    by (rule slp_h1_pair_on_add[OF
          X_measurable X_bounded left_leading left_correction])

  have right_leading:
      "slp_h1_pair_on X
        (slp_antiholomorphic_quadratic_phase_multiplier tau c)
        (\<lambda>z. \<chi> i.
          slp_antiholomorphic_quadratic_phase_multiplier tau c z *
            (\<i> * of_real tau * cnj (slp_point_as_complex (z - c)) *
              cnj (slp_point_as_complex (axis i 1))))"
    by (rule slp_h1_pair_on_antiholomorphic_quadratic_phase[OF
          X_measurable X_bounded])
  have right_correction:
      "slp_h1_pair_on X
        (\<lambda>z.
          slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
            W_right z)
        (\<lambda>z. \<chi> i.
          slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
              slp_right_outer_conjugated_gradient
                tau c cutoff coefficient W_right z $ i +
          W_right z *
            (slp_holomorphic_quadratic_phase_multiplier (- tau) c z *
              (\<i> * of_real (- tau) * slp_point_as_complex (z - c) *
                slp_point_as_complex (axis i 1))))"
    by (rule slp_h1_pair_on_holomorphic_quadratic_phase_multiplier[OF
          X_measurable X_bounded right_fixed_h1])
  have right_sum:
      "slp_h1_pair_on X
        (slp_right_cgo_field tau c W_right)
        (slp_right_cgo_gradient tau c W_right
          (slp_right_outer_conjugated_gradient
            tau c cutoff coefficient W_right))"
    unfolding slp_right_cgo_field_def slp_right_cgo_gradient_def
    by (rule slp_h1_pair_on_add[OF
          X_measurable X_bounded right_leading right_correction])

  show ?thesis using left_sum right_sum by blast
qed

end

end
