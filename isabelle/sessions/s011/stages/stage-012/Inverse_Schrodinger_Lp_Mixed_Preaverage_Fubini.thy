theory Inverse_Schrodinger_Lp_Mixed_Preaverage_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Center_Support_Mass"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Absolute integration before the mixed center average\<close>

definition slp_mixed_preaverage_integrand ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_point \<Rightarrow> slp_point \<Rightarrow>
    ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
where
  "slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B phi
      target center coordinates =
    slp_center_kernel tau center target * phi target *
      slp_parameterized_real_phase_integrand tau slp_mixed_center_finite_residual
        (slp_mixed_center_finite_complex_amplitude Q left_cutoff q right_cutoff qt)
        center coordinates *
      (A (snd (fst (snd coordinates))) - A target) *
      (B (slp_mixed_center_finite_right_terminal center coordinates) - B target)"

theorem slp_center_average_terminal_difference_integral:
  fixes tau :: real and phi A B :: slp_scalar_field
    and center left_terminal right_terminal :: slp_point
  assumes phi_integrable: "integrable lborel phi"
    and phi_B_integrable: "integrable lborel (\<lambda>x. phi x * B x)"
    and phi_A_integrable: "integrable lborel (\<lambda>x. phi x * A x)"
    and phi_AB_integrable: "integrable lborel (\<lambda>x. phi x * (A x * B x))"
  shows "integrable lborel (\<lambda>x. slp_center_kernel tau center x * phi x *
      (A left_terminal - A x) * (B right_terminal - B x))"
    and "slp_mixed_center_average_bracket tau phi A B center
        left_terminal right_terminal =
      of_real (tau / pi) * integral\<^sup>L lborel
        (\<lambda>x. slp_center_kernel tau center x * phi x *
          (A left_terminal - A x) * (B right_terminal - B x))"
proof -
  let ?F0 = "\<lambda>x. slp_center_kernel tau center x * phi x"
  let ?F1 = "\<lambda>x. slp_center_kernel tau center x * (phi x * B x)"
  let ?F2 = "\<lambda>x. slp_center_kernel tau center x * (phi x * A x)"
  let ?F3 = "\<lambda>x. slp_center_kernel tau center x * (phi x * (A x * B x))"
  let ?G0 = "\<lambda>x. (A left_terminal * B right_terminal) * ?F0 x"
  let ?G1 = "\<lambda>x. A left_terminal * ?F1 x"
  let ?G2 = "\<lambda>x. B right_terminal * ?F2 x"
  have F0: "integrable lborel ?F0"
    by (rule slp_center_kernel_integrable_mult[OF phi_integrable])
  have F1: "integrable lborel ?F1"
    by (rule slp_center_kernel_integrable_mult[OF phi_B_integrable])
  have F2: "integrable lborel ?F2"
    by (rule slp_center_kernel_integrable_mult[OF phi_A_integrable])
  have F3: "integrable lborel ?F3"
    by (rule slp_center_kernel_integrable_mult[OF phi_AB_integrable])
  have G0: "integrable lborel ?G0" by (rule integrable_mult_right[OF F0])
  have G1: "integrable lborel ?G1" by (rule integrable_mult_right[OF F1])
  have G2: "integrable lborel ?G2" by (rule integrable_mult_right[OF F2])
  have D01: "integrable lborel (\<lambda>x. ?G0 x - ?G1 x)"
    by (rule Bochner_Integration.integrable_diff[OF G0 G1])
  have D012: "integrable lborel (\<lambda>x. ?G0 x - ?G1 x - ?G2 x)"
    by (rule Bochner_Integration.integrable_diff[OF D01 G2])
  have full: "integrable lborel (\<lambda>x. ?G0 x - ?G1 x - ?G2 x + ?F3 x)"
    by (rule Bochner_Integration.integrable_add[OF D012 F3])
  have expansion: "slp_center_kernel tau center x * phi x *
      (A left_terminal - A x) * (B right_terminal - B x) =
      ?G0 x - ?G1 x - ?G2 x + ?F3 x" for x
    by (simp add: algebra_simps)
  show "integrable lborel (\<lambda>x. slp_center_kernel tau center x * phi x *
      (A left_terminal - A x) * (B right_terminal - B x))"
    using full by (simp only: expansion)
  have integral_expansion: "integral\<^sup>L lborel
        (\<lambda>x. slp_center_kernel tau center x * phi x *
          (A left_terminal - A x) * (B right_terminal - B x)) =
      (A left_terminal * B right_terminal) * integral\<^sup>L lborel ?F0 -
      A left_terminal * integral\<^sup>L lborel ?F1 -
      B right_terminal * integral\<^sup>L lborel ?F2 + integral\<^sup>L lborel ?F3"
    by (simp only: expansion Bochner_Integration.integral_add[OF D012 F3]
        Bochner_Integration.integral_diff[OF D01 G2]
        Bochner_Integration.integral_diff[OF G0 G1]
        Bochner_Integration.integral_mult_right_zero)
  show "slp_mixed_center_average_bracket tau phi A B center
        left_terminal right_terminal =
      of_real (tau / pi) * integral\<^sup>L lborel
        (\<lambda>x. slp_center_kernel tau center x * phi x *
          (A left_terminal - A x) * (B right_terminal - B x))"
    by (simp only: integral_expansion slp_mixed_center_average_bracket_def
        slp_center_average_def; simp add: algebra_simps)
qed

theorem slp_mixed_preaverage_integrable:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and tau :: real
    and Q left_cutoff q A right_cutoff qt B phi :: slp_scalar_field
    and center :: slp_point
    and coordinates :: "('i, 'j) slp_mixed_center_finite_coordinates"
  assumes phi_integrable: "integrable lborel phi"
    and phi_B_integrable: "integrable lborel (\<lambda>x. phi x * B x)"
    and phi_A_integrable: "integrable lborel (\<lambda>x. phi x * A x)"
    and phi_AB_integrable: "integrable lborel (\<lambda>x. phi x * (A x * B x))"
    and weighted0_integrable: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q A right_cutoff qt B (\<lambda>_. 1) (fst y) (snd y))"
    and weighted1_integrable: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q A right_cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
    and weighted2_integrable: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B (\<lambda>_. 1) (fst y) (snd y))"
    and weighted3_integrable: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
  shows "integrable lborel (\<lambda>z :: slp_point \<times> (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates).
      slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B phi
        (fst z) (fst (snd z)) (snd (snd z)))"
    and "of_real (tau / pi) * integral\<^sup>L lborel
        (\<lambda>target. slp_mixed_preaverage_integrand tau Q left_cutoff q A
          right_cutoff qt B phi target center coordinates) =
      slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
        right_cutoff qt B phi center coordinates"
proof -
  let ?W0 = "(\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q A right_cutoff qt B (\<lambda>_. 1) (fst y) (snd y))"
  let ?W1 = "(\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q A right_cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
  let ?W2 = "(\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B (\<lambda>_. 1) (fst y) (snd y))"
  let ?W3 = "(\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
  let ?G0 = "\<lambda>z. phi (fst z) * ?W0 (snd z)"
  let ?G1 = "\<lambda>z. (phi (fst z) * B (fst z)) * ?W1 (snd z)"
  let ?G2 = "\<lambda>z. (phi (fst z) * A (fst z)) * ?W2 (snd z)"
  let ?G3 = "\<lambda>z. (phi (fst z) * (A (fst z) * B (fst z))) * ?W3 (snd z)"
  have G0: "integrable lborel ?G0"
    by (rule slp_complex_lborel_product_integral(1)[OF phi_integrable weighted0_integrable])
  have G1: "integrable lborel ?G1"
    by (rule slp_complex_lborel_product_integral(1)[OF phi_B_integrable weighted1_integrable])
  have G2: "integrable lborel ?G2"
    by (rule slp_complex_lborel_product_integral(1)[OF phi_A_integrable weighted2_integrable])
  have G3: "integrable lborel ?G3"
    by (rule slp_complex_lborel_product_integral(1)[OF phi_AB_integrable weighted3_integrable])
  let ?J = "\<lambda>z. ?G0 z - ?G1 z - ?G2 z + ?G3 z"
  have J: "integrable lborel ?J"
    by (intro Bochner_Integration.integrable_add Bochner_Integration.integrable_diff
        G0 G1 G2 G3)
  let ?K = "\<lambda>z :: slp_point \<times> (slp_point \<times>
      ('i, 'j) slp_mixed_center_finite_coordinates).
      slp_center_kernel tau (fst (snd z)) (fst z)"
  have K_continuous: "continuous_on UNIV ?K"
    unfolding slp_center_kernel_def slp_center_phase_def
    by (intro continuous_intros)
  have K_measurable: "?K \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF K_continuous] by simp
  have phased_integrable: "integrable lborel (\<lambda>z. ?K z * ?J z)"
  proof (rule Bochner_Integration.integrable_bound[OF J])
    show "(\<lambda>z. ?K z * ?J z) \<in> borel_measurable lborel"
      using K_measurable J by measurable
    show "AE z in lborel. norm (?K z * ?J z) \<le> norm (?J z)"
      by (simp add: norm_mult)
  qed
  have expanded:
      "slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B phi
        (fst z) (fst (snd z)) (snd (snd z)) = ?K z * ?J z" for z
    by (simp add: slp_mixed_preaverage_integrand_def
        slp_mixed_weighted_integrand_terminal_factor algebra_simps)
  show "integrable lborel (\<lambda>z :: slp_point \<times> (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates).
      slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B phi
        (fst z) (fst (snd z)) (snd (snd z)))"
    using phased_integrable by (simp only: expanded)
  let ?phase = "slp_parameterized_real_phase_integrand tau slp_mixed_center_finite_residual
    (slp_mixed_center_finite_complex_amplitude Q left_cutoff q right_cutoff qt)
    center coordinates"
  let ?s = "snd (fst (snd coordinates))"
  let ?t = "slp_mixed_center_finite_right_terminal center coordinates"
  have factor:
      "slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B phi
        target center coordinates =
      ?phase * (slp_center_kernel tau center target * phi target *
        (A ?s - A target) * (B ?t - B target))" for target
    by (simp add: slp_mixed_preaverage_integrand_def algebra_simps)
  have scalar:
      "slp_mixed_center_average_bracket tau phi A B center ?s ?t =
        of_real (tau / pi) * integral\<^sup>L lborel
          (\<lambda>x. slp_center_kernel tau center x * phi x *
            (A ?s - A x) * (B ?t - B x))"
    by (rule slp_center_average_terminal_difference_integral(2)[OF
        phi_integrable phi_B_integrable phi_A_integrable phi_AB_integrable])
  show "of_real (tau / pi) * integral\<^sup>L lborel
        (\<lambda>target. slp_mixed_preaverage_integrand tau Q left_cutoff q A
          right_cutoff qt B phi target center coordinates) =
      slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
        right_cutoff qt B phi center coordinates"
    by (simp only: factor Bochner_Integration.integral_mult_right_zero
        slp_mixed_center_finite_bracket_integrand_def scalar; simp add: algebra_simps)
qed

theorem slp_mixed_preaverage_bracket_fubini:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and tau :: real
    and Q left_cutoff q A right_cutoff qt B phi :: slp_scalar_field
  assumes phi_integrable: "integrable lborel phi"
    and phi_B_integrable: "integrable lborel (\<lambda>x. phi x * B x)"
    and phi_A_integrable: "integrable lborel (\<lambda>x. phi x * A x)"
    and phi_AB_integrable: "integrable lborel (\<lambda>x. phi x * (A x * B x))"
    and weighted0_integrable: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q A right_cutoff qt B (\<lambda>_. 1) (fst y) (snd y))"
    and weighted1_integrable: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q A right_cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
    and weighted2_integrable: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B (\<lambda>_. 1) (fst y) (snd y))"
    and weighted3_integrable: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
  shows "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
      right_cutoff qt B phi (fst y) (snd y))"
    and "of_real (tau / pi) * integral\<^sup>L lborel
      (\<lambda>target. integral\<^sup>L lborel
        (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
          slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B phi target (fst y) (snd y))) =
      integral\<^sup>L lborel
        (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
          Q left_cutoff q A right_cutoff qt B phi)"
proof -
  let ?F = "\<lambda>target (y :: slp_point \<times>
      ('i, 'j) slp_mixed_center_finite_coordinates).
      slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B phi target (fst y) (snd y)"
  let ?J = "(\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
      right_cutoff qt B phi (fst y) (snd y))"
  let ?k = "of_real (tau / pi) :: complex"
  have joint: "integrable lborel (\<lambda>z :: slp_point \<times> (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates).
      slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B phi
        (fst z) (fst (snd z)) (snd (snd z)))"
    by (rule slp_mixed_preaverage_integrable(1)[OF phi_integrable phi_B_integrable phi_A_integrable phi_AB_integrable
        weighted0_integrable weighted1_integrable weighted2_integrable weighted3_integrable])
  have product: "integrable ((lborel :: slp_point measure) \<Otimes>\<^sub>M
      (lborel :: (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates) measure))
      (case_prod ?F)"
    using joint by (simp only: lborel_prod split_beta')
  have fiber: "?k * integral\<^sup>L lborel (\<lambda>target. ?F target y) = ?J y" for y
    by (rule slp_mixed_preaverage_integrable(2)[OF phi_integrable phi_B_integrable phi_A_integrable phi_AB_integrable
        weighted0_integrable weighted1_integrable weighted2_integrable weighted3_integrable])
  have outer: "integrable lborel (\<lambda>y. integral\<^sup>L lborel (\<lambda>target. ?F target y))"
    by (rule lborel_pair.integrable_snd[OF product])
  have scaled: "integrable lborel (\<lambda>y. ?k *
      integral\<^sup>L lborel (\<lambda>target. ?F target y))"
    by (rule integrable_mult_right[OF outer])
  have J_integrable: "integrable lborel ?J"
    using scaled by (simp only: fiber)
  show "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
      right_cutoff qt B phi (fst y) (snd y))" by (rule J_integrable)
  have exchange:
      "integral\<^sup>L lborel (\<lambda>target. integral\<^sup>L lborel (?F target)) =
       integral\<^sup>L lborel (\<lambda>y. integral\<^sup>L lborel (\<lambda>target. ?F target y))"
    by (rule sym[OF lborel_pair.Fubini_integral[OF product]])
  have target_to_joint:
      "?k * integral\<^sup>L lborel (\<lambda>target. integral\<^sup>L lborel (?F target)) =
        integral\<^sup>L lborel ?J"
  proof -
    have "?k * integral\<^sup>L lborel (\<lambda>target. integral\<^sup>L lborel (?F target)) =
        integral\<^sup>L lborel (\<lambda>y. ?k *
          integral\<^sup>L lborel (\<lambda>target. ?F target y))"
      by (simp only: exchange Bochner_Integration.integral_mult_right_zero)
    also have "... = integral\<^sup>L lborel ?J" by (simp only: fiber)
    finally show ?thesis .
  qed
  have J_product: "integrable ((lborel :: slp_point measure) \<Otimes>\<^sub>M
      (lborel :: ('i, 'j) slp_mixed_center_finite_coordinates measure)) ?J"
    using J_integrable by (simp only: lborel_prod)
  have kernel_function:
      "slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
        Q left_cutoff q A right_cutoff qt B phi =
       (\<lambda>center. integral\<^sup>L lborel
         (\<lambda>coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates.
           slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
             right_cutoff qt B phi center coordinates))"
    by (rule ext) (simp only: slp_mixed_center_finite_bracket_kernel_def)
  have joint_to_kernel:
      "integral\<^sup>L lborel ?J = integral\<^sup>L lborel
        (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
          Q left_cutoff q A right_cutoff qt B phi)"
    using lborel_pair.integral_fst'[OF J_product, symmetric]
    by (simp only: lborel_prod fst_conv snd_conv kernel_function)
  show "of_real (tau / pi) * integral\<^sup>L lborel
      (\<lambda>target. integral\<^sup>L lborel
        (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
          slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B phi target (fst y) (snd y))) =
      integral\<^sup>L lborel
        (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
          Q left_cutoff q A right_cutoff qt B phi)"
    by (rule trans[OF target_to_joint joint_to_kernel])
qed

end
