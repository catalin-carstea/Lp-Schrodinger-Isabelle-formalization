theory Inverse_Schrodinger_Lp_Common_CGO_Scalar_Center_Integral_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Scalar_Decay"
begin

section \<open>Fixed-center integral lift of the common-CGO scalar decay\<close>

definition slp_common_cgo_scalar_center_majorant ::
    "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
      real \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow>
      ('a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
  where
  "slp_common_cgo_scalar_center_majorant
      N M alpha C_left CV_left C_right CV_right
      weight left_factor right_factor tau x =
    slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
        (weight x * left_factor x) +
    slp_common_cgo_scalar_tail M C_right CV_right alpha tau *
        (weight x * right_factor x) +
    (slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
      slp_common_cgo_scalar_tail M C_right CV_right alpha tau) *
        (weight x * left_factor x * right_factor x) +
    (slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
      slp_common_cgo_scalar_prefix C_right CV_right alpha tau) *
        (weight x * left_factor x * right_factor x) +
    (slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
      slp_common_cgo_scalar_tail M C_right CV_right alpha tau) *
        (weight x * left_factor x * right_factor x)"

lemma slp_common_cgo_scalar_center_majorant_integral_expansion:
  fixes mu :: "'a measure"
  assumes left_integrable:
      "integrable mu (\<lambda>x. weight x * left_factor x)"
    and right_integrable:
      "integrable mu (\<lambda>x. weight x * right_factor x)"
    and cross_integrable:
      "integrable mu
        (\<lambda>x. weight x * left_factor x * right_factor x)"
  shows
    "integral\<^sup>L mu
        (slp_common_cgo_scalar_center_majorant
          N M alpha C_left CV_left C_right CV_right
          weight left_factor right_factor tau) =
      slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
          integral\<^sup>L mu (\<lambda>x. weight x * left_factor x) +
      slp_common_cgo_scalar_tail M C_right CV_right alpha tau *
          integral\<^sup>L mu (\<lambda>x. weight x * right_factor x) +
      (slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
        slp_common_cgo_scalar_tail M C_right CV_right alpha tau) *
          integral\<^sup>L mu
            (\<lambda>x. weight x * left_factor x * right_factor x) +
      (slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
        slp_common_cgo_scalar_prefix C_right CV_right alpha tau) *
          integral\<^sup>L mu
            (\<lambda>x. weight x * left_factor x * right_factor x) +
      (slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
        slp_common_cgo_scalar_tail M C_right CV_right alpha tau) *
          integral\<^sup>L mu
            (\<lambda>x. weight x * left_factor x * right_factor x)"
proof -
  let ?left = "\<lambda>x. weight x * left_factor x"
  let ?right = "\<lambda>x. weight x * right_factor x"
  let ?cross = "\<lambda>x. weight x * left_factor x * right_factor x"
  let ?a = "slp_common_cgo_scalar_tail N C_left CV_left alpha tau"
  let ?b = "slp_common_cgo_scalar_tail M C_right CV_right alpha tau"
  let ?c =
    "slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
      slp_common_cgo_scalar_tail M C_right CV_right alpha tau"
  let ?d =
    "slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
      slp_common_cgo_scalar_prefix C_right CV_right alpha tau"
  let ?e =
    "slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
      slp_common_cgo_scalar_tail M C_right CV_right alpha tau"
  have term_a_integrable: "integrable mu (\<lambda>x. ?a * ?left x)"
    by (rule Bochner_Integration.integrable_mult_right)
      (use left_integrable in simp)
  have term_b_integrable: "integrable mu (\<lambda>x. ?b * ?right x)"
    by (rule Bochner_Integration.integrable_mult_right)
      (use right_integrable in simp)
  have term_c_integrable: "integrable mu (\<lambda>x. ?c * ?cross x)"
    by (rule Bochner_Integration.integrable_mult_right)
      (use cross_integrable in simp)
  have term_d_integrable: "integrable mu (\<lambda>x. ?d * ?cross x)"
    by (rule Bochner_Integration.integrable_mult_right)
      (use cross_integrable in simp)
  have term_e_integrable: "integrable mu (\<lambda>x. ?e * ?cross x)"
    by (rule Bochner_Integration.integrable_mult_right)
      (use cross_integrable in simp)
  have sum_two_integrable:
      "integrable mu (\<lambda>x. ?a * ?left x + ?b * ?right x)"
    by (rule Bochner_Integration.integrable_add[OF
          term_a_integrable term_b_integrable])
  have sum_three_integrable:
      "integrable mu
        (\<lambda>x. ?a * ?left x + ?b * ?right x + ?c * ?cross x)"
    by (rule Bochner_Integration.integrable_add[OF
          sum_two_integrable term_c_integrable])
  have sum_four_integrable:
      "integrable mu
        (\<lambda>x.
          ?a * ?left x + ?b * ?right x + ?c * ?cross x +
            ?d * ?cross x)"
    by (rule Bochner_Integration.integrable_add[OF
          sum_three_integrable term_d_integrable])
  show ?thesis
    unfolding slp_common_cgo_scalar_center_majorant_def
    apply (subst Bochner_Integration.integral_add[OF
          sum_four_integrable term_e_integrable])
    apply (subst Bochner_Integration.integral_add[OF
          sum_three_integrable term_d_integrable])
    apply (subst Bochner_Integration.integral_add[OF
          sum_two_integrable term_c_integrable])
    apply (subst Bochner_Integration.integral_add[OF
          term_a_integrable term_b_integrable])
    by (simp only: Bochner_Integration.integral_mult_right_zero)
qed

theorem slp_common_cgo_outer_scalar_center_integral_tendsto_zero:
  fixes mu :: "'a measure"
    and alpha C_left CV_left C_right CV_right :: real
  assumes alpha_positive: "0 < alpha"
    and alpha_at_most_one: "alpha \<le> 1"
    and CV_left_nonnegative: "0 \<le> CV_left"
    and CV_right_nonnegative: "0 \<le> CV_right"
    and left_integrable:
      "integrable mu (\<lambda>x. weight x * left_factor x)"
    and right_integrable:
      "integrable mu (\<lambda>x. weight x * right_factor x)"
    and cross_integrable:
      "integrable mu
        (\<lambda>x. weight x * left_factor x * right_factor x)"
  defines "N \<equiv> nat (slp_tail_cutoff1 alpha alpha)"
  shows
    "((\<lambda>tau :: real.
        tau * integral\<^sup>L mu
          (slp_common_cgo_scalar_center_majorant
            N N alpha C_left CV_left C_right CV_right
            weight left_factor right_factor tau))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?I_left = "integral\<^sup>L mu (\<lambda>x. weight x * left_factor x)"
  let ?I_right = "integral\<^sup>L mu (\<lambda>x. weight x * right_factor x)"
  let ?I_cross =
    "integral\<^sup>L mu
      (\<lambda>x. weight x * left_factor x * right_factor x)"
  have prefix_left:
      "((slp_common_cgo_scalar_prefix C_left CV_left alpha)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_common_cgo_scalar_prefix_tendsto_zero[OF alpha_positive])
  have prefix_right:
      "((slp_common_cgo_scalar_prefix C_right CV_right alpha)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_common_cgo_scalar_prefix_tendsto_zero[OF alpha_positive])
  have tail_right:
      "((slp_common_cgo_scalar_tail N C_right CV_right alpha)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_common_cgo_scalar_tail_tendsto_zero[OF alpha_positive])
  have outer_tail_left:
      "((\<lambda>tau :: real.
          tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau)
        \<longlongrightarrow> 0) at_top"
    unfolding N_def
    by (rule slp_common_cgo_outer_scalar_tail_tendsto_zero[
          OF alpha_positive alpha_at_most_one CV_left_nonnegative])
  have outer_tail_right:
      "((\<lambda>tau :: real.
          tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau)
        \<longlongrightarrow> 0) at_top"
    unfolding N_def
    by (rule slp_common_cgo_outer_scalar_tail_tendsto_zero[
          OF alpha_positive alpha_at_most_one CV_right_nonnegative])
  have cross_left_right:
      "((\<lambda>tau :: real.
          slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
            (tau *
              slp_common_cgo_scalar_tail N C_right CV_right alpha tau))
        \<longlongrightarrow> 0) at_top"
    using tendsto_mult[OF prefix_left outer_tail_right] by simp
  have cross_right_left:
      "((\<lambda>tau :: real.
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_prefix C_right CV_right alpha tau)
        \<longlongrightarrow> 0) at_top"
    using tendsto_mult[OF outer_tail_left prefix_right] by simp
  have cross_tail_tail:
      "((\<lambda>tau :: real.
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_tail N C_right CV_right alpha tau)
        \<longlongrightarrow> 0) at_top"
    using tendsto_mult[OF outer_tail_left tail_right] by simp
  have left_term:
      "((\<lambda>tau :: real.
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            ?I_left)
        \<longlongrightarrow> 0) at_top"
    using tendsto_mult_right[OF outer_tail_left, of ?I_left] by simp
  have right_term:
      "((\<lambda>tau :: real.
          (tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
            ?I_right)
        \<longlongrightarrow> 0) at_top"
    using tendsto_mult_right[OF outer_tail_right, of ?I_right] by simp
  have left_right_term:
      "((\<lambda>tau :: real.
          (slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
            (tau *
              slp_common_cgo_scalar_tail N C_right CV_right alpha tau)) *
            ?I_cross)
        \<longlongrightarrow> 0) at_top"
    using tendsto_mult_right[OF cross_left_right, of ?I_cross] by simp
  have right_left_term:
      "((\<lambda>tau :: real.
          ((tau *
              slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_prefix C_right CV_right alpha tau) *
            ?I_cross)
        \<longlongrightarrow> 0) at_top"
    using tendsto_mult_right[OF cross_right_left, of ?I_cross] by simp
  have tail_tail_term:
      "((\<lambda>tau :: real.
          ((tau *
              slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
            ?I_cross)
        \<longlongrightarrow> 0) at_top"
    using tendsto_mult_right[OF cross_tail_tail, of ?I_cross] by simp
  have sum_two:
      "((\<lambda>tau :: real.
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
              ?I_left +
          (tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
              ?I_right)
        \<longlongrightarrow> 0) at_top"
    using tendsto_add[OF left_term right_term] by simp
  have sum_three:
      "((\<lambda>tau :: real.
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
              ?I_left +
          (tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
              ?I_right +
          (slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
            (tau *
              slp_common_cgo_scalar_tail N C_right CV_right alpha tau)) *
              ?I_cross)
        \<longlongrightarrow> 0) at_top"
    using tendsto_add[OF sum_two left_right_term] by simp
  have sum_four:
      "((\<lambda>tau :: real.
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
              ?I_left +
          (tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
              ?I_right +
          (slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
            (tau *
              slp_common_cgo_scalar_tail N C_right CV_right alpha tau)) *
              ?I_cross +
          ((tau *
              slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_prefix C_right CV_right alpha tau) *
              ?I_cross)
        \<longlongrightarrow> 0) at_top"
    using tendsto_add[OF sum_three right_left_term] by simp
  have distributed_limit:
      "((\<lambda>tau :: real.
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
              ?I_left +
          (tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
              ?I_right +
          (slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
            (tau *
              slp_common_cgo_scalar_tail N C_right CV_right alpha tau)) *
              ?I_cross +
          ((tau *
              slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_prefix C_right CV_right alpha tau) *
              ?I_cross +
          ((tau *
              slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
              ?I_cross)
        \<longlongrightarrow> 0) at_top"
    using tendsto_add[OF sum_four tail_tail_term] by simp
  have integral_expansion:
      "integral\<^sup>L mu
          (slp_common_cgo_scalar_center_majorant
            N N alpha C_left CV_left C_right CV_right
            weight left_factor right_factor tau) =
        slp_common_cgo_scalar_tail N C_left CV_left alpha tau * ?I_left +
        slp_common_cgo_scalar_tail N C_right CV_right alpha tau * ?I_right +
        (slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
          slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
            ?I_cross +
        (slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
          slp_common_cgo_scalar_prefix C_right CV_right alpha tau) *
            ?I_cross +
        (slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
          slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
            ?I_cross"
    for tau
    by (rule slp_common_cgo_scalar_center_majorant_integral_expansion[
          OF left_integrable right_integrable cross_integrable])
  have envelope_identity:
      "(\<lambda>tau :: real.
          tau * integral\<^sup>L mu
            (slp_common_cgo_scalar_center_majorant
              N N alpha C_left CV_left C_right CV_right
              weight left_factor right_factor tau)) =
        (\<lambda>tau :: real.
            (tau *
              slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
                ?I_left +
            (tau *
              slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
                ?I_right +
            (slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
              (tau *
                slp_common_cgo_scalar_tail N C_right CV_right alpha tau)) *
                ?I_cross +
            ((tau *
                slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
              slp_common_cgo_scalar_prefix C_right CV_right alpha tau) *
                ?I_cross +
            ((tau *
                slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
              slp_common_cgo_scalar_tail N C_right CV_right alpha tau) *
                ?I_cross)"
    by (simp add: fun_eq_iff integral_expansion algebra_simps)
  show ?thesis
    unfolding envelope_identity
    by (rule distributed_limit)
qed

end
