theory Inverse_Schrodinger_Lp_Common_CGO_Scalar_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Tested_Remainder_Package"
begin

section \<open>Fixed-order decay of the common-CGO scalar envelope\<close>

definition slp_common_cgo_scalar_prefix ::
    "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where
  "slp_common_cgo_scalar_prefix C CV alpha tau =
    C * tau powr (- alpha) / (1 - CV * tau powr (- alpha))"

definition slp_common_cgo_scalar_tail ::
    "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where
  "slp_common_cgo_scalar_tail N C CV alpha tau =
    slp_common_cgo_scalar_prefix C CV alpha tau *
      (CV * tau powr (- alpha)) ^ N"

definition slp_common_cgo_outer_scalar_majorant ::
    "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
      real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where
  "slp_common_cgo_outer_scalar_majorant
      N M alpha C_left CV_left C_right CV_right tau =
    tau *
      (slp_common_cgo_scalar_tail N C_left CV_left alpha tau +
       slp_common_cgo_scalar_tail M C_right CV_right alpha tau +
       slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
         slp_common_cgo_scalar_tail M C_right CV_right alpha tau +
       slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
         slp_common_cgo_scalar_prefix C_right CV_right alpha tau +
       slp_common_cgo_scalar_tail N C_left CV_left alpha tau *
         slp_common_cgo_scalar_tail M C_right CV_right alpha tau)"

lemma slp_common_cgo_scalar_prefix_tendsto_zero:
  fixes C CV alpha :: real
  assumes alpha_positive: "0 < alpha"
  shows
    "((slp_common_cgo_scalar_prefix C CV alpha) \<longlongrightarrow> 0) at_top"
proof -
  have power_limit:
      "((\<lambda>tau :: real. tau powr (- alpha)) \<longlongrightarrow> 0) at_top"
    by (rule slp_negative_powr_at_top) (use alpha_positive in simp)
  have numerator_limit:
      "((\<lambda>tau :: real. C * tau powr (- alpha)) \<longlongrightarrow> 0) at_top"
    using tendsto_mult_left[OF power_limit, of C] by simp
  have ratio_limit:
      "((\<lambda>tau :: real. CV * tau powr (- alpha)) \<longlongrightarrow> 0) at_top"
    using tendsto_mult_left[OF power_limit, of CV] by simp
  have denominator_limit:
      "((\<lambda>tau :: real. 1 - CV * tau powr (- alpha)) \<longlongrightarrow> 1) at_top"
    using tendsto_diff[OF tendsto_const ratio_limit] by simp
  show ?thesis
    unfolding slp_common_cgo_scalar_prefix_def
    using tendsto_divide[OF numerator_limit denominator_limit] by simp
qed

lemma slp_common_cgo_scalar_tail_tendsto_zero:
  fixes C CV alpha :: real
    and N :: nat
  assumes alpha_positive: "0 < alpha"
  shows
    "((slp_common_cgo_scalar_tail N C CV alpha) \<longlongrightarrow> 0) at_top"
proof -
  have prefix_limit:
      "((slp_common_cgo_scalar_prefix C CV alpha) \<longlongrightarrow> 0) at_top"
    by (rule slp_common_cgo_scalar_prefix_tendsto_zero[OF alpha_positive])
  have ratio_limit:
      "((\<lambda>tau :: real. CV * tau powr (- alpha)) \<longlongrightarrow> 0) at_top"
    by (rule slp_neumann_ratio_tendsto_zero[OF alpha_positive])
  have power_limit:
      "((\<lambda>tau :: real. (CV * tau powr (- alpha)) ^ N)
        \<longlongrightarrow> 0 ^ N) at_top"
    by (rule tendsto_power[OF ratio_limit])
  show ?thesis
    unfolding slp_common_cgo_scalar_tail_def
    using tendsto_mult[OF prefix_limit power_limit] by simp
qed

lemma slp_common_cgo_outer_scalar_tail_tendsto_zero:
  fixes C CV alpha :: real
  assumes alpha_positive: "0 < alpha"
    and alpha_at_most_one: "alpha \<le> 1"
    and CV_nonnegative: "0 \<le> CV"
  defines "N \<equiv> nat (slp_tail_cutoff1 alpha alpha)"
  shows
    "((\<lambda>tau :: real.
        tau * slp_common_cgo_scalar_tail N C CV alpha tau)
      \<longlongrightarrow> 0) at_top"
proof -
  let ?rho = "\<lambda>tau :: real. CV * tau powr (- alpha)"
  have ratio_interval:
      "eventually
        (\<lambda>tau :: real.
          0 < tau \<and> 0 \<le> ?rho tau \<and> ?rho tau \<le> 1 / 2)
        at_top"
    by (rule slp_neumann_ratio_eventually_half[
          OF alpha_positive CV_nonnegative])
  have eventual_identity:
      "eventually
        (\<lambda>tau :: real.
          tau * slp_common_cgo_scalar_tail N C CV alpha tau =
            C * slp_one_sided_model_tail CV alpha alpha tau)
        at_top"
    using ratio_interval
  proof eventually_elim
    case (elim tau)
    have tau_positive: "0 < tau"
      using elim by blast
    have rho_nonnegative: "0 \<le> ?rho tau"
      using elim by blast
    have rho_half: "?rho tau \<le> 1 / 2"
      using elim by blast
    have rho_norm: "norm (?rho tau) < 1"
      using rho_nonnegative rho_half
      by (simp add: real_norm_def abs_of_nonneg; linarith)
    have geometric_identity:
        "slp_geometric_tail (?rho tau) N =
          (?rho tau) ^ N / (1 - ?rho tau)"
      by (rule slp_geometric_tail_identity[OF rho_norm])
    have scale_start:
        "tau * tau powr (- alpha) =
          tau powr 1 * tau powr (- alpha)"
      using tau_positive by simp
    also have "... = tau powr (1 + (- alpha))"
      by (rule powr_add[symmetric])
    also have "... = tau powr (1 - alpha)"
      by simp
    finally have scale_identity:
        "tau * tau powr (- alpha) = tau powr (1 - alpha)" .
    show ?case
    proof -
      have first:
          "tau * slp_common_cgo_scalar_tail N C CV alpha tau =
            C * ((tau * tau powr (- alpha)) *
              ((?rho tau) ^ N / (1 - ?rho tau)))"
        unfolding slp_common_cgo_scalar_tail_def
          slp_common_cgo_scalar_prefix_def
        by (simp only: divide_inverse; simp add: ac_simps)
      also have "... =
          C * (tau powr (1 - alpha) *
            ((?rho tau) ^ N / (1 - ?rho tau)))"
        by (simp only: scale_identity)
      also have "... =
          C * slp_one_sided_model_tail CV alpha alpha tau"
        unfolding slp_one_sided_model_tail_def
        using geometric_identity
        by (simp only: N_def)
      finally show ?thesis .
    qed
  qed
  have model_limit:
      "((slp_one_sided_model_tail CV alpha alpha) \<longlongrightarrow> 0) at_top"
    by (rule slp_one_sided_model_tail_tendsto_zero[
          OF alpha_positive CV_nonnegative alpha_at_most_one])
  have scaled_model_limit:
      "((\<lambda>tau. C * slp_one_sided_model_tail CV alpha alpha tau)
        \<longlongrightarrow> 0) at_top"
    using tendsto_mult_left[OF model_limit, of C] by simp
  show ?thesis
    by (rule tendsto_cong[OF eventual_identity, THEN iffD2,
          OF scaled_model_limit])
qed

theorem slp_common_cgo_outer_scalar_majorant_tendsto_zero:
  fixes alpha C_left CV_left C_right CV_right :: real
  assumes alpha_positive: "0 < alpha"
    and alpha_at_most_one: "alpha \<le> 1"
    and CV_left_nonnegative: "0 \<le> CV_left"
    and CV_right_nonnegative: "0 \<le> CV_right"
  defines "N \<equiv> nat (slp_tail_cutoff1 alpha alpha)"
  shows
    "((slp_common_cgo_outer_scalar_majorant
        N N alpha C_left CV_left C_right CV_right)
      \<longlongrightarrow> 0) at_top"
proof -
  have prefix_left:
      "((slp_common_cgo_scalar_prefix C_left CV_left alpha)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_common_cgo_scalar_prefix_tendsto_zero[OF alpha_positive])
  have prefix_right:
      "((slp_common_cgo_scalar_prefix C_right CV_right alpha)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_common_cgo_scalar_prefix_tendsto_zero[OF alpha_positive])
  have tail_left:
      "((slp_common_cgo_scalar_tail N C_left CV_left alpha)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_common_cgo_scalar_tail_tendsto_zero[OF alpha_positive])
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
          (tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau))
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
  have sum_two:
      "((\<lambda>tau :: real.
          tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau +
          tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau)
        \<longlongrightarrow> 0) at_top"
    using tendsto_add[OF outer_tail_left outer_tail_right] by simp
  have sum_three:
      "((\<lambda>tau :: real.
          tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau +
          tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau +
          slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
            (tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau))
        \<longlongrightarrow> 0) at_top"
    using tendsto_add[OF sum_two cross_left_right] by simp
  have sum_four:
      "((\<lambda>tau :: real.
          tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau +
          tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau +
          slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
            (tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau) +
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_prefix C_right CV_right alpha tau)
        \<longlongrightarrow> 0) at_top"
    using tendsto_add[OF sum_three cross_right_left] by simp
  have distributed_limit:
      "((\<lambda>tau :: real.
          tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau +
          tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau +
          slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
            (tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau) +
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_prefix C_right CV_right alpha tau +
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_tail N C_right CV_right alpha tau)
        \<longlongrightarrow> 0) at_top"
    using tendsto_add[OF sum_four cross_tail_tail] by simp
  have envelope_identity:
      "slp_common_cgo_outer_scalar_majorant
          N N alpha C_left CV_left C_right CV_right =
        (\<lambda>tau :: real.
          tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau +
          tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau +
          slp_common_cgo_scalar_prefix C_left CV_left alpha tau *
            (tau * slp_common_cgo_scalar_tail N C_right CV_right alpha tau) +
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_prefix C_right CV_right alpha tau +
          (tau * slp_common_cgo_scalar_tail N C_left CV_left alpha tau) *
            slp_common_cgo_scalar_tail N C_right CV_right alpha tau)"
    by (simp add: slp_common_cgo_outer_scalar_majorant_def
          fun_eq_iff algebra_simps)
  show ?thesis
    unfolding envelope_identity
    by (rule distributed_limit)
qed

end
