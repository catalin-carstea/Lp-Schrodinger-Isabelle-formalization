theory Inverse_Schrodinger_Lp_Ratio_Power_Normalization
  imports Inverse_Schrodinger_Lp_Tail_Squeeze
begin

section \<open>Normalization of scaled Neumann-ratio powers\<close>

lemma slp_scaled_ratio_power_normalization:
  fixes tau C alpha base_exponent :: real
    and N :: nat
  assumes tau_positive: "0 < tau"
  shows
    "(tau powr base_exponent) *
        (C * (tau powr (- alpha))) ^ N =
      C ^ N *
        (tau powr (base_exponent - alpha * real N))"
proof -
  have tau_nonzero: "tau \<noteq> 0"
    using tau_positive by simp
  have phase_power:
    "(tau powr (- alpha)) ^ N =
      tau powr (real N * (- alpha))"
    by (rule powr_power[OF tau_nonzero])
  have phase_combine:
    "tau powr base_exponent *
        tau powr (real N * (- alpha)) =
      tau powr (base_exponent - alpha * real N)"
    by (subst powr_add[symmetric])
      (simp add: algebra_simps)
  have coefficient_reassociate:
    "tau powr base_exponent *
        (C ^ N * tau powr (real N * (- alpha))) =
      C ^ N *
        (tau powr base_exponent *
          tau powr (real N * (- alpha)))"
    by (simp only: mult.assoc mult.commute mult.left_commute)
  show ?thesis
    by (simp only: power_mult_distrib phase_power
        coefficient_reassociate phase_combine)
qed

corollary slp_one_sided_ratio_power_normalization:
  fixes tau C alpha s :: real
    and N :: nat
  assumes tau_positive: "0 < tau"
  shows
    "(tau powr (1 - s)) *
        (C * (tau powr (- alpha))) ^ N =
      C ^ N *
        (tau powr (1 - s - alpha * real N))"
  by (rule slp_scaled_ratio_power_normalization[OF tau_positive])

corollary slp_mixed_ratio_power_normalization:
  fixes tau C alpha s :: real
    and N :: nat
  assumes tau_positive: "0 < tau"
  shows
    "(tau powr (1 - s - alpha)) *
        (C * (tau powr (- alpha))) ^ N =
      C ^ N *
        (tau powr (1 - s - alpha - alpha * real N))"
  by (rule slp_scaled_ratio_power_normalization[OF tau_positive])

lemma slp_tail_cutoff1_nat_real:
  assumes alpha_positive: "0 < alpha"
    and s_at_most_one: "s \<le> 1"
  shows
    "real (nat (slp_tail_cutoff1 alpha s)) =
      of_int (slp_tail_cutoff1 alpha s)"
  using slp_tail_cutoff1_nonnegative[
      OF alpha_positive s_at_most_one]
  by simp

lemma slp_tail_cutoff2_nat_real:
  "real (nat (slp_tail_cutoff2 alpha s)) =
    of_int (slp_tail_cutoff2 alpha s)"
  using slp_tail_cutoff2_nonnegative[of alpha s]
  by simp

corollary slp_one_sided_cutoff_ratio_power_normalization:
  fixes tau C alpha s :: real
  assumes tau_positive: "0 < tau"
    and alpha_positive: "0 < alpha"
    and s_at_most_one: "s \<le> 1"
  shows
    "(tau powr (1 - s)) *
        (C * (tau powr (- alpha))) ^
          nat (slp_tail_cutoff1 alpha s) =
      C ^ nat (slp_tail_cutoff1 alpha s) *
        (tau powr
          (1 - s - alpha *
            of_int (slp_tail_cutoff1 alpha s)))"
  using slp_one_sided_ratio_power_normalization[
      OF tau_positive,
      where C = C and alpha = alpha and s = s
        and N = "nat (slp_tail_cutoff1 alpha s)"]
    slp_tail_cutoff1_nat_real[
      OF alpha_positive s_at_most_one]
  by simp

corollary slp_mixed_cutoff_ratio_power_normalization:
  fixes tau C alpha s :: real
  assumes tau_positive: "0 < tau"
  shows
    "(tau powr (1 - s - alpha)) *
        (C * (tau powr (- alpha))) ^
          nat (slp_tail_cutoff2 alpha s) =
      C ^ nat (slp_tail_cutoff2 alpha s) *
        (tau powr
          (1 - s - alpha - alpha *
            of_int (slp_tail_cutoff2 alpha s)))"
  using slp_mixed_ratio_power_normalization[
      OF tau_positive,
      where C = C and alpha = alpha and s = s
        and N = "nat (slp_tail_cutoff2 alpha s)"]
    slp_tail_cutoff2_nat_real[of alpha s]
  by simp

end
