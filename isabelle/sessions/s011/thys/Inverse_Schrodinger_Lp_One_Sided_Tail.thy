theory Inverse_Schrodinger_Lp_One_Sided_Tail
  imports Inverse_Schrodinger_Lp_Ratio_Power_Normalization
begin

section \<open>Modeled one-sided Neumann-tail convergence\<close>

definition slp_one_sided_model_tail ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
where
  "slp_one_sided_model_tail C alpha s tau =
    (tau powr (1 - s)) *
      slp_geometric_tail
        (C * (tau powr (- alpha)))
        (nat (slp_tail_cutoff1 alpha s))"

lemma slp_neumann_ratio_tendsto_zero:
  fixes C alpha :: real
  assumes alpha_positive: "0 < alpha"
  shows
    "((\<lambda>tau :: real. C * (tau powr (- alpha)))
      \<longlongrightarrow> 0) at_top"
  by (rule slp_real_constant_negative_powr_at_top)
    (use alpha_positive in simp)

lemma slp_neumann_ratio_eventually_half:
  fixes C alpha :: real
  assumes alpha_positive: "0 < alpha"
    and C_nonnegative: "0 \<le> C"
  shows
    "eventually
      (\<lambda>tau :: real.
        0 < tau \<and>
        0 \<le> C * (tau powr (- alpha)) \<and>
        C * (tau powr (- alpha)) \<le> 1 / 2)
      at_top"
proof -
  have ratio_limit:
    "((\<lambda>tau :: real. C * (tau powr (- alpha)))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_neumann_ratio_tendsto_zero[OF alpha_positive])
  have ratio_small:
    "eventually
      (\<lambda>tau :: real.
        dist (C * (tau powr (- alpha))) 0 < 1 / 2)
      at_top"
    by (rule tendstoD[OF ratio_limit]) simp
  have tau_positive:
    "eventually (\<lambda>tau :: real. 0 < tau) at_top"
    by simp
  from tau_positive ratio_small show ?thesis
  proof eventually_elim
    case (elim tau)
    have ratio_nonnegative:
      "0 \<le> C * (tau powr (- alpha))"
      by (rule mult_nonneg_nonneg[OF C_nonnegative]) simp
    have ratio_half:
      "C * (tau powr (- alpha)) \<le> 1 / 2"
      using elim(2) ratio_nonnegative
      by (simp add: dist_real_def abs_of_nonneg)
    show ?case
      using elim(1) ratio_nonnegative ratio_half by blast
  qed
qed

theorem slp_one_sided_model_tail_tendsto_zero:
  fixes C alpha s :: real
  assumes alpha_positive: "0 < alpha"
    and C_nonnegative: "0 \<le> C"
    and s_at_most_one: "s \<le> 1"
  shows
    "((slp_one_sided_model_tail C alpha s)
      \<longlongrightarrow> 0) at_top"
proof -
  let ?N = "nat (slp_tail_cutoff1 alpha s)"
  let ?rho = "\<lambda>tau :: real. C * (tau powr (- alpha))"
  have ratio_interval:
    "eventually
      (\<lambda>tau :: real.
        0 < tau \<and> 0 \<le> ?rho tau \<and> ?rho tau \<le> 1 / 2)
      at_top"
    by (rule slp_neumann_ratio_eventually_half[
          OF alpha_positive C_nonnegative])
  have tail_nonnegative:
    "eventually
      (\<lambda>tau. 0 \<le> slp_one_sided_model_tail C alpha s tau)
      at_top"
    using ratio_interval
  proof eventually_elim
    case (elim tau)
    have rho_nonnegative: "0 \<le> ?rho tau"
      using elim by blast
    have rho_half: "?rho tau \<le> 1 / 2"
      using elim by blast
    have rho_norm: "norm (?rho tau) < 1"
      using rho_nonnegative rho_half
      by (simp add: real_norm_def abs_of_nonneg; linarith)
    have denominator_positive: "0 < 1 - ?rho tau"
      using rho_half by linarith
    have geometric_nonnegative:
      "0 \<le> slp_geometric_tail (?rho tau) ?N"
    proof -
      have quotient_nonnegative:
        "0 \<le> (?rho tau) ^ ?N / (1 - ?rho tau)"
        by (rule divide_nonneg_pos[
              OF zero_le_power[OF rho_nonnegative]
                denominator_positive])
      show ?thesis
        using slp_geometric_tail_identity[OF rho_norm, of ?N]
          quotient_nonnegative
        by simp
    qed
    show ?case
      unfolding slp_one_sided_model_tail_def
      by (rule mult_nonneg_nonneg) (simp_all add: geometric_nonnegative)
  qed
  have tail_bound:
    "eventually
      (\<lambda>tau.
        slp_one_sided_model_tail C alpha s tau \<le>
          (2 * C ^ ?N) *
            (tau powr
              (1 - s - alpha *
                of_int (slp_tail_cutoff1 alpha s))))
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
    have outside_nonnegative: "0 \<le> tau powr (1 - s)"
      by simp
    have geometric_bound:
      "slp_geometric_tail (?rho tau) ?N \<le>
        2 * (?rho tau) ^ ?N"
      by (rule slp_geometric_tail_le_twice[
            OF rho_nonnegative rho_half])
    have scaled_bound:
      "(tau powr (1 - s)) *
          slp_geometric_tail (?rho tau) ?N \<le>
        (tau powr (1 - s)) * (2 * (?rho tau) ^ ?N)"
      by (rule mult_left_mono[OF geometric_bound outside_nonnegative])
    have normalized:
      "(tau powr (1 - s)) * (?rho tau) ^ ?N =
        C ^ ?N *
          (tau powr
            (1 - s - alpha *
              of_int (slp_tail_cutoff1 alpha s)))"
      by (rule slp_one_sided_cutoff_ratio_power_normalization[
            OF tau_positive alpha_positive s_at_most_one])
    have right_identity:
      "(tau powr (1 - s)) * (2 * (?rho tau) ^ ?N) =
        (2 * C ^ ?N) *
          (tau powr
            (1 - s - alpha *
              of_int (slp_tail_cutoff1 alpha s)))"
      using normalized by (simp add: algebra_simps)
    show ?case
      unfolding slp_one_sided_model_tail_def
      using scaled_bound right_identity by simp
  qed
  have constant_nonnegative: "0 \<le> 2 * C ^ ?N"
    by (rule mult_nonneg_nonneg) (simp_all add: C_nonnegative)
  show ?thesis
    by (rule slp_tail_cutoff1_bound_tendsto_zero[
          OF alpha_positive constant_nonnegative
            tail_nonnegative tail_bound])
qed

end
