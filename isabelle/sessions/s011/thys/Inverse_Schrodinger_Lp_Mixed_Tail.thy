theory Inverse_Schrodinger_Lp_Mixed_Tail
  imports Inverse_Schrodinger_Lp_One_Sided_Tail
begin

section \<open>Modeled mixed Neumann-tail convergence\<close>

definition slp_mixed_model_tail ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
where
  "slp_mixed_model_tail C C_tilde alpha s tau =
    (tau powr (1 - s - alpha)) *
      slp_mixed_diagonal_tail
        (C * (tau powr (- alpha)))
        (C_tilde * (tau powr (- alpha)))
        (nat (slp_tail_cutoff2 alpha s))"

theorem slp_mixed_model_tail_tendsto_zero:
  fixes C C_tilde alpha s :: real
  assumes alpha_positive: "0 < alpha"
    and C_nonnegative: "0 \<le> C"
    and C_tilde_nonnegative: "0 \<le> C_tilde"
  shows
    "((slp_mixed_model_tail C C_tilde alpha s)
      \<longlongrightarrow> 0) at_top"
proof -
  let ?N = "nat (slp_tail_cutoff2 alpha s)"
  let ?rho = "\<lambda>tau :: real. C * (tau powr (- alpha))"
  let ?rho_tilde =
    "\<lambda>tau :: real. C_tilde * (tau powr (- alpha))"
  let ?Cmax = "max C C_tilde"
  have ratio_interval:
    "eventually
      (\<lambda>tau :: real.
        0 < tau \<and>
        0 \<le> ?rho tau \<and> ?rho tau \<le> 1 / 2 \<and>
        0 \<le> ?rho_tilde tau \<and> ?rho_tilde tau \<le> 1 / 2)
      at_top"
  proof -
    have first:
      "eventually
        (\<lambda>tau :: real.
          0 < tau \<and> 0 \<le> ?rho tau \<and> ?rho tau \<le> 1 / 2)
        at_top"
      by (rule slp_neumann_ratio_eventually_half[
            OF alpha_positive C_nonnegative])
    have second:
      "eventually
        (\<lambda>tau :: real.
          0 < tau \<and>
          0 \<le> ?rho_tilde tau \<and> ?rho_tilde tau \<le> 1 / 2)
        at_top"
      by (rule slp_neumann_ratio_eventually_half[
            OF alpha_positive C_tilde_nonnegative])
    from first second show ?thesis
      by eventually_elim blast
  qed
  have tail_nonnegative:
    "eventually
      (\<lambda>tau. 0 \<le> slp_mixed_model_tail C C_tilde alpha s tau)
      at_top"
    using ratio_interval
  proof eventually_elim
    case (elim tau)
    have rho_nonnegative: "0 \<le> ?rho tau"
      using elim by blast
    have rho_half: "?rho tau \<le> 1 / 2"
      using elim by blast
    have rho_tilde_nonnegative: "0 \<le> ?rho_tilde tau"
      using elim by blast
    have rho_tilde_half: "?rho_tilde tau \<le> 1 / 2"
      using elim by blast
    have mixed_summable:
      "summable
        (\<lambda>k.
          slp_mixed_diagonal_term
            (?rho tau) (?rho_tilde tau) (?N + k))"
      by (rule slp_mixed_diagonal_shifted_summable[
            OF rho_nonnegative rho_tilde_nonnegative
              rho_half rho_tilde_half])
    have mixed_nonnegative:
      "0 \<le> slp_mixed_diagonal_tail (?rho tau) (?rho_tilde tau) ?N"
      unfolding slp_mixed_diagonal_tail_def
      by (rule suminf_nonneg[OF mixed_summable])
        (rule slp_mixed_diagonal_term_nonnegative[
          OF rho_nonnegative rho_tilde_nonnegative])
    show ?case
      unfolding slp_mixed_model_tail_def
      by (rule mult_nonneg_nonneg) (simp_all add: mixed_nonnegative)
  qed
  have tail_bound:
    "eventually
      (\<lambda>tau.
        slp_mixed_model_tail C C_tilde alpha s tau \<le>
          (slp_weighted_tail_constant ?N * ?Cmax ^ ?N) *
            (tau powr
              (1 - s - alpha - alpha *
                of_int (slp_tail_cutoff2 alpha s))))
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
    have rho_tilde_nonnegative: "0 \<le> ?rho_tilde tau"
      using elim by blast
    have rho_tilde_half: "?rho_tilde tau \<le> 1 / 2"
      using elim by blast
    have outside_nonnegative: "0 \<le> tau powr (1 - s - alpha)"
      by simp
    have mixed_bound:
      "slp_mixed_diagonal_tail (?rho tau) (?rho_tilde tau) ?N \<le>
        slp_weighted_tail_constant ?N *
          max (?rho tau) (?rho_tilde tau) ^ ?N"
      by (rule slp_mixed_diagonal_tail_le_constant[
            OF rho_nonnegative rho_tilde_nonnegative
              rho_half rho_tilde_half])
    have scaled_bound:
      "(tau powr (1 - s - alpha)) *
          slp_mixed_diagonal_tail (?rho tau) (?rho_tilde tau) ?N \<le>
        (tau powr (1 - s - alpha)) *
          (slp_weighted_tail_constant ?N *
            max (?rho tau) (?rho_tilde tau) ^ ?N)"
      by (rule mult_left_mono[OF mixed_bound outside_nonnegative])
    have power_nonnegative: "0 \<le> tau powr (- alpha)"
      by simp
    have max_ratio:
      "max (?rho tau) (?rho_tilde tau) =
        ?Cmax * (tau powr (- alpha))"
      using power_nonnegative
      by (simp add: max_mult_distrib_right)
    have normalized:
      "(tau powr (1 - s - alpha)) *
          (?Cmax * (tau powr (- alpha))) ^ ?N =
        ?Cmax ^ ?N *
          (tau powr
            (1 - s - alpha - alpha *
              of_int (slp_tail_cutoff2 alpha s)))"
      by (rule slp_mixed_cutoff_ratio_power_normalization[OF tau_positive])
    have right_identity:
      "(tau powr (1 - s - alpha)) *
          (slp_weighted_tail_constant ?N *
            max (?rho tau) (?rho_tilde tau) ^ ?N) =
        (slp_weighted_tail_constant ?N * ?Cmax ^ ?N) *
          (tau powr
            (1 - s - alpha - alpha *
              of_int (slp_tail_cutoff2 alpha s)))"
      using max_ratio normalized by (simp add: algebra_simps)
    show ?case
      unfolding slp_mixed_model_tail_def
      using scaled_bound right_identity by simp
  qed
  have Cmax_nonnegative: "0 \<le> ?Cmax"
    using C_nonnegative by simp
  have constant_nonnegative:
    "0 \<le> slp_weighted_tail_constant ?N * ?Cmax ^ ?N"
    by (rule mult_nonneg_nonneg[
          OF slp_weighted_tail_constant_nonnegative])
      (rule zero_le_power[OF Cmax_nonnegative])
  show ?thesis
    by (rule slp_tail_cutoff2_bound_tendsto_zero[
          OF alpha_positive constant_nonnegative
            tail_nonnegative tail_bound])
qed

end
