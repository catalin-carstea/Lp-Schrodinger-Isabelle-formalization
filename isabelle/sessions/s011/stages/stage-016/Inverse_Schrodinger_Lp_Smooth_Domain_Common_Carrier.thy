theory Inverse_Schrodinger_Lp_Smooth_Domain_Common_Carrier
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Common_Center_Carrier"
begin

section \<open>Smooth-domain specialization of the common carrier\<close>

theorem slp_bounded_smooth_domain_lborel_carrier:
  assumes domain: "slp_bounded_smooth_domain Omega"
  shows
    "Omega \<in> sets (lborel :: slp_point measure)
      \<and> Omega \<notin> null_sets (lborel :: slp_point measure)"
proof -
  have Omega_nonempty: "Omega \<noteq> {}"
    and Omega_open: "open Omega"
    using domain unfolding slp_bounded_smooth_domain_def by blast+
  have Omega_measurable: "Omega \<in> sets (lborel :: slp_point measure)"
    using Omega_open by simp
  have Omega_nonnegligible: "\<not> negligible Omega"
    by (rule open_not_negligible[OF Omega_open Omega_nonempty])
  have Omega_nonnull_completion:
      "Omega \<notin> null_sets (completion (lborel :: slp_point measure))"
    using Omega_nonnegligible by (simp add: negligible_iff_null_sets)
  have Omega_nonnull: "Omega \<notin> null_sets (lborel :: slp_point measure)"
  proof
    assume "Omega \<in> null_sets (lborel :: slp_point measure)"
    then have "Omega \<in> null_sets (completion (lborel :: slp_point measure))"
      by (rule null_sets_completionI)
    with Omega_nonnull_completion show False by contradiction
  qed
  show ?thesis
    using Omega_measurable Omega_nonnull by blast
qed

theorem slp_bounded_smooth_domain_common_carrier:
  fixes P Q :: "slp_point \<Rightarrow> bool"
  assumes domain: "slp_bounded_smooth_domain Omega"
    and P_AE:
      "AE x in (lborel :: slp_point measure). x \<in> Omega \<longrightarrow> P x"
    and Q_AE:
      "AE x in (lborel :: slp_point measure). x \<in> Omega \<longrightarrow> Q x"
  shows
    "\<exists>Z. Z \<in> sets (lborel :: slp_point measure)
      \<and> Z \<noteq> {}
      \<and> Z \<subseteq> Omega
      \<and> (AE x in (lborel :: slp_point measure).
        x \<in> Omega \<longleftrightarrow> x \<in> Z)
      \<and> (\<forall>x \<in> Z. P x \<and> Q x)"
proof -
  have Omega_measurable: "Omega \<in> sets (lborel :: slp_point measure)"
    and Omega_nonnull: "Omega \<notin> null_sets (lborel :: slp_point measure)"
    using slp_bounded_smooth_domain_lborel_carrier[OF domain] by blast+
  show ?thesis
    by (rule slp_common_measurable_conull_carrier[
          OF Omega_measurable Omega_nonnull P_AE Q_AE])
qed

end
