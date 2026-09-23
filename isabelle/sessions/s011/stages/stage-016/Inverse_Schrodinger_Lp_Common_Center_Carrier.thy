theory Inverse_Schrodinger_Lp_Common_Center_Carrier
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Left_Neumann_Joint_Geometric_Series"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Neumann_AE_Center_Fixed_Point"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Common conull carriers and the totalized left series\<close>

theorem slp_common_measurable_conull_carrier:
  fixes M :: "'a measure"
    and Omega :: "'a set"
    and P Q :: "'a \<Rightarrow> bool"
  assumes Omega_measurable: "Omega \<in> sets M"
    and Omega_nonnull: "Omega \<notin> null_sets M"
    and P_AE: "AE x in M. x \<in> Omega \<longrightarrow> P x"
    and Q_AE: "AE x in M. x \<in> Omega \<longrightarrow> Q x"
  shows
    "\<exists>Z. Z \<in> sets M
      \<and> Z \<noteq> {}
      \<and> Z \<subseteq> Omega
      \<and> (AE x in M. x \<in> Omega \<longleftrightarrow> x \<in> Z)
      \<and> (\<forall>x \<in> Z. P x \<and> Q x)"
proof -
  obtain NP where P_outside:
      "\<And>x. x \<in> space M - NP \<Longrightarrow> x \<in> Omega \<longrightarrow> P x"
    and NP_null: "NP \<in> null_sets M"
    using AE_E3[
      where M = M and P = "\<lambda>x. x \<in> Omega \<longrightarrow> P x",
      OF P_AE]
    by blast
  obtain NQ where Q_outside:
      "\<And>x. x \<in> space M - NQ \<Longrightarrow> x \<in> Omega \<longrightarrow> Q x"
    and NQ_null: "NQ \<in> null_sets M"
    using AE_E3[
      where M = M and P = "\<lambda>x. x \<in> Omega \<longrightarrow> Q x",
      OF Q_AE]
    by blast

  let ?N = "NP \<union> NQ"
  let ?Z = "Omega - ?N"

  have N_null: "?N \<in> null_sets M"
    by (rule null_sets.Un[OF NP_null NQ_null])
  have Z_measurable: "?Z \<in> sets M"
    using Omega_measurable null_setsD2[OF N_null] by measurable
  have Z_subset: "?Z \<subseteq> Omega"
    by blast
  have Z_nonempty: "?Z \<noteq> {}"
  proof
    assume Z_empty: "?Z = {}"
    have Omega_subset_N: "Omega \<subseteq> ?N"
      using Z_empty by blast
    have "Omega \<in> null_sets M"
      by (rule null_sets_subset[OF N_null Omega_measurable Omega_subset_N])
    with Omega_nonnull show False by contradiction
  qed

  have carrier_AE: "AE x in M. x \<in> Omega \<longleftrightarrow> x \<in> ?Z"
    using AE_not_in[OF N_null]
  proof eventually_elim
    fix x
    assume x_outside: "x \<notin> ?N"
    show "x \<in> Omega \<longleftrightarrow> x \<in> ?Z"
      using x_outside by simp
  qed

  have pointwise_good: "\<forall>x \<in> ?Z. P x \<and> Q x"
  proof (intro ballI conjI)
    fix x
    assume x_in: "x \<in> ?Z"
    have Omega_space: "Omega \<subseteq> space M"
      by (rule sets.sets_into_space[OF Omega_measurable])
    have x_space: "x \<in> space M"
      using x_in Omega_space by blast
    have x_in_Omega: "x \<in> Omega"
      using x_in by blast
    have P_imp: "x \<in> Omega \<longrightarrow> P x"
      by (rule P_outside)
        (use x_in x_space in blast)
    have Q_imp: "x \<in> Omega \<longrightarrow> Q x"
      by (rule Q_outside)
        (use x_in x_space in blast)
    show "P x"
      using P_imp x_in_Omega by blast
    show "Q x"
      using Q_imp x_in_Omega by blast
  qed

  show ?thesis
    by (rule exI[of _ ?Z])
      (use Z_measurable Z_nonempty Z_subset carrier_AE pointwise_good in blast)
qed

definition slp_left_neumann_joint_series_on ::
    "slp_point set \<Rightarrow> slp_point set \<Rightarrow> real \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_point \<times> slp_point \<Rightarrow> complex"
  where
  "slp_left_neumann_joint_series_on centers X tau cutoff coefficient =
    (\<lambda>pair. \<Sum>j.
      if fst pair \<in> centers
      then slp_restrict_field X
        (slp_neumann_iterate
          (slp_left_neumann_step tau (fst pair) cutoff coefficient)
          (slp_left_neumann_base tau (fst pair) cutoff coefficient
            SLP_Dbar_Inverse) j) (snd pair)
      else 0)"

theorem slp_left_neumann_joint_series_on_fiber:
  "slp_left_neumann_joint_series_on centers X tau cutoff coefficient (c, z) =
    (if c \<in> centers
     then slp_left_neumann_series_sum X tau c cutoff coefficient z
     else 0)"
proof (cases "c \<in> centers")
  case True
  then show ?thesis
    unfolding slp_left_neumann_joint_series_on_def
      slp_left_neumann_series_sum_def
    by simp
next
  case False
  then show ?thesis
    unfolding slp_left_neumann_joint_series_on_def by simp
qed

end
