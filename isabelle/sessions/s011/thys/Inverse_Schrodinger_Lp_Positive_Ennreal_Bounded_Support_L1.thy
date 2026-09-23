theory Inverse_Schrodinger_Lp_Positive_Ennreal_Bounded_Support_L1
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Root_All_Order_Terminal_Weighted"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Root_Bounded_Support"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Complex_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Two"
begin

section \<open>Bounded-support L1 closure for positive extended-real densities\<close>

lemma slp_positive_ennreal_lp_integrable_bounded_support:
  fixes p :: real
    and F :: "slp_point \<Rightarrow> ennreal"
  assumes p_at_least_one: "1 \<le> p"
    and F_lp: "slp_positive_ennreal_lp_on_plane p F"
    and F_support: "bounded {x. F x \<noteq> 0}"
  shows "integrable lborel (\<lambda>x. enn2real (F x))"
proof -
  let ?f = "\<lambda>x. of_real (enn2real (F x)) :: complex"
  have f_lp: "aim_complex_lp_on_plane p ?f"
    by (rule slp_positive_ennreal_lp_to_complex[OF F_lp])
  have f_support_subset: "{x. ?f x \<noteq> 0} \<subseteq> {x. F x \<noteq> 0}"
    by auto
  have f_support: "bounded {x. ?f x \<noteq> 0}"
    by (rule bounded_subset[OF F_support f_support_subset])
  have f_l1: "aim_complex_lp_on_plane 1 ?f"
    by (rule aim_complex_lp_on_plane_mono_exponent_bounded_support[OF
          zero_less_one p_at_least_one f_support f_lp])
  have f_measurable: "?f \<in> borel_measurable lborel"
    using f_l1 unfolding aim_complex_lp_on_plane_def by blast
  have f_support_measurable: "{x. ?f x \<noteq> 0} \<in> sets lborel"
    by (rule slp_nonzero_set_measurable[OF f_measurable])
  have f_integrable: "integrable lborel ?f"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          order_refl f_support_measurable f_support f_l1]) simp
  have real_integrable:
      "integrable lborel (\<lambda>x. Re (?f x))"
    by (rule integrable_Re[OF f_integrable])
  show ?thesis using real_integrable by simp
qed

context aim_planar_riesz_hls
begin

theorem slp_positive_root_output_density_terminal_weighted_real_integrable:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside: "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integrable lborel (\<lambda>output. enn2real
      (slp_positive_root_output_density R cutoff potential
        (slp_positive_terminal_riesz_weight R potential) n potential
        output))"
proof -
  let ?q = "slp_branch_power_exponent p"
  let ?F = "slp_positive_root_output_density R cutoff potential
    (slp_positive_terminal_riesz_weight R potential) n potential"
  have potential_support_subset: "{x. potential x \<noteq> 0} \<subseteq> X"
    using potential_outside by blast
  have potential_support: "bounded {x. potential x \<noteq> 0}"
    by (rule bounded_subset[OF X_bounded potential_support_subset])
  note all_order =
    slp_positive_root_output_density_all_orders_terminal_weighted_lp_root[OF
      radius_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable potential_lp potential_lp potential_outside
      cutoff_bound C_nonnegative]
  have q_lower: "1 < ?q"
    using all_order(1) by blast
  obtain L where F_lp: "slp_positive_ennreal_lp_on_plane ?q ?F"
    using all_order(2)[of n] by blast
  have F_support: "bounded {x. ?F x \<noteq> 0}"
    by (rule slp_positive_root_output_density_bounded_support[OF
          radius_nonnegative potential_support])
  show ?thesis
    by (rule slp_positive_ennreal_lp_integrable_bounded_support[OF
          less_imp_le[OF q_lower] F_lp F_support])
qed

end

end
