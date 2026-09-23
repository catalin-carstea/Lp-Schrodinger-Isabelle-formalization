theory Inverse_Schrodinger_Lp_Born_One_Sided_All_Order_L2
  imports Inverse_Schrodinger_Lp_Born_Root_Positive_Order_L2
begin

section \<open>All-order real \(L^2\) interfaces for one-sided densities\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_right_one_sided_output_density_real_all_orders_l2:
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
  shows positive_all_orders:
      "\<And>n. aim_real_lp_on_plane 2
        (slp_positive_root_output_density_real R cutoff potential
          (\<lambda>_. 1) n potential)"
    and left_all_orders:
      "\<And>n. aim_real_lp_on_plane 2
        (\<lambda>output. enn2real
          (slp_left_one_sided_output_density R cutoff potential
            (\<lambda>_. 1) n potential output))"
    and right_all_orders:
      "\<And>n. aim_real_lp_on_plane 2
        (\<lambda>output. enn2real
          (slp_right_one_sided_output_density R cutoff potential
            (\<lambda>_. 1) n potential output))"
proof -
  have potential_support_subset: "{x. potential x \<noteq> 0} \<subseteq> X"
    using potential_outside by blast
  have potential_support: "bounded {x. potential x \<noteq> 0}"
    by (rule bounded_subset[OF X_bounded potential_support_subset])
  show positive:
      "\<And>n. aim_real_lp_on_plane 2
        (slp_positive_root_output_density_real R cutoff potential
          (\<lambda>_. 1) n potential)"
  proof -
    fix n :: nat
    show "aim_real_lp_on_plane 2
        (slp_positive_root_output_density_real R cutoff potential
          (\<lambda>_. 1) n potential)"
    proof (cases n)
      case 0
      show ?thesis
        unfolding 0
        by (rule slp_positive_root_output_density_real_zero_l2[OF
              radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
              potential_support cutoff_bound C_nonnegative])
    next
      case (Suc k)
      show ?thesis
        unfolding Suc
        by (rule slp_positive_root_output_density_real_positive_order_l2[OF
              radius_nonnegative p_lower p_upper X_measurable X_bounded
              cutoff_measurable potential_lp potential_lp potential_outside
              cutoff_bound C_nonnegative])
    qed
  qed
  show "\<And>n. aim_real_lp_on_plane 2
      (\<lambda>output. enn2real
        (slp_left_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output))"
    using positive
    unfolding slp_positive_root_output_density_real_def
      slp_left_one_sided_output_density_def by blast
  show "\<And>n. aim_real_lp_on_plane 2
      (\<lambda>output. enn2real
        (slp_right_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output))"
    using positive
    unfolding slp_positive_root_output_density_real_def
      slp_right_one_sided_output_density_def by blast
qed

end

end
