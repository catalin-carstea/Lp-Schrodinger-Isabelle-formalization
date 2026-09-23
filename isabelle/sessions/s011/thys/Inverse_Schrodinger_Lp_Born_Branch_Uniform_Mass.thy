theory Inverse_Schrodinger_Lp_Born_Branch_Uniform_Mass
  imports
    Inverse_Schrodinger_Lp_Born_Branch_Uniform_Base_Mass
    Inverse_Schrodinger_Lp_Born_Block_Uniform_Mass
begin

section \<open>All-orders origin-uniform positive branch mass\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_branch_mass_unweighted_uniform:
  fixes R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "\<forall>n. \<exists>M. M < top \<and>
      (\<forall>origin.
        slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
          origin (\<lambda>_. 1) \<le> M)"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  obtain B where B_finite: "B < top"
    and B_bound:
      "\<And>origin.
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point
          \<partial>lborel \<partial>lborel) \<le> B"
    using slp_positive_branch_block_mass_uniform[OF radius_nonnegative
      p_lower p_upper cutoff_measurable potential_lp cutoff_bound
      C_nonnegative]
    by blast
  show ?thesis
  proof
    fix n :: nat
    show "\<exists>M. M < top \<and>
        (\<forall>origin.
          slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
            origin (\<lambda>_. 1) \<le> M)"
    proof (induction n)
      case 0
      show ?case
        by (rule slp_positive_branch_mass_zero_unweighted_uniform[OF
              cutoff_measurable cutoff_bound C_nonnegative])
    next
      case (Suc n)
      obtain M where M_finite: "M < top"
        and M_bound:
          "\<And>origin.
            slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
              origin (\<lambda>_. 1) \<le> M"
        using Suc.IH by blast
      let ?next = "ennreal (inverse (pi ^ 2)) * (B * M)"
      have next_finite: "?next < top"
        using B_finite M_finite by (simp add: ennreal_mult_less_top)
      have next_bound:
          "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1)
              (Suc n) origin (\<lambda>_. 1) \<le> ?next"
        for origin
      proof -
        have recurrence:
            "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1)
                (Suc n) origin (\<lambda>_. 1) \<le>
              ennreal (inverse (pi ^ 2)) *
                ((\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
                    slp_positive_branch_block_weight R cutoff potential origin
                      pos_point neg_point
                    \<partial>lborel \<partial>lborel) * M)"
          by (rule slp_positive_branch_mass_Suc_le[OF cutoff_measurable
                potential_measurable M_bound])
        have block_scaled:
            "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
                slp_positive_branch_block_weight R cutoff potential origin
                  pos_point neg_point
                \<partial>lborel \<partial>lborel) * M \<le> B * M"
          by (rule mult_right_mono[OF B_bound]) simp
        have recurrence_scaled:
            "ennreal (inverse (pi ^ 2)) *
                ((\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
                    slp_positive_branch_block_weight R cutoff potential origin
                      pos_point neg_point
                    \<partial>lborel \<partial>lborel) * M) \<le> ?next"
          by (rule mult_left_mono[OF block_scaled]) simp
        show ?thesis
        proof (rule order_trans[OF recurrence])
          show "ennreal (inverse (pi ^ 2)) *
              ((\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
                  slp_positive_branch_block_weight R cutoff potential origin
                    pos_point neg_point
                  \<partial>lborel \<partial>lborel) * M) \<le> ?next"
            using recurrence_scaled by (simp add: mult.assoc)
        qed
      qed
      show ?case
        by (intro exI[of _ ?next] conjI next_finite allI next_bound)
    qed
  qed
qed

end

end
