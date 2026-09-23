theory Inverse_Schrodinger_Lp_Born_One_Sided_Square_Recurrence_HLS
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Step_HLS
    Inverse_Schrodinger_Lp_Born_One_Sided_Step_Square_Recurrence
begin

section \<open>Concrete HLS successor square recurrence\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_root_output_density_Suc_square_recurrence:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_support: "bounded {x. root_weight x \<noteq> 0}"
    and root_mass_bound:
      "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
        slp_positive_root_step_weight R cutoff root_weight root_weight
          pos_point neg_point \<partial>lborel \<partial>lborel) \<le> B"
    and recursive_square_bound:
      "\<And>origin.
        slp_positive_output_square_mass R cutoff root_weight (\<lambda>_. 1) n
          origin \<le> L"
  shows
    "(\<integral>\<^sup>+out.
        slp_positive_root_output_density R cutoff root_weight (\<lambda>_. 1)
          (Suc n) root_weight out ^ 2 \<partial>lborel) \<le>
      ennreal (inverse (pi ^ 2)) ^ 2 * B ^ 2 * L"
proof -
  have root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have successor_identity:
      "slp_positive_root_output_density R cutoff root_weight (\<lambda>_. 1)
          (Suc n) root_weight out =
        slp_positive_root_step_density R cutoff root_weight (\<lambda>_. 1) n
          root_weight out"
      for out
    by (rule slp_positive_root_output_density_Suc_riesz_compact_lp[OF
          radius_nonnegative p_lower p_upper cutoff_measurable root_weight_lp
          root_weight_support])
  have step_bound:
      "(\<integral>\<^sup>+out.
          slp_positive_root_step_density R cutoff root_weight (\<lambda>_. 1) n
            root_weight out ^ 2 \<partial>lborel) \<le>
        ennreal (inverse (pi ^ 2)) ^ 2 * B ^ 2 * L"
    by (rule slp_positive_root_step_density_square_recurrence[OF
          cutoff_measurable root_weight_measurable _ root_weight_measurable
          root_mass_bound recursive_square_bound]) measurable
  show ?thesis
    using step_bound by (simp only: successor_identity)
qed

end

end
