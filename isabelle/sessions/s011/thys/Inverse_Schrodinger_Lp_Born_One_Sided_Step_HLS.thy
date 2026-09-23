theory Inverse_Schrodinger_Lp_Born_One_Sided_Step_HLS
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Step_Riesz
begin

section \<open>HLS discharge of the root-step recurrence\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_root_output_density_Suc_riesz_compact_lp:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_support: "bounded {x. root_weight x \<noteq> 0}"
  shows
    "slp_positive_root_output_density R cutoff root_weight (\<lambda>_. 1)
        (Suc n) root_weight output =
      slp_positive_root_step_density R cutoff root_weight (\<lambda>_. 1) n
        root_weight output"
proof -
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_fibers:
      "AE pos_point in lborel.
        integrable lborel
          (slp_localized_riesz_integrand R root_weight pos_point)"
    using slp_localized_riesz_l2_compact_lp[OF radius_nonnegative p_lower
      p_upper root_weight_lp root_weight_support]
    by blast
  show ?thesis
    by (rule slp_positive_root_output_density_Suc_riesz[OF
          cutoff_measurable root_weight_measurable _ root_weight_measurable
          root_fibers]) measurable
qed

end

end
