theory Inverse_Schrodinger_Lp_Born_One_Sided_Riesz_L2
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Root_Lp
    Inverse_Schrodinger_Lp_Localized_Cauchy_L2_Compact
begin

section \<open>The localized positive Riesz field in \(L^2\)\<close>

lemma slp_hls_target_exponent_above_two:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
  shows "2 < aim_hls_target_exponent p"
proof -
  have denominator_positive: "0 < 2 - p"
    using p_upper by linarith
  show ?thesis
    unfolding aim_hls_target_exponent_def
    using p_lower denominator_positive
    by (simp add: less_divide_eq)
qed

context aim_planar_riesz_hls
begin

theorem slp_localized_riesz_l2_compact_lp:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and f_lp: "aim_complex_lp_on_plane p f"
    and f_support: "bounded {x. f x \<noteq> 0}"
  shows
    "(AE z in lborel.
        integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
      aim_real_lp_on_plane 2 (slp_localized_riesz_potential R f) \<and>
      bounded {z. slp_localized_riesz_potential R f z \<noteq> 0}"
proof -
  obtain C :: real where C_positive: "0 < C"
    and localized:
      "\<forall>R p f. 0 \<le> R \<and> 1 < p \<and> p < 2 \<and>
          aim_complex_lp_on_plane p f
        \<longrightarrow>
        (AE z in lborel.
          integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (slp_localized_riesz_potential R f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_localized_riesz_hls by blast
  have hls_result:
      "(AE z in lborel.
          integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R f)"
    using localized radius_nonnegative p_lower p_upper f_lp by blast
  have potential_support:
      "bounded {z. slp_localized_riesz_potential R f z \<noteq> 0}"
    by (rule slp_localized_riesz_potential_bounded_support[OF
          radius_nonnegative f_support])
  have target_above_two: "2 < aim_hls_target_exponent p"
    by (rule slp_hls_target_exponent_above_two[OF p_lower p_upper])
  have potential_l2:
      "aim_real_lp_on_plane 2 (slp_localized_riesz_potential R f)"
    by (rule aim_real_lp_on_plane_mono_exponent_bounded_support[OF
          _ less_imp_le[OF target_above_two] potential_support])
       (use hls_result in auto)
  show ?thesis
    using hls_result potential_l2 potential_support by blast
qed

end

end
