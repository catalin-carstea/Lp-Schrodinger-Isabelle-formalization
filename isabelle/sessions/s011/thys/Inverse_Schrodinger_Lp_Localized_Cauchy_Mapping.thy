theory Inverse_Schrodinger_Lp_Localized_Cauchy_Mapping
  imports Inverse_Schrodinger_Lp_Localized_Cauchy_L2_Compact
begin

section \<open>The four localized-kernel mapping certificates\<close>

context aim_planar_riesz_hls
begin

theorem slp_localized_cauchy_kernel_mapping_facts:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and r_def: "r = 2 * p / (2 - p)"
    and f_lp: "aim_complex_lp_on_plane p f"
    and g_lp: "aim_complex_lp_on_plane r g"
    and h_lp: "aim_complex_lp_on_plane 2 h"
    and h_support: "bounded {x. h x \<noteq> 0}"
    and s_lower: "1 \<le> (s::real)"
  shows
    "((AE z in lborel.
        integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
      aim_real_lp_on_plane r (slp_localized_riesz_potential R f)) \<and>
    (\<forall>z. integrable lborel (slp_localized_riesz_integrand R g z) \<and>
      slp_localized_riesz_potential R g z \<le>
        integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr
              slp_holder_conjugate r) / slp_holder_conjugate r +
          integral\<^sup>L lborel (\<lambda>y. norm (g y) powr r) / r) \<and>
    (\<forall>z. integrable lborel
        (slp_double_localized_endpoint_integrand R f z) \<and>
      slp_double_localized_endpoint_potential R f z \<le>
        integral\<^sup>L lborel
            (\<lambda>x. abs (slp_double_localized_cauchy_kernel R x) powr
              slp_holder_conjugate p) / slp_holder_conjugate p +
          integral\<^sup>L lborel (\<lambda>y. norm (f y) powr p) / p) \<and>
    ((AE z in lborel.
        integrable lborel (slp_localized_complex_integrand R h z)) \<and>
      aim_complex_lp_on_plane s (slp_localized_complex_convolution R h) \<and>
      bounded {z. slp_localized_complex_convolution R h z \<noteq> 0})"
proof -
  have denominator_positive: "0 < 2 - p"
    using p_upper by linarith
  have target_identity: "aim_hls_target_exponent p = r"
    unfolding aim_hls_target_exponent_def r_def by simp
  have r_above_two: "2 < r"
    unfolding r_def
    using denominator_positive p_lower
    by (simp add: less_divide_eq)
  obtain C::real where C_positive: "0 < C"
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
  have first_mapping:
    "(AE z in lborel.
        integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
      aim_real_lp_on_plane r (slp_localized_riesz_potential R f)"
    using localized radius_nonnegative p_lower p_upper f_lp target_identity
    by blast
  have second_mapping:
    "\<forall>z. integrable lborel (slp_localized_riesz_integrand R g z) \<and>
      slp_localized_riesz_potential R g z \<le>
        integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr
              slp_holder_conjugate r) / slp_holder_conjugate r +
          integral\<^sup>L lborel (\<lambda>y. norm (g y) powr r) / r"
    unfolding slp_localized_riesz_potential_def
    by (rule slp_localized_cauchy_endpoint_bound[OF
          r_above_two radius_nonnegative g_lp])
  have third_mapping:
    "\<forall>z. integrable lborel
        (slp_double_localized_endpoint_integrand R f z) \<and>
      slp_double_localized_endpoint_potential R f z \<le>
        integral\<^sup>L lborel
            (\<lambda>x. abs (slp_double_localized_cauchy_kernel R x) powr
              slp_holder_conjugate p) / slp_holder_conjugate p +
          integral\<^sup>L lborel (\<lambda>y. norm (f y) powr p) / p"
    by (rule slp_double_localized_cauchy_endpoint_bound[OF
          radius_nonnegative p_lower p_upper f_lp])
  have fourth_mapping:
    "(AE z in lborel.
        integrable lborel (slp_localized_complex_integrand R h z)) \<and>
      aim_complex_lp_on_plane s (slp_localized_complex_convolution R h) \<and>
      bounded {z. slp_localized_complex_convolution R h z \<noteq> 0}"
    by (rule slp_localized_complex_l2_compact_all_finite[OF
          radius_nonnegative s_lower h_lp h_support])
  show ?thesis
    using first_mapping second_mapping third_mapping fourth_mapping by blast
qed

end

end
