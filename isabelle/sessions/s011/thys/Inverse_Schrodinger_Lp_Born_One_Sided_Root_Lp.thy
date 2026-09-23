theory Inverse_Schrodinger_Lp_Born_One_Sided_Root_Lp
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Root_Density
    Inverse_Schrodinger_Lp_Local_L1_Integrability
begin

section \<open>Compactly supported root potentials in the one-sided density\<close>

lemma aim_complex_lp_on_plane_integrable_bounded_support:
  assumes p_at_least_one: "1 \<le> p"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and f_lp: "aim_complex_lp_on_plane p f"
    and f_outside: "\<And>x. x \<notin> X \<Longrightarrow> f x = 0"
  shows "integrable lborel f"
proof -
  have local_integrable: "set_integrable lborel X f"
    by (rule aim_complex_lp_on_plane_set_integrable_bounded[OF
          p_at_least_one X_measurable X_bounded f_lp])
  have restrict_eq: "(\<lambda>x. indicator X x *\<^sub>R f x) = f"
    by (rule ext) (simp add: indicator_def f_outside)
  show ?thesis
    using local_integrable
    unfolding set_integrable_def restrict_eq .
qed

context aim_planar_riesz_hls
begin

theorem slp_positive_root_output_density_unweighted_mass_finite_lp_root:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside: "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "(\<integral>\<^sup>+ output.
        slp_positive_root_output_density R cutoff potential (\<lambda>_. 1) n
          root_weight output
        \<partial>lborel) < top"
proof -
  have root_weight_integrable: "integrable lborel root_weight"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded root_weight_lp root_weight_outside])
       (use p_lower in simp)
  show ?thesis
    by (rule slp_positive_root_output_density_unweighted_mass_finite[OF
          radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
          cutoff_bound C_nonnegative root_weight_integrable])
qed

corollary slp_left_one_sided_output_density_unweighted_mass_finite_lp_root:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
  assumes "0 \<le> R" "1 < p" "p < 2"
    "X \<in> sets lborel" "bounded X"
    "cutoff \<in> borel_measurable lborel"
    "aim_complex_lp_on_plane p potential"
    "aim_complex_lp_on_plane p root_weight"
    "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    "\<And>x. norm (cutoff x) \<le> C" "0 \<le> C"
  shows
    "(\<integral>\<^sup>+ output.
        slp_left_one_sided_output_density R cutoff potential (\<lambda>_. 1) n
          root_weight output
        \<partial>lborel) < top"
  unfolding slp_left_one_sided_output_density_def
  by (rule slp_positive_root_output_density_unweighted_mass_finite_lp_root[OF
        assms])

corollary slp_right_one_sided_output_density_unweighted_mass_finite_lp_root:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
  assumes "0 \<le> R" "1 < p" "p < 2"
    "X \<in> sets lborel" "bounded X"
    "cutoff \<in> borel_measurable lborel"
    "aim_complex_lp_on_plane p potential"
    "aim_complex_lp_on_plane p root_weight"
    "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    "\<And>x. norm (cutoff x) \<le> C" "0 \<le> C"
  shows
    "(\<integral>\<^sup>+ output.
        slp_right_one_sided_output_density R cutoff potential (\<lambda>_. 1) n
          root_weight output
        \<partial>lborel) < top"
  unfolding slp_right_one_sided_output_density_def
  by (rule slp_positive_root_output_density_unweighted_mass_finite_lp_root[OF
        assms])

end

end
