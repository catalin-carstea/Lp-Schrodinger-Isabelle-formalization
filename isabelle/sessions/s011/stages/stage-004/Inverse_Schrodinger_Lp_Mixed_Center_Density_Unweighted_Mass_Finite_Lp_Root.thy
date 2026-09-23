theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Unweighted_Mass_Finite_Lp_Root
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Unweighted_Mass_Finite"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Root_Lp"
begin

section \<open>Compact-support project-Lp discharge for the mixed density\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_unweighted_mass_finite_lp_root:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
    and left_order right_order :: nat
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_lp:
      "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp:
      "aim_complex_lp_on_plane p right_potential"
    and root_weight_lp:
      "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "(\<integral>\<^sup>+ center.
        slp_mixed_center_density R cutoff left_potential right_potential
          (\<lambda>_. 1) (\<lambda>_. 1) left_order right_order
          root_weight center \<partial>lborel) < top_class.top"
proof -
  have root_weight_integrable: "integrable lborel root_weight"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded root_weight_lp root_weight_outside])
       (use p_lower in simp)
  show ?thesis
    by (rule slp_mixed_center_density_unweighted_mass_finite[OF
          radius_nonnegative p_lower p_upper cutoff_measurable
          left_potential_lp right_potential_lp cutoff_bound C_nonnegative
          root_weight_integrable])
qed

end

end
