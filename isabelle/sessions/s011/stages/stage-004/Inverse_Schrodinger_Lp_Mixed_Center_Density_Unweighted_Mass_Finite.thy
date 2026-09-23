theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Unweighted_Mass_Finite
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Mass_Uniform_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Branch_Uniform_Mass"
begin

section \<open>Finite mass of the unweighted mixed center density\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_unweighted_mass_finite:
  fixes R C p :: real
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
    and left_order right_order :: nat
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_lp:
      "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp:
      "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_weight_integrable: "integrable lborel root_weight"
  shows
    "(\<integral>\<^sup>+ center.
        slp_mixed_center_density R cutoff left_potential right_potential
          (\<lambda>_. 1) (\<lambda>_. 1) left_order right_order
          root_weight center \<partial>lborel) < top_class.top"
proof -
  have left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable unfolding integrable_iff_bounded by blast
  have one_measurable[measurable]:
      "(\<lambda>_ :: slp_point. (1 :: ennreal))
        \<in> borel_measurable lborel"
    by measurable
  obtain left_cap where left_cap_finite: "left_cap < top_class.top"
    and left_functional_bound:
      "\<And>root.
        slp_positive_branch_functional R cutoff left_potential (\<lambda>_. 1)
          left_order root (\<lambda>_. 1) \<le> left_cap"
    using slp_positive_branch_mass_unweighted_uniform[OF
        radius_nonnegative p_lower p_upper cutoff_measurable
        left_potential_lp cutoff_bound C_nonnegative]
    by blast
  obtain right_cap where right_cap_finite: "right_cap < top_class.top"
    and right_functional_bound:
      "\<And>root.
        slp_positive_branch_functional R cutoff right_potential (\<lambda>_. 1)
          right_order root (\<lambda>_. 1) \<le> right_cap"
    using slp_positive_branch_mass_unweighted_uniform[OF
        radius_nonnegative p_lower p_upper cutoff_measurable
        right_potential_lp cutoff_bound C_nonnegative]
    by blast
  have left_mass_bound:
      "(\<integral>\<^sup>+ output.
        slp_left_positive_output_density R cutoff left_potential
          (\<lambda>_. 1) left_order root output \<partial>lborel) \<le> left_cap"
    for root
  proof -
    note exact = slp_left_positive_output_density_mass[OF
        cutoff_measurable left_potential_measurable one_measurable,
        of R left_order root]
    show ?thesis
      using exact left_functional_bound[of root] by simp
  qed
  have right_mass_bound:
      "(\<integral>\<^sup>+ output.
        slp_right_positive_output_density R cutoff right_potential
          (\<lambda>_. 1) right_order root output \<partial>lborel) \<le> right_cap"
    for root
  proof -
    note exact = slp_right_positive_output_density_mass[OF
        cutoff_measurable right_potential_measurable one_measurable,
        of R right_order root]
    show ?thesis
      using exact right_functional_bound[of root] by simp
  qed
  have total_bound:
      "(\<integral>\<^sup>+ center.
          slp_mixed_center_density R cutoff left_potential right_potential
            (\<lambda>_. 1) (\<lambda>_. 1) left_order right_order
            root_weight center \<partial>lborel) \<le>
        (\<integral>\<^sup>+ root.
          ennreal (Real_Vector_Spaces.norm (root_weight root))
          \<partial>lborel) * left_cap * right_cap"
    by (rule slp_mixed_center_density_mass_uniform_bound[OF
          cutoff_measurable left_potential_measurable
          right_potential_measurable one_measurable one_measurable
          root_weight_measurable left_mass_bound right_mass_bound])
  have root_mass_finite:
      "(\<integral>\<^sup>+ root.
        ennreal (Real_Vector_Spaces.norm (root_weight root))
        \<partial>lborel) < top_class.top"
    using root_weight_integrable
    unfolding integrable_iff_bounded by simp
  have majorant_finite:
      "(\<integral>\<^sup>+ root.
        ennreal (Real_Vector_Spaces.norm (root_weight root))
        \<partial>lborel) * left_cap * right_cap < top_class.top"
    using root_mass_finite left_cap_finite right_cap_finite
    by (simp add: ennreal_mult_less_top)
  show ?thesis
    by (rule le_less_trans[OF total_bound majorant_finite])
qed

end

end
