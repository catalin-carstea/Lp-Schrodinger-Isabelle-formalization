theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel_Product_Dual_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Positive_Fiber_Mass_Density"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Complex_Kernel_Lp_Domination"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Product_Duality_Exponents"
begin

section \<open>Product-dual membership of the literal finite oscillatory kernel\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_oscillatory_kernel_product_dual_lp:
  fixes frequency B C p :: real
    and X :: "slp_point set"
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside: "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound:
      "\<And>x. Real_Vector_Spaces.norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> Real_Vector_Spaces.norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
  shows
    "aim_complex_lp_on_plane (slp_mixed_product_dual_exponent p)
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite)
        TYPE('j::finite) frequency root_weight cutoff left_potential cutoff
        right_potential)"
proof -
  let ?dual = "slp_mixed_product_dual_exponent p"
  let ?kernel =
    "slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j) frequency
      root_weight cutoff left_potential cutoff right_potential"
  let ?positive_mass =
    "slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) (2 * B)
      root_weight cutoff left_potential cutoff right_potential"
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>_. 1) (\<lambda>_. 1) CARD('i) CARD('j) root_weight"
  have dual_lower: "1 < ?dual"
    by (rule slp_mixed_product_duality_exponents(3)[OF p_lower p_upper])
  have dual_positive: "0 < ?dual"
    using dual_lower by simp
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  have cutoff_cmod_bound: "\<And>x. cmod (cutoff x) \<le> C"
    using cutoff_bound by simp
  have left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable:
      "(\<lambda>_ :: slp_point. (1 :: complex)) \<in> borel_measurable lborel"
    by measurable
  have root_weight_integrable: "integrable lborel root_weight"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded root_weight_lp root_weight_outside])
      (use p_lower in simp)
  note kernel_properties_open =
    slp_mixed_center_finite_oscillatory_kernel_properties[
      where frequency = frequency and B = B and C = C and p = p
        and cutoff = cutoff and left_potential = left_potential
        and right_potential = right_potential and root_weight = root_weight
        and 'i = 'i and 'j = 'j,
      OF B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
        right_potential_lp cutoff_bound C_nonnegative root_weight_integrable
    ]
  have kernel_measurable: "?kernel \<in> borel_measurable lborel"
    by (rule kernel_properties_open(1)[OF root_support cutoff_support
          left_potential_support right_potential_support])
  have kernel_positive_bound:
      "AE center in lborel.
        ennreal (norm_class.norm (?kernel center)) \<le> ?positive_mass center"
    by (rule kernel_properties_open(2)[OF root_support cutoff_support
          left_potential_support right_potential_support])
  have positive_mass_density: "?positive_mass center = ?density center"
    for center
  proof -
    have weighted_unit:
        "slp_mixed_center_finite_weighted_positive_fiber_mass TYPE('i)
            TYPE('j) (2 * B) root_weight cutoff left_potential (\<lambda>_. 1)
            cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) center =
          ?positive_mass center"
      by (rule slp_mixed_center_finite_weighted_positive_fiber_mass_unit)
    note raw_weighted_density =
      slp_mixed_center_finite_weighted_positive_fiber_mass_density[
        where R = "2 * B" and root_weight = root_weight and cutoff = cutoff
          and left_potential = left_potential
          and left_terminal_value = "\<lambda>_ :: slp_point. (1 :: complex)"
          and right_potential = right_potential
          and right_terminal_value = "\<lambda>_ :: slp_point. (1 :: complex)"
          and center_factor = "\<lambda>_ :: slp_point. (1 :: complex)"
          and center = center and 'i = 'i and 'j = 'j,
        OF root_weight_measurable cutoff_measurable
          left_potential_measurable unit_measurable
          right_potential_measurable unit_measurable]
    have weighted_density:
        "slp_mixed_center_finite_weighted_positive_fiber_mass TYPE('i)
            TYPE('j) (2 * B) root_weight cutoff left_potential (\<lambda>_. 1)
            cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) center =
          ennreal (cmod (1 :: complex)) * ?density center"
      using raw_weighted_density by simp
    show ?thesis
      using weighted_unit weighted_density by simp
  qed
  have density_lp: "slp_positive_ennreal_lp_on_plane ?dual ?density"
    by (rule slp_mixed_center_density_unit_terminal_all_orders_finite_target[
          OF radius_nonnegative p_lower p_upper dual_lower X_measurable
            X_bounded cutoff_measurable left_potential_lp right_potential_lp
            root_weight_lp root_weight_outside cutoff_cmod_bound
            C_nonnegative])
  have kernel_dominated:
      "AE center in lborel.
        ennreal (norm_class.norm (?kernel center)) \<le> ?density center"
    using kernel_positive_bound by (simp only: positive_mass_density)
  have lifted_norm_lp:
      "slp_positive_ennreal_lp_on_plane ?dual
        (\<lambda>center. ennreal (norm_class.norm (?kernel center)))"
    by (rule slp_complex_kernel_lp_of_positive_density_domination[
          OF dual_positive density_lp kernel_measurable kernel_dominated])
  have kernel_power_integrable:
      "integrable lborel
        (\<lambda>center. norm_class.norm (?kernel center) powr ?dual)"
    using lifted_norm_lp
    unfolding slp_positive_ennreal_lp_on_plane_def by simp
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using kernel_measurable kernel_power_integrable by blast
qed

end

end
