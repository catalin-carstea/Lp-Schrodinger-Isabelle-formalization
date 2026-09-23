theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Mass_Finite
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Uniform"
begin

section \<open>Finiteness of the global finite mixed positive mass\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_positive_mass_finite:
  fixes R C p :: real
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_lp:
      "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp:
      "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_weight_integrable: "integrable lborel root_weight"
  shows
    "nn_integral lborel (\<lambda>center.
        slp_mixed_center_finite_positive_fiber_mass TYPE('i::finite)
          TYPE('j::finite) R root_weight cutoff left_potential
          cutoff right_potential center) < top_class.top"
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
  have root_norm_measurable[measurable]:
      "(\<lambda>root. ennreal (cmod (root_weight root)))
        \<in> borel_measurable lborel"
    by measurable
  obtain left_cap where left_cap_finite: "left_cap < top_class.top"
    and left_mass_bound:
      "\<And>root.
        slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
          left_potential (\<lambda>_. 1) (\<lambda>_. 1) root \<le> left_cap"
    using slp_left_branch_positive_inner_mass_finite_unit_uniform[
      where 'i = 'i and R = R and C = C and p = p and cutoff = cutoff
        and potential = left_potential,
      OF radius_nonnegative p_lower p_upper cutoff_measurable
        left_potential_lp cutoff_bound C_nonnegative]
    by blast
  obtain right_cap where right_cap_finite: "right_cap < top_class.top"
    and right_mass_bound:
      "\<And>root.
        slp_left_branch_positive_inner_mass_finite TYPE('j) R cutoff
          right_potential (\<lambda>_. 1) (\<lambda>_. 1) root \<le> right_cap"
    using slp_left_branch_positive_inner_mass_finite_unit_uniform[
      where 'i = 'j and R = R and C = C and p = p and cutoff = cutoff
        and potential = right_potential,
      OF radius_nonnegative p_lower p_upper cutoff_measurable
        right_potential_lp cutoff_bound C_nonnegative]
    by blast
  have integrand_bound:
      "ennreal (cmod (root_weight root)) *
          slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
            left_potential (\<lambda>_. 1) (\<lambda>_. 1) root *
          slp_left_branch_positive_inner_mass_finite TYPE('j) R cutoff
            right_potential (\<lambda>_. 1) (\<lambda>_. 1) root \<le>
        ennreal (cmod (root_weight root)) * left_cap * right_cap"
    for root
  proof -
    have first:
        "ennreal (cmod (root_weight root)) *
            slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
              left_potential (\<lambda>_. 1) (\<lambda>_. 1) root \<le>
          ennreal (cmod (root_weight root)) * left_cap"
      by (intro mult_left_mono left_mass_bound) simp
    show ?thesis
      by (intro mult_mono first right_mass_bound) simp_all
  qed
  have total_bound:
      "nn_integral lborel (\<lambda>center.
          slp_mixed_center_finite_positive_fiber_mass TYPE('i)
            TYPE('j) R root_weight cutoff left_potential cutoff
            right_potential center) \<le>
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root))) * left_cap * right_cap"
  proof -
    note factorization =
      slp_mixed_center_finite_positive_mass_factorization[
        OF root_weight_measurable cutoff_measurable
          left_potential_measurable cutoff_measurable
          right_potential_measurable,
        where R = R and 'i = 'i and 'j = 'j]
    have factorization_exact:
      "nn_integral lborel (\<lambda>center.
          slp_mixed_center_finite_positive_fiber_mass TYPE('i)
            TYPE('j) R root_weight cutoff left_potential cutoff
            right_potential center) =
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root)) *
            slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
              left_potential (\<lambda>_. 1) (\<lambda>_. 1) root *
            slp_left_branch_positive_inner_mass_finite TYPE('j) R cutoff
              right_potential (\<lambda>_. 1) (\<lambda>_. 1) root)"
      by (rule factorization)
    have dominated:
      "nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root)) *
            slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
              left_potential (\<lambda>_. 1) (\<lambda>_. 1) root *
            slp_left_branch_positive_inner_mass_finite TYPE('j) R cutoff
              right_potential (\<lambda>_. 1) (\<lambda>_. 1) root) \<le>
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root)) * left_cap * right_cap)"
      by (rule nn_integral_mono) (rule integrand_bound)
    have constants_extracted:
      "nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root)) * left_cap * right_cap) =
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root))) * left_cap * right_cap"
      by (simp add: nn_integral_multc)
    show ?thesis
      using factorization_exact dominated constants_extracted by simp
  qed
  have root_mass_finite:
      "nn_integral lborel (\<lambda>root.
        ennreal (cmod (root_weight root))) < top_class.top"
    using root_weight_integrable
    unfolding integrable_iff_bounded by simp
  have majorant_finite:
      "nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root))) * left_cap * right_cap <
        top_class.top"
    using root_mass_finite left_cap_finite right_cap_finite
    by (simp add: ennreal_mult_less_top)
  show ?thesis
    by (rule le_less_trans[OF total_bound majorant_finite])
qed

end

end
