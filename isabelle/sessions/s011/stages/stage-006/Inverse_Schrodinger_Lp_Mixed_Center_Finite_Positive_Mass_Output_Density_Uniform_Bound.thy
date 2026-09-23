theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Mass_Output_Density_Uniform_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Mass_Output_Density_Factorization"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Output_Density_Finite_Unit_Mass_Uniform"
begin

section \<open>Mixed positive-mass majorant through uniform density caps\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_positive_mass_output_density_uniform_bound:
  fixes R C p :: real
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_lp:
      "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp:
      "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "\<exists>(left_cap :: ennreal) (right_cap :: ennreal).
      left_cap < top_class.top \<and>
      right_cap < top_class.top \<and>
      (\<forall>root.
        nn_integral lborel
          (slp_positive_output_density R cutoff left_potential (\<lambda>_. 1)
            CARD('i::finite) root) \<le> left_cap) \<and>
      (\<forall>root.
        nn_integral lborel
          (slp_positive_output_density R cutoff right_potential (\<lambda>_. 1)
            CARD('j::finite) root) \<le> right_cap) \<and>
      nn_integral lborel (\<lambda>center.
        slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) R
          root_weight cutoff left_potential cutoff right_potential center) \<le>
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root))) * left_cap * right_cap"
proof -
  have left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  obtain left_cap where left_cap_finite: "left_cap < top_class.top"
    and left_mass_bound:
      "\<And>root.
        nn_integral lborel
          (slp_positive_output_density R cutoff left_potential (\<lambda>_. 1)
            CARD('i) root) \<le> left_cap"
    using slp_positive_output_density_finite_unit_mass_uniform[
      where 'i = 'i and R = R and C = C and p = p and cutoff = cutoff
        and potential = left_potential,
      OF radius_nonnegative p_lower p_upper cutoff_measurable
        left_potential_lp cutoff_bound C_nonnegative]
    by blast
  obtain right_cap where right_cap_finite: "right_cap < top_class.top"
    and right_mass_bound:
      "\<And>root.
        nn_integral lborel
          (slp_positive_output_density R cutoff right_potential (\<lambda>_. 1)
            CARD('j) root) \<le> right_cap"
    using slp_positive_output_density_finite_unit_mass_uniform[
      where 'i = 'j and R = R and C = C and p = p and cutoff = cutoff
        and potential = right_potential,
      OF radius_nonnegative p_lower p_upper cutoff_measurable
        right_potential_lp cutoff_bound C_nonnegative]
    by blast
  have integrand_bound:
      "ennreal (cmod (root_weight root)) *
          nn_integral lborel
            (slp_positive_output_density R cutoff left_potential (\<lambda>_. 1)
              CARD('i) root) *
          nn_integral lborel
            (slp_positive_output_density R cutoff right_potential (\<lambda>_. 1)
              CARD('j) root) \<le>
        ennreal (cmod (root_weight root)) * left_cap * right_cap"
    for root
  proof -
    have first:
        "ennreal (cmod (root_weight root)) *
            nn_integral lborel
              (slp_positive_output_density R cutoff left_potential (\<lambda>_. 1)
                CARD('i) root) \<le>
          ennreal (cmod (root_weight root)) * left_cap"
      by (intro mult_left_mono left_mass_bound) simp
    show ?thesis
      by (intro mult_mono first right_mass_bound) simp_all
  qed
  note factorization =
    slp_mixed_center_finite_positive_mass_output_density_factorization[
      OF root_weight_measurable cutoff_measurable left_potential_measurable
        cutoff_measurable right_potential_measurable,
      where R = R and 'i = 'i and 'j = 'j]
  have dominated:
      "nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root)) *
            nn_integral lborel
              (slp_positive_output_density R cutoff left_potential (\<lambda>_. 1)
                CARD('i) root) *
            nn_integral lborel
              (slp_positive_output_density R cutoff right_potential (\<lambda>_. 1)
                CARD('j) root)) \<le>
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root)) * left_cap * right_cap)"
    by (rule nn_integral_mono) (rule integrand_bound)
  have constants_extracted:
      "nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root)) * left_cap * right_cap) =
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root))) * left_cap * right_cap"
    by (simp add: nn_integral_multc)
  have total_bound:
      "nn_integral lborel (\<lambda>center.
          slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) R
            root_weight cutoff left_potential cutoff right_potential center) \<le>
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root))) * left_cap * right_cap"
    using factorization dominated constants_extracted by simp
  show ?thesis
    using left_cap_finite right_cap_finite left_mass_bound right_mass_bound
      total_bound
    by blast
qed

end

end
