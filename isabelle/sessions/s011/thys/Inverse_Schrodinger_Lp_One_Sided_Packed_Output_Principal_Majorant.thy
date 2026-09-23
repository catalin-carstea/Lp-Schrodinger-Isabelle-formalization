theory Inverse_Schrodinger_Lp_One_Sided_Packed_Output_Principal_Majorant
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Packed_Unit_Terminal_Output_Pairing"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Test_Cauchy_Product_L2"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Complex_Pairing"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Packed_Positive_Amplitude"
begin

section \<open>Guarded L2 majorants for the output principal term\<close>

lemma slp_positive_ennreal_lp_from_enn2real:
  fixes F :: "slp_point \<Rightarrow> ennreal"
    and p :: real
  assumes F_measurable: "F \<in> borel_measurable lborel"
    and F_finite: "AE x in lborel. F x < top_class.top"
    and F_lp: "aim_real_lp_on_plane p (\<lambda>x. enn2real (F x))"
  shows "slp_positive_ennreal_lp_on_plane p F"
proof -
  have F_power_integrable:
      "integrable lborel (\<lambda>x. abs (enn2real (F x)) powr p)"
    using F_lp unfolding aim_real_lp_on_plane_def by blast
  have positive_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr p)"
    using F_power_integrable by simp
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    using F_measurable F_finite positive_power_integrable by blast
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_positive_amplitude_packed_unit_terminal_test_cauchy_lt_top:
  fixes branch_dummy :: "'i::finite itself"
    and R C p :: real
    and X :: "slp_point set"
    and cutoff potential phi :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside: "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed R potential
          cutoff potential (\<lambda>_. 1)
          (\<lambda>x. phi x * slp_cauchy_transform orientation potential x))
          coordinates
      \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
      top_class.top"
proof -
  let ?output_factor =
    "\<lambda>x. phi x * slp_cauchy_transform orientation potential x"
  let ?density =
    "slp_left_one_sided_output_density R cutoff potential (\<lambda>_. 1)
      CARD('i) potential"
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have potential_integrable: "integrable lborel potential"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded potential_lp potential_outside])
      (use p_lower in simp)
  have unit_weight_measurable:
      "(\<lambda>_ :: slp_point. 1 :: ennreal) \<in> borel_measurable lborel"
    by measurable
  have density_measurable: "?density \<in> borel_measurable lborel"
    unfolding slp_left_one_sided_output_density_def
    by (rule slp_positive_root_output_density_measurable[OF
          cutoff_measurable potential_measurable unit_weight_measurable
          potential_measurable])
  have density_mass_finite:
      "(\<integral>\<^sup>+ out. ?density out \<partial>lborel) < top_class.top"
    by (rule slp_left_one_sided_output_density_unweighted_mass_finite[OF
          radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
          cutoff_bound C_nonnegative potential_integrable])
  have density_finite:
      "AE out in lborel. ?density out < top_class.top"
  proof -
    have density_not_infinite:
        "(\<integral>\<^sup>+ out. ?density out \<partial>lborel) \<noteq>
          \<infinity>"
      using density_mass_finite by simp
    have "AE out in lborel. ?density out \<noteq> \<infinity>"
      by (rule nn_integral_noteq_infinite[
            where M = lborel and g = ?density, OF density_measurable
              density_not_infinite])
    then show ?thesis
      by eventually_elim (simp add: less_top)
  qed
  have density_l2:
      "aim_real_lp_on_plane 2 (\<lambda>out. enn2real (?density out))"
    by (rule slp_left_right_one_sided_output_density_real_all_orders_l2(2)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative])
  have positive_density_l2:
      "slp_positive_ennreal_lp_on_plane 2 ?density"
    by (rule slp_positive_ennreal_lp_from_enn2real[OF
          density_measurable density_finite density_l2])
  have output_factor_l2:
      "aim_complex_lp_on_plane 2 ?output_factor"
    by (rule slp_test_cauchy_product_l2[OF
          p_lower p_upper potential_lp phi_test])
  have output_factor_measurable:
      "?output_factor \<in> borel_measurable lborel"
    using output_factor_l2 unfolding aim_complex_lp_on_plane_def by blast
  have pairing_finite:
      "(\<integral>\<^sup>+ out. ?density out *
          ennreal (cmod (?output_factor out)) \<partial>lborel) < top_class.top"
    by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[
          where q = 2 and r = 2, OF _ _ _ positive_density_l2
            output_factor_l2]) simp_all
  have exact_pairing:
      "(\<integral>\<^sup>+ coordinates.
          case_prod (slp_left_branch_positive_amplitude_packed R potential
            cutoff potential (\<lambda>_. 1) ?output_factor) coordinates
        \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) =
        (\<integral>\<^sup>+ out. ?density out *
          ennreal (cmod (?output_factor out)) \<partial>lborel)"
    by (rule
        slp_left_branch_positive_amplitude_packed_unit_terminal_pairing[OF
          potential_measurable cutoff_measurable potential_measurable
          output_factor_measurable])
  show ?thesis
    using exact_pairing pairing_finite by simp
qed

end

end
