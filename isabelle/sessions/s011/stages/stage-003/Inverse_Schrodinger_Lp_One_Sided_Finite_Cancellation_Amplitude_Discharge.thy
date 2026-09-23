theory Inverse_Schrodinger_Lp_One_Sided_Finite_Cancellation_Amplitude_Discharge
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_One_Sided_Finite_Cancellation_Algebra"
begin

section \<open>Finite cancellation-amplitude premise discharge\<close>

lemma slp_left_branch_complex_amplitude_finite_output_mult:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
        terminal_value output_factor coordinates =
      slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value (\<lambda>_. 1) coordinates *
        output_factor
          (slp_left_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates)))"
  unfolding slp_left_branch_complex_amplitude_finite_def
  by simp

theorem slp_left_branch_complex_amplitude_finite_bounded_output_integrable:
  fixes branch_dummy :: "'i::finite itself"
    and output_factor :: "slp_point \<Rightarrow> complex"
    and K :: real
  assumes unit_output_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    and output_factor_bound:
      "\<And>x. Real_Vector_Spaces.norm (output_factor x) \<le> K"
  shows
    "integrable lborel
      (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
        terminal_value output_factor ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
proof -
  let ?output =
    "\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      slp_left_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))"
  let ?base =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value (\<lambda>_. 1) ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?target =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value output_factor ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  have K_nonnegative: "0 \<le> K"
    by (rule order_trans[OF norm_ge_zero output_factor_bound])
  have output_measurable: "?output \<in> borel_measurable lborel"
    by (rule slp_left_branch_finite_output_measurable)
  have output_factor_measurable_borel:
      "output_factor \<in> measurable borel borel"
    using output_factor_measurable by (simp only: measurable_lborel2)
  have output_comp_measurable:
      "(\<lambda>coordinates. output_factor (?output coordinates)) \<in>
        borel_measurable lborel"
    using measurable_compose[OF output_measurable
      output_factor_measurable_borel]
    by (simp only: comp_def)
  have base_measurable: "?base \<in> borel_measurable lborel"
    using unit_output_integrable by measurable
  have target_eq:
      "?target = (\<lambda>coordinates.
        ?base coordinates * output_factor (?output coordinates))"
    by (rule ext)
      (rule slp_left_branch_complex_amplitude_finite_output_mult)
  have target_measurable: "?target \<in> borel_measurable lborel"
    unfolding target_eq
    using base_measurable output_comp_measurable by measurable
  have scaled_integrable:
      "integrable lborel (\<lambda>coordinates. ?base coordinates * of_real K)"
    by (rule Bochner_Integration.integrable_mult_left)
      (use unit_output_integrable in simp)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF
      scaled_integrable target_measurable])
    show "AE coordinates in lborel.
        Real_Vector_Spaces.norm (?target coordinates) \<le>
          Real_Vector_Spaces.norm (?base coordinates * of_real K)"
    proof (intro always_eventually allI)
      fix coordinates :: "'i slp_left_branch_finite_coordinates"
      have factor_bound:
          "Real_Vector_Spaces.norm (output_factor (?output coordinates)) \<le> K"
        by (rule output_factor_bound)
      show
        "Real_Vector_Spaces.norm (?target coordinates) \<le>
          Real_Vector_Spaces.norm (?base coordinates * of_real K)"
        unfolding target_eq
        using mult_left_mono[OF factor_bound norm_ge_zero[of "?base coordinates"]]
        by (simp only: norm_mult norm_of_real abs_of_nonneg[OF K_nonnegative])
    qed
  qed
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_complex_amplitude_finite_unit_terminal_l2_integrable:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and cutoff potential output_factor :: "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and cutoff_support:
      "\<And>x :: slp_point. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x :: slp_point. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and output_factor_l2: "aim_complex_lp_on_plane 2 output_factor"
  shows
    "integrable lborel
      (slp_left_branch_complex_amplitude_finite potential cutoff potential
        (\<lambda>_. 1) output_factor ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
proof -
  let ?density =
    "slp_left_one_sided_output_density (2 * B) cutoff potential
      (\<lambda>_ :: slp_point. 1 :: ennreal) CARD('i) potential"
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have potential_integrable: "integrable lborel potential"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded potential_lp potential_outside])
      (use p_lower in simp)
  have output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    using output_factor_l2 unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable:
      "(\<lambda>_ :: slp_point. 1 :: complex) \<in> borel_measurable lborel"
    by measurable
  have unit_weight_measurable:
      "(\<lambda>_ :: slp_point. 1 :: ennreal) \<in> borel_measurable lborel"
    by measurable
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  have density_measurable: "?density \<in> borel_measurable lborel"
    unfolding slp_left_one_sided_output_density_def
    by (rule slp_positive_root_output_density_measurable[OF
          cutoff_measurable potential_measurable unit_weight_measurable
          potential_measurable])
  have density_mass_finite:
      "(\<integral>\<^sup>+ output. ?density output \<partial>lborel) <
        top_class.top"
    by (rule slp_left_one_sided_output_density_unweighted_mass_finite[OF
          radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
          cutoff_bound C_nonnegative potential_integrable])
  have density_finite:
      "AE output in lborel. ?density output < top_class.top"
  proof -
    have density_not_infinite:
        "(\<integral>\<^sup>+ output. ?density output \<partial>lborel) \<noteq>
          \<infinity>"
      using density_mass_finite by simp
    have "AE output in lborel. ?density output \<noteq> \<infinity>"
      by (rule nn_integral_noteq_infinite[OF
            density_measurable density_not_infinite])
    then show ?thesis
      by eventually_elim (simp add: less_top)
  qed
  have density_real_l2:
      "aim_real_lp_on_plane 2
        (\<lambda>output. enn2real (?density output))"
    by (rule slp_left_right_one_sided_output_density_real_all_orders_l2(2)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative])
  have density_l2: "slp_positive_ennreal_lp_on_plane 2 ?density"
    by (rule slp_positive_ennreal_lp_from_enn2real[OF
          density_measurable density_finite density_real_l2])
  have pairing_finite:
      "(\<integral>\<^sup>+ output. ?density output *
        ennreal (Real_Vector_Spaces.norm (output_factor output))
        \<partial>lborel) < top_class.top"
    by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[
          where q = 2 and r = 2, OF _ _ _ density_l2 output_factor_l2])
      simp_all
  have majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          potential cutoff potential (\<lambda>_. 1) output_factor) coordinates
        \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  proof -
    note pairing =
      slp_left_branch_positive_amplitude_packed_unit_terminal_pairing[
        where 'i = 'i and R = "2 * B" and root_weight = potential
          and cutoff = cutoff and potential = potential
          and output_factor = output_factor,
        OF potential_measurable cutoff_measurable potential_measurable
          output_factor_measurable]
    show ?thesis
      using pairing pairing_finite by simp
  qed
  show ?thesis
    by (rule slp_left_branch_complex_amplitude_finite_integrable[
          where B = B, OF B_nonnegative potential_support cutoff_support
            potential_support potential_measurable cutoff_measurable
            potential_measurable unit_measurable output_factor_measurable
            majorant_finite])
qed

theorem slp_left_branch_finite_cancellation_model_v2_eq_evaluated_pair_lp_root:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real
    and X :: "slp_point set"
    and cutoff potential phi :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and cutoff_support:
      "\<And>x :: slp_point. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x :: slp_point. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and phi_test: "slp_test_function_on UNIV phi"
    and source_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)"
    and center_source_l2:
      "aim_complex_lp_on_plane 2
        (slp_center_average tau
          (\<lambda>u. phi u * slp_cauchy_transform orientation potential u))"
  shows
    "slp_left_branch_finite_cancellation_model_v2 TYPE('i) tau potential
        cutoff potential (slp_cauchy_transform orientation potential) phi =
      slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
          cutoff potential (slp_cauchy_transform orientation potential)
            (slp_center_average tau phi) -
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
          cutoff potential (\<lambda>_. 1)
            (slp_center_average tau
              (\<lambda>u.
                phi u * slp_cauchy_transform orientation potential u))"
proof -
  let ?terminal = "slp_cauchy_transform orientation potential"
  let ?source = "\<lambda>u. phi u * ?terminal u"
  note phi_data = slp_test_function_integrable_bounded[OF phi_test]
  have phi_integrable: "integrable lborel phi"
    by (rule phi_data(1))
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  obtain K where phi_bound:
      "\<And>x. Real_Vector_Spaces.norm (phi x) \<le> K"
    using phi_data(2) unfolding bounded_iff by blast
  have center_phi_measurable:
      "slp_center_average tau phi \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF phi_integrable])
  have center_phi_bound:
      "\<And>x. Real_Vector_Spaces.norm (slp_center_average tau phi x) \<le>
        Real_Vector_Spaces.norm (of_real (tau / pi) :: complex) *
          integral\<^sup>L lborel (\<lambda>z. Real_Vector_Spaces.norm (phi z))"
    by (rule slp_center_average_fixed_tau_bound)
  have cauchy_unit_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite potential cutoff potential
          ?terminal (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_left_branch_complex_amplitude_finite_cauchy_integrable_lp_root[
        where B = B and C = C and p = p and X = X and root_weight = potential
          and cutoff = cutoff and potential = potential
          and orientation = orientation,
        OF B_nonnegative potential_support cutoff_support potential_support
          p_lower p_upper X_measurable X_bounded cutoff_measurable
          potential_lp potential_lp potential_outside cutoff_bound
          C_nonnegative])
  have terminal_base_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite potential cutoff potential
          ?terminal phi ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_left_branch_complex_amplitude_finite_bounded_output_integrable[
        OF cauchy_unit_amplitude_integrable phi_measurable phi_bound])
  have terminal_center_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite potential cutoff potential
          ?terminal (slp_center_average tau phi) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_left_branch_complex_amplitude_finite_bounded_output_integrable[
        OF cauchy_unit_amplitude_integrable center_phi_measurable
          center_phi_bound])
  have unit_base_source_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite potential cutoff potential
          (\<lambda>_. 1) ?source ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_left_branch_complex_amplitude_finite_unit_terminal_l2_integrable[
        where B = B and C = C and p = p and X = X and cutoff = cutoff
          and potential = potential and output_factor = ?source,
        OF B_nonnegative cutoff_support potential_support p_lower p_upper
          X_measurable X_bounded potential_lp potential_outside
          cutoff_measurable cutoff_bound C_nonnegative source_l2])
  have unit_center_source_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite potential cutoff potential
          (\<lambda>_. 1) (slp_center_average tau ?source) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_left_branch_complex_amplitude_finite_unit_terminal_l2_integrable[
        where B = B and C = C and p = p and X = X and cutoff = cutoff
          and potential = potential
          and output_factor = "slp_center_average tau ?source",
        OF B_nonnegative cutoff_support potential_support p_lower p_upper
          X_measurable X_bounded potential_lp potential_outside
          cutoff_measurable cutoff_bound C_nonnegative center_source_l2])
  show ?thesis
    by (rule
      slp_left_branch_finite_cancellation_model_v2_eq_evaluated_pair[
        OF terminal_center_amplitude_integrable
          terminal_base_amplitude_integrable
          unit_center_source_amplitude_integrable
          unit_base_source_amplitude_integrable])
qed

end

end
