theory Inverse_Schrodinger_Lp_One_Sided_Finite_L2_Error_Decay_V2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Born_Functional"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_L2_Error_Decay"
begin

section \<open>Residual-frequency-parametric finite one-sided L2 error decay\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_branch_finite_oscillatory_l2_error_decay_indexed_frequency:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and error :: "'a \<Rightarrow> slp_point \<Rightarrow> complex"
    and frequency :: "'a \<Rightarrow> real"
    and F :: "'a filter"
  assumes B_nonnegative: "0 \<le> B"
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
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and error_l2: "\<And>i. aim_complex_lp_on_plane 2 (error i)"
    and error_square_decay:
      "((\<lambda>i. \<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm (error i x)) ^ 2 \<partial>lborel)
        \<longlongrightarrow> 0) F"
  shows
    "((\<lambda>i.
        slp_left_branch_finite_oscillatory_integral TYPE('i) (frequency i)
          potential cutoff potential (\<lambda>_. 1) (error i))
      \<longlongrightarrow> 0) F"
proof -
  let ?density =
    "slp_left_one_sided_output_density (2 * B) cutoff potential
      (\<lambda>_ :: slp_point. 1 :: ennreal) CARD('i) potential"
  let ?pairing = "\<lambda>i. \<integral>\<^sup>+ output. ?density output *
    ennreal (Real_Vector_Spaces.norm (error i output)) \<partial>lborel"
  let ?packed = "\<lambda>i. \<integral>\<^sup>+ coordinates.
    case_prod (slp_left_branch_positive_amplitude_packed (2 * B) potential
      cutoff potential (\<lambda>_. 1) (error i)) coordinates
    \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
      (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))"
  let ?I = "\<lambda>i.
    slp_left_branch_finite_oscillatory_integral TYPE('i) (frequency i)
      potential cutoff potential (\<lambda>_. 1) (error i)"
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
  have density_measurable:
      "?density \<in> borel_measurable lborel"
    unfolding slp_left_one_sided_output_density_def
    by (rule slp_positive_root_output_density_measurable[OF
          cutoff_measurable potential_measurable unit_weight_measurable
          potential_measurable])
  have density_mass_finite:
      "(\<integral>\<^sup>+ output. ?density output \<partial>lborel) <
        top_class.top"
    by (rule slp_left_one_sided_output_density_unweighted_mass_finite[OF
          _ p_lower p_upper cutoff_measurable potential_lp cutoff_bound
          C_nonnegative potential_integrable])
      (use B_nonnegative in simp)
  have density_finite:
      "AE output in lborel. ?density output < top_class.top"
  proof -
    have "(\<integral>\<^sup>+ output. ?density output \<partial>lborel) \<noteq>
        \<infinity>"
      using density_mass_finite by simp
    then have "AE output in lborel. ?density output \<noteq> \<infinity>"
      by (rule nn_integral_noteq_infinite[OF density_measurable])
    then show ?thesis
      by eventually_elim (simp add: less_top)
  qed
  have density_real_l2:
      "aim_real_lp_on_plane 2 (\<lambda>output. enn2real (?density output))"
    by (rule slp_left_right_one_sided_output_density_real_all_orders_l2(2)[OF
          _ p_lower p_upper X_measurable X_bounded cutoff_measurable
          potential_lp potential_outside cutoff_bound C_nonnegative])
      (use B_nonnegative in simp)
  have density_l2: "slp_positive_ennreal_lp_on_plane 2 ?density"
    by (rule slp_positive_ennreal_lp_from_enn2real[OF
          density_measurable density_finite density_real_l2])
  have pairing_decay: "(?pairing \<longlongrightarrow> 0) F"
    by (rule slp_positive_ennreal_complex_l2_pairing_tendsto_zero[OF
          density_l2 error_l2 error_square_decay])
  have error_measurable:
      "error i \<in> borel_measurable lborel" for i
    using error_l2[of i] unfolding aim_complex_lp_on_plane_def by blast
  have packed_eq_pairing: "?packed i = ?pairing i" for i
    by (rule slp_left_branch_positive_amplitude_packed_unit_terminal_pairing[
          where 'i = 'i, OF potential_measurable cutoff_measurable
            potential_measurable error_measurable])
  have eventually_pairing_lt_one:
      "eventually (\<lambda>i. ?pairing i < (1 :: ennreal)) F"
    using order_tendstoD(2)[OF pairing_decay, of "1 :: ennreal"] by simp
  have eventually_norm_le_pairing:
      "eventually (\<lambda>i.
        ennreal (Real_Vector_Spaces.norm (?I i)) \<le> ?pairing i) F"
    using eventually_pairing_lt_one
  proof eventually_elim
    case (elim i)
    have pairing_finite: "?pairing i < top_class.top"
      by (rule less_trans[OF elim]) simp
    have packed_finite: "?packed i < top_class.top"
      using packed_eq_pairing[of i] pairing_finite by simp
    show "ennreal (Real_Vector_Spaces.norm (?I i)) \<le> ?pairing i"
    proof (rule
        slp_left_branch_finite_oscillatory_integral_unit_terminal_bound[
          where 'i = 'i and B = B and omega = "frequency i"
            and root_weight = potential and cutoff = cutoff
            and potential = potential and output_factor = "error i"])
      show "0 \<le> B" by (rule B_nonnegative)
    next
      fix x :: slp_point
      assume "potential x \<noteq> 0"
      then show "Real_Vector_Spaces.norm x \<le> B"
        by (rule potential_support)
    next
      fix x :: slp_point
      assume "cutoff x \<noteq> 0"
      then show "Real_Vector_Spaces.norm x \<le> B"
        by (rule cutoff_support)
    next
      fix x :: slp_point
      assume "potential x \<noteq> 0"
      then show "Real_Vector_Spaces.norm x \<le> B"
        by (rule potential_support)
    next
      show "potential \<in> borel_measurable lborel"
        by (rule potential_measurable)
    next
      show "cutoff \<in> borel_measurable lborel"
        by (rule cutoff_measurable)
    next
      show "potential \<in> borel_measurable lborel"
        by (rule potential_measurable)
    next
      show "error i \<in> borel_measurable lborel"
        by (rule error_measurable)
    next
      show "(\<integral>\<^sup>+ coordinates.
          case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
            potential cutoff potential (\<lambda>_. 1) (error i)) coordinates
          \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
          \<infinity>"
        using packed_eq_pairing[of i] pairing_finite by simp
    qed
  qed
  have norm_ennreal_decay:
      "((\<lambda>i. ennreal (Real_Vector_Spaces.norm (?I i)))
        \<longlongrightarrow> 0) F"
    by (rule tendsto_sandwich[where f = "\<lambda>_. 0" and h = ?pairing])
      (use eventually_norm_le_pairing pairing_decay in auto)
  have norm_real_decay:
      "((\<lambda>i. Real_Vector_Spaces.norm (?I i)) \<longlongrightarrow> 0) F"
  proof -
    have cast_decay:
        "((\<lambda>i. ennreal (Real_Vector_Spaces.norm (?I i)))
          \<longlongrightarrow> ennreal 0) F"
      using norm_ennreal_decay by simp
    show ?thesis
      by (rule tendsto_ennrealD[OF cast_decay]) simp_all
  qed
  show ?thesis
    using norm_real_decay by (rule tendsto_norm_zero_cancel)
qed

theorem
    slp_left_branch_finite_oscillatory_center_average_l2_error_decay_at_residual_frequency:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and cutoff potential source :: "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
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
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and source_l2: "aim_complex_lp_on_plane 2 source"
    and center_average_l2:
      "\<And>tau. aim_complex_lp_on_plane 2 (slp_center_average tau source)"
    and center_average_error_square_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x. ennreal (Real_Vector_Spaces.norm
          (slp_center_average tau source x - source x)) ^ 2 \<partial>lborel)
        \<longlongrightarrow> 0) at_top"
  shows
    "((\<lambda>tau.
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
          cutoff potential (\<lambda>_. 1)
          (\<lambda>output.
            slp_center_average tau source output - source output))
      \<longlongrightarrow> 0) at_top"
proof -
  have error_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>x. slp_center_average tau source x - source x)" for tau
    by (rule aim_complex_lp_on_plane_diff[OF zero_less_numeral
          center_average_l2 source_l2])
  show ?thesis
    by (rule
        slp_left_branch_finite_oscillatory_l2_error_decay_indexed_frequency[
          where 'i = 'i and B = B and C = C and p = p and X = X
            and cutoff = cutoff and potential = potential
            and error = "\<lambda>tau output.
              slp_center_average tau source output - source output"
            and frequency = "\<lambda>tau::real. tau" and F = at_top,
          OF B_nonnegative p_lower p_upper X_measurable X_bounded
            potential_lp potential_outside cutoff_measurable cutoff_bound
            C_nonnegative cutoff_support potential_support error_l2
            center_average_error_square_decay])
qed

end

end
