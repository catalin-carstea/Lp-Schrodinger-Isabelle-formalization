theory Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Smooth_Error_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Finite_Oscillatory_Output_Bounds"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Smooth_Error_Decay"
begin

section \<open>Finite right one-sided smooth-error decay\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_branch_finite_oscillatory_center_average_error_decay:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and cutoff potential phi :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
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
    and phi_integrable: "integrable lborel phi"
    and uniform_convergence:
      "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi at_top"
  shows
    "((\<lambda>tau.
        slp_right_branch_finite_oscillatory_integral TYPE('i) tau potential
          cutoff potential (slp_cauchy_transform orientation potential)
          (\<lambda>output. slp_center_average tau phi output - phi output))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?terminal_value = "slp_cauchy_transform orientation potential"
  let ?terminal_weight = "\<lambda>x.
    ennreal (Real_Vector_Spaces.norm (?terminal_value x))"
  let ?terminal_majorant =
    "slp_positive_terminal_riesz_weight (2 * B) potential"
  let ?error = "\<lambda>tau output.
    slp_center_average tau phi output - phi output"
  let ?error_weight = "\<lambda>tau output.
    ennreal (Real_Vector_Spaces.norm (?error tau output))"
  let ?actual = "\<lambda>tau. \<integral>\<^sup>+ output.
    slp_positive_root_output_density (2 * B) cutoff potential
      ?terminal_weight CARD('i) potential output * ?error_weight tau output
    \<partial>lborel"
  let ?majorant = "\<lambda>tau. \<integral>\<^sup>+ output.
    slp_positive_root_output_density (2 * B) cutoff potential
      ?terminal_majorant CARD('i) potential output * ?error_weight tau output
    \<partial>lborel"
  let ?packed = "\<lambda>tau. \<integral>\<^sup>+ coordinates.
    case_prod (slp_left_branch_positive_amplitude_packed (2 * B) potential
      cutoff potential ?terminal_value (?error tau)) coordinates
    \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
      (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))"
  let ?I = "\<lambda>tau.
    slp_right_branch_finite_oscillatory_integral TYPE('i) tau potential
      cutoff potential ?terminal_value (?error tau)"
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_value_measurable:
      "?terminal_value \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper potential_lp])
  have terminal_weight_measurable:
      "?terminal_weight \<in> borel_measurable lborel"
    using terminal_value_measurable by measurable
  have terminal_majorant_measurable:
      "?terminal_majorant \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          potential_measurable])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have average_measurable:
      "slp_center_average tau phi \<in> borel_measurable lborel"
    for tau
    by (rule slp_center_average_measurable[OF phi_integrable])
  have error_measurable:
      "?error tau \<in> borel_measurable lborel"
    for tau
    using average_measurable[of tau] phi_measurable by measurable
  have error_weight_measurable:
      "?error_weight tau \<in> borel_measurable lborel"
    for tau
    using error_measurable[of tau] by measurable
  have support_radius:
      "Real_Vector_Spaces.norm (x - y) \<le> 2 * B"
    if "cutoff x \<noteq> 0" "potential y \<noteq> 0"
    for x y :: slp_point
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          cutoff_support[OF that(1)] potential_support[OF that(2)]])
  have terminal_weight_le:
      "ennreal (Real_Vector_Spaces.norm (cutoff x)) *
          ?terminal_weight x \<le>
        ennreal (Real_Vector_Spaces.norm (cutoff x)) *
          ?terminal_majorant x"
    for x
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF
          support_radius])
  have actual_le_majorant: "?actual tau \<le> ?majorant tau" for tau
    by (rule slp_positive_root_output_density_pairing_cutoff_mono[OF
          cutoff_measurable potential_measurable terminal_weight_measurable
          terminal_majorant_measurable potential_measurable
          error_weight_measurable terminal_weight_le])
  have majorant_decay: "(?majorant \<longlongrightarrow> 0) at_top"
    by (rule
        slp_positive_root_output_density_terminal_weighted_center_average_error_nn_integral_tendsto_zero[
          where R = "2 * B" and C = C and p = p and X = X
            and cutoff = cutoff and potential = potential and phi = phi
            and n = "CARD('i)",
          OF _ p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp potential_outside cutoff_bound C_nonnegative
            phi_integrable uniform_convergence])
      (use B_nonnegative in simp)
  have packed_eq_actual: "?packed tau = ?actual tau" for tau
  proof -
    note pairing =
      slp_left_branch_positive_amplitude_packed_terminal_pairing[
        where 'i = 'i and R = "2 * B" and root_weight = potential
          and cutoff = cutoff and potential = potential
          and terminal_value = ?terminal_value and output_factor = "?error tau",
        OF potential_measurable cutoff_measurable potential_measurable
          terminal_value_measurable error_measurable]
    show ?thesis
      using pairing
      unfolding slp_left_one_sided_output_density_def
      by simp
  qed
  have eventually_majorant_lt_one:
      "eventually (\<lambda>tau. ?majorant tau < (1 :: ennreal)) at_top"
    using order_tendstoD(2)[OF majorant_decay, of "1 :: ennreal"]
    by simp
  have eventually_norm_le_majorant:
      "eventually (\<lambda>tau.
        ennreal (Real_Vector_Spaces.norm (?I tau)) \<le> ?majorant tau)
        at_top"
    using eventually_majorant_lt_one
  proof eventually_elim
    case (elim tau)
    have majorant_lt_top: "?majorant tau < top_class.top"
      by (rule less_trans[OF elim]) simp
    have actual_lt_top: "?actual tau < top_class.top"
      by (rule le_less_trans[OF actual_le_majorant majorant_lt_top])
    have packed_finite: "?packed tau < top_class.top"
      using packed_eq_actual[of tau] actual_lt_top by simp
    have oscillatory_bound:
        "ennreal (Real_Vector_Spaces.norm (?I tau)) \<le> ?actual tau"
    proof -
      have terminal_bound:
          "ennreal (Real_Vector_Spaces.norm (?I tau)) \<le>
            (\<integral>\<^sup>+ output.
              slp_right_one_sided_output_density (2 * B) cutoff potential
                ?terminal_weight CARD('i) potential output *
              ?error_weight tau output
              \<partial>lborel)"
      proof (rule slp_right_branch_finite_oscillatory_integral_terminal_bound[
          where 'i = 'i and B = B and omega = tau
            and root_weight = potential and cutoff = cutoff
            and potential = potential and terminal_value = ?terminal_value
            and output_factor = "?error tau"])
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
        show "?terminal_value \<in> borel_measurable lborel"
          by (rule terminal_value_measurable)
      next
        show "?error tau \<in> borel_measurable lborel"
          by (rule error_measurable)
      next
        show "?packed tau < \<infinity>"
          using packed_finite by simp
      qed
      show ?thesis
        using terminal_bound
        unfolding slp_right_one_sided_output_density_def by simp
    qed
    show ?case
      by (rule order_trans[OF oscillatory_bound actual_le_majorant])
  qed
  have ennreal_norm_decay:
      "((\<lambda>tau. ennreal (Real_Vector_Spaces.norm (?I tau)))
        \<longlongrightarrow> 0) at_top"
    by (rule tendsto_sandwich[where f = "\<lambda>_. 0" and h = ?majorant])
      (use eventually_norm_le_majorant majorant_decay in auto)
  have real_norm_decay:
      "((\<lambda>tau. Real_Vector_Spaces.norm (?I tau)) \<longlongrightarrow> 0)
        at_top"
  proof -
    have cast_decay:
        "((\<lambda>tau. ennreal (Real_Vector_Spaces.norm (?I tau)))
          \<longlongrightarrow> ennreal 0) at_top"
      using ennreal_norm_decay by simp
    show ?thesis
      by (rule tendsto_ennrealD[OF cast_decay])
        (simp_all add: eventuallyI)
  qed
  show ?thesis
    using real_norm_decay by (rule tendsto_norm_zero_cancel)
qed

end

end
