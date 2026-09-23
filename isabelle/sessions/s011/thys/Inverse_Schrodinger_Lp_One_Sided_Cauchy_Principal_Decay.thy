theory Inverse_Schrodinger_Lp_One_Sided_Cauchy_Principal_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Packed_Output_Principal_Majorant"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Packed_Potential_Root"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Principal_Integral"
begin

section \<open>Concrete finite one-sided principal decay with a Cauchy terminal\<close>

lemma slp_test_function_aim_complex_lp_on_plane:
  assumes q_positive: "0 < q"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "aim_complex_lp_on_plane q phi"
proof -
  let ?X = "closure {x. phi x \<noteq> 0}"
  have X_compact: "compact ?X"
    using phi_test unfolding slp_test_function_on_def by blast
  have X_measurable: "?X \<in> sets lborel"
    using borel_compact[OF X_compact] by simp
  have X_bounded: "bounded ?X"
    by (rule compact_imp_bounded[OF X_compact])
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have phi_bounded: "bounded (range phi)"
    by (rule slp_test_function_integrable_bounded(2)[OF phi_test])
  obtain C where phi_bound: "\<And>x. cmod (phi x) \<le> C"
    using phi_bounded unfolding bounded_iff by auto
  have C_nonnegative: "0 \<le> C"
  proof -
    have "0 \<le> cmod (phi 0)" by simp
    then show ?thesis using phi_bound[of 0] by linarith
  qed
  have indicator_integrable:
      "integrable lborel (indicator ?X :: slp_point \<Rightarrow> real)"
    using X_measurable emeasure_bounded_finite[OF X_bounded]
    by (simp add: integrable_indicator_iff)
  have majorant_integrable:
      "integrable lborel
        (\<lambda>x. (C powr q) * indicator ?X x)"
    using indicator_integrable by simp
  have power_measurable:
      "(\<lambda>x. cmod (phi x) powr q) \<in> borel_measurable lborel"
    using phi_measurable by measurable
  have pointwise_bound:
      "AE x in lborel.
        Real_Vector_Spaces.norm (cmod (phi x) powr q) \<le>
          Real_Vector_Spaces.norm ((C powr q) * indicator ?X x)"
  proof (rule AE_I2)
    fix x :: slp_point
    show "Real_Vector_Spaces.norm (cmod (phi x) powr q) \<le>
        Real_Vector_Spaces.norm ((C powr q) * indicator ?X x)"
    proof (cases "x \<in> ?X")
      case True
      have power_bound: "cmod (phi x) powr q \<le> C powr q"
        by (rule powr_mono2[OF less_imp_le[OF q_positive]
              norm_ge_zero phi_bound])
      then show ?thesis
        using True C_nonnegative by simp
    next
      case False
      have phi_zero: "phi x = 0"
        using False by auto
      then show ?thesis
        using False q_positive by simp
    qed
  qed
  have power_integrable:
      "integrable lborel (\<lambda>x. cmod (phi x) powr q)"
    by (rule Bochner_Integration.integrable_bound[OF
          majorant_integrable power_measurable pointwise_bound])
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using phi_measurable power_integrable by simp
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_principal_finite_integral_cauchy_decay:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and cutoff potential phi :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside: "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "((\<lambda>omega. slp_left_branch_principal_finite_integral TYPE('i)
        omega potential cutoff potential
          (slp_cauchy_transform orientation potential) phi)
      \<longlongrightarrow> 0) at_top"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_measurable:
      "slp_cauchy_transform orientation potential \<in>
        borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper potential_lp])
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have holder_positive: "0 < slp_branch_holder_exponent p"
    using slp_branch_weighted_exponents(3)[OF p_lower p_upper]
    by linarith
  have phi_lp:
      "aim_complex_lp_on_plane (slp_branch_holder_exponent p) phi"
    by (rule slp_test_function_aim_complex_lp_on_plane[OF
          holder_positive phi_test])
  have outside_self: "\<And>x. x \<notin> X \<Longrightarrow> x \<notin> X"
    by simp
  have cutoff_nonzero_self:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> cutoff x \<noteq> 0"
    by simp
  have potential_nonzero_self:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> potential x \<noteq> 0"
    by simp
  note terminal_majorant_finite_conditional =
        slp_left_branch_positive_amplitude_packed_cauchy_potential_root_lt_top[
          where B = B and C = C and p = p and X = X and cutoff = cutoff
            and potential = potential and test = phi and orientation = orientation,
          OF B_nonnegative p_lower p_upper X_measurable X_bounded potential_lp
            potential_outside cutoff_measurable cutoff_bound C_nonnegative
            cutoff_support potential_support phi_lp]
  note terminal_majorant_finite = terminal_majorant_finite_conditional[
    OF outside_self cutoff_nonzero_self potential_nonzero_self]
  have terminal_majorant_finite_exact:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          potential cutoff potential
          (slp_cauchy_transform orientation potential) phi)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        top_class.top"
    by (rule terminal_majorant_finite)
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  note output_majorant_finite_conditional =
        slp_left_branch_positive_amplitude_packed_unit_terminal_test_cauchy_lt_top[
          where R = "2 * B" and C = C and p = p and X = X
            and cutoff = cutoff and potential = potential and phi = phi
            and orientation = orientation,
          OF radius_nonnegative p_lower p_upper X_measurable X_bounded
            cutoff_measurable potential_lp potential_outside cutoff_bound
            C_nonnegative phi_test]
  note output_majorant_finite = output_majorant_finite_conditional[OF outside_self]
  have output_majorant_finite_exact:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          potential cutoff potential (\<lambda>_. 1)
          (\<lambda>u. phi u * slp_cauchy_transform orientation potential u))
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        top_class.top"
    by (rule output_majorant_finite)
  show ?thesis
  proof (rule slp_left_branch_principal_finite_integral_decay[
      where B = B and root_weight = potential and cutoff = cutoff
        and potential = potential
        and terminal_value = "slp_cauchy_transform orientation potential"
        and test = phi])
    show "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
      by (rule stationary_phase)
  next
    show "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
      by (rule density)
  next
    show "0 \<le> B" by (rule B_nonnegative)
  next
    fix x :: slp_point
    assume "potential x \<noteq> 0"
    then show "Real_Vector_Spaces.norm x \<le> B" by (rule potential_support)
  next
    fix x :: slp_point
    assume "cutoff x \<noteq> 0"
    then show "Real_Vector_Spaces.norm x \<le> B" by (rule cutoff_support)
  next
    fix x :: slp_point
    assume "potential x \<noteq> 0"
    then show "Real_Vector_Spaces.norm x \<le> B" by (rule potential_support)
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
    show "slp_cauchy_transform orientation potential \<in>
        borel_measurable lborel"
      by (rule terminal_measurable)
  next
    show "phi \<in> borel_measurable lborel"
      by (rule phi_measurable)
  next
    show "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          potential cutoff potential
          (slp_cauchy_transform orientation potential) phi)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
      using terminal_majorant_finite_exact by simp
  next
    show "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          potential cutoff potential (\<lambda>_. 1)
          (\<lambda>u. phi u * slp_cauchy_transform orientation potential u))
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
      using output_majorant_finite_exact by simp
  qed
qed

end

end
