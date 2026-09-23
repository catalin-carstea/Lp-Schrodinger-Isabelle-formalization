theory Inverse_Schrodinger_Lp_Left_One_Sided_Finite_L2_Error_Positive_Tail
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_One_Sided_Finite_L2_Error_Decay_V2"
begin

section \<open>Positive-parameter tail form of left finite L2 error decay\<close>

context aim_planar_riesz_hls
begin

theorem
    slp_left_branch_finite_oscillatory_center_average_l2_error_decay_positive_tail:
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
      "\<And>tau. 0 < tau \<Longrightarrow>
        aim_complex_lp_on_plane 2 (slp_center_average tau source)"
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
  let ?actual = "\<lambda>tau output.
    slp_center_average tau source output - source output"
  let ?error = "\<lambda>tau output.
    if 0 < tau then ?actual tau output else 0"
  have error_l2:
      "aim_complex_lp_on_plane 2 (?error tau)" for tau
  proof (cases "0 < tau")
    case True
    then show ?thesis
      by (simp only: if_True)
        (rule aim_complex_lp_on_plane_diff[OF zero_less_numeral
          center_average_l2 source_l2])
  next
    case False
    then show ?thesis
      by (simp add: aim_complex_lp_on_plane_def)
  qed
  have tau_positive:
      "eventually (\<lambda>tau :: real. 0 < tau) at_top"
    by simp
  have eventual_mass_identity:
      "eventually (\<lambda>tau.
        (\<integral>\<^sup>+x. ennreal (Real_Vector_Spaces.norm
            (?actual tau x)) ^ 2 \<partial>lborel) =
        (\<integral>\<^sup>+x. ennreal (Real_Vector_Spaces.norm
            (?error tau x)) ^ 2 \<partial>lborel)) at_top"
    using tau_positive
    by eventually_elim simp
  have modified_square_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x. ennreal (Real_Vector_Spaces.norm
          (?error tau x)) ^ 2 \<partial>lborel) \<longlongrightarrow> 0) at_top"
    using center_average_error_square_decay
    by (rule tendsto_cong[OF eventual_mass_identity, THEN iffD1])
  have modified_decay:
      "((\<lambda>tau.
          slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
            cutoff potential (\<lambda>_. 1) (?error tau))
        \<longlongrightarrow> 0) at_top"
    by (rule
        slp_left_branch_finite_oscillatory_l2_error_decay_indexed_frequency[
          where 'i = 'i and B = B and C = C and p = p and X = X
            and cutoff = cutoff and potential = potential
            and error = ?error and frequency = "\<lambda>tau::real. tau"
            and F = at_top,
          OF B_nonnegative p_lower p_upper X_measurable X_bounded
            potential_lp potential_outside cutoff_measurable cutoff_bound
            C_nonnegative cutoff_support potential_support error_l2
            modified_square_decay])
  have eventual_integral_identity:
      "eventually (\<lambda>tau.
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
            cutoff potential (\<lambda>_. 1) (?actual tau) =
          slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
            cutoff potential (\<lambda>_. 1) (?error tau)) at_top"
    using tau_positive
    by eventually_elim simp
  from modified_decay show ?thesis
    by (rule tendsto_cong[OF eventual_integral_identity, THEN iffD2])
qed

end

end
