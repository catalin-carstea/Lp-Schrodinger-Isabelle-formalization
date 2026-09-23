theory Inverse_Schrodinger_Lp_Left_Born_Finite_Cancellation_V2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_One_Sided_Finite_Cancellation_Amplitude_Discharge"
begin

section \<open>Identification of the finite left Born term with cancellation\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_born_functional_eq_finite_cancellation_model_v2:
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
    "slp_left_born_functional CARD('i) tau phi potential cutoff potential
        orientation =
      slp_left_branch_finite_cancellation_model_v2 TYPE('i) tau potential
        cutoff potential (slp_cauchy_transform orientation potential) phi"
proof -
  let ?terminal = "slp_cauchy_transform orientation potential"
  let ?evaluated_pair =
    "slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
        cutoff potential ?terminal (slp_center_average tau phi) -
      slp_left_branch_finite_oscillatory_integral TYPE('i) tau potential
        cutoff potential (\<lambda>_. 1)
          (slp_center_average tau (\<lambda>u. phi u * ?terminal u))"
  have born_evaluated:
      "slp_left_born_functional CARD('i) tau phi potential cutoff potential
          orientation = ?evaluated_pair"
    by (rule slp_left_born_functional_eq_finite_center_cauchy_pair_lp_root[
          where B = B and C = C and p = p and X = X
            and root_weight = potential,
          OF B_nonnegative potential_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp potential_lp potential_outside cutoff_bound
            C_nonnegative phi_test])
  have cancellation_evaluated:
      "slp_left_branch_finite_cancellation_model_v2 TYPE('i) tau potential
          cutoff potential ?terminal phi = ?evaluated_pair"
    by (rule
      slp_left_branch_finite_cancellation_model_v2_eq_evaluated_pair_lp_root[
        where B = B and C = C and p = p and X = X,
        OF B_nonnegative cutoff_support potential_support p_lower p_upper
          X_measurable X_bounded potential_lp potential_outside
          cutoff_measurable cutoff_bound C_nonnegative phi_test source_l2
          center_source_l2])
  show ?thesis
    using born_evaluated cancellation_evaluated by simp
qed

end

end
