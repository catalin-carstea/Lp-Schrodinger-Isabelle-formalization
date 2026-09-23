theory Inverse_Schrodinger_Lp_Cauchy_Packed_Potential_Root
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Packed_Bounded_Support"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Root_Lp"
begin

section \<open>Potential-root packed finiteness for a Cauchy terminal\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_positive_amplitude_packed_cauchy_potential_root_lt_top:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and cutoff potential test :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
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
    and test_lp:
      "aim_complex_lp_on_plane (slp_branch_holder_exponent p) test"
  shows
    "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          potential cutoff potential
          (slp_cauchy_transform orientation potential) test)
          coordinates
      \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
      top_class.top"
proof -
  have potential_integrable: "integrable lborel potential"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded potential_lp potential_outside])
      (use p_lower in simp)
  show ?thesis
    by (rule
        slp_left_branch_positive_amplitude_packed_cauchy_bounded_support_lt_top[
          OF potential_integrable B_nonnegative p_lower p_upper
            cutoff_measurable potential_lp cutoff_bound C_nonnegative
            cutoff_support potential_support test_lp])
qed

end

end
