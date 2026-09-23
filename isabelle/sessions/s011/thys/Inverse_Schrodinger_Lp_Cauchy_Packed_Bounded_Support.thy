theory Inverse_Schrodinger_Lp_Cauchy_Packed_Bounded_Support
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Packed_Positive_Amplitude"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Support"
begin

section \<open>Bounded-support packed finiteness for a Cauchy terminal\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_positive_amplitude_packed_cauchy_bounded_support_lt_top:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and root_weight cutoff potential output_factor ::
      "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes root_weight_integrable: "integrable lborel root_weight"
    and B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and output_factor_lp:
      "aim_complex_lp_on_plane (slp_branch_holder_exponent p) output_factor"
  shows
    "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential
          (slp_cauchy_transform orientation potential) output_factor)
          coordinates
      \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
      top_class.top"
proof (rule
    slp_left_branch_positive_amplitude_packed_cauchy_terminal_cutoff_lt_top[
      OF root_weight_integrable])
  show "0 \<le> 2 * B"
    using B_nonnegative by simp
next
  show "1 < p" by (rule p_lower)
next
  show "p < 2" by (rule p_upper)
next
  show "cutoff \<in> borel_measurable lborel"
    by (rule cutoff_measurable)
next
  show "aim_complex_lp_on_plane p potential"
    by (rule potential_lp)
next
  fix x :: slp_point
  show "cmod (cutoff x) \<le> C"
    by (rule cutoff_bound)
next
  show "0 \<le> C" by (rule C_nonnegative)
next
  fix x y :: slp_point
  assume cutoff_nonzero: "cutoff x \<noteq> 0"
    and potential_nonzero: "potential y \<noteq> 0"
  show "Real_Vector_Spaces.norm (x - y) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          cutoff_support[OF cutoff_nonzero]
          potential_support[OF potential_nonzero]])
next
  show
    "aim_complex_lp_on_plane (slp_branch_holder_exponent p) output_factor"
    by (rule output_factor_lp)
qed

end

end
