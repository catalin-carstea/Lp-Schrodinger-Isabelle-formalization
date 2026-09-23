theory Inverse_Schrodinger_Lp_Cauchy_Packed_Positive_Amplitude
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Measurable_Below_Two"
begin

section \<open>Packed positive-amplitude finiteness for a Cauchy terminal\<close>

locale aim_planar_riesz_hls_cauchy =
  aim_planar_riesz_hls + aim_planar_hls_cauchy

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_positive_amplitude_packed_cauchy_terminal_cutoff_lt_top:
  fixes branch_dummy :: "'i::finite itself"
    and R C p :: real
    and root_weight cutoff potential output_factor ::
      "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes root_weight_integrable: "integrable lborel root_weight"
    and radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and support_radius:
      "\<And>x y. \<lbrakk>cutoff x \<noteq> 0; potential y \<noteq> 0\<rbrakk> \<Longrightarrow>
        Real_Vector_Spaces.norm (x - y) \<le> R"
    and output_factor_lp:
      "aim_complex_lp_on_plane (slp_branch_holder_exponent p) output_factor"
  shows
    "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed R root_weight
          cutoff potential (slp_cauchy_transform orientation potential)
          output_factor) coordinates
      \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
      top_class.top"
proof (rule
    slp_left_branch_positive_amplitude_packed_terminal_weighted_cutoff_lt_top[
      OF root_weight_integrable radius_nonnegative p_lower p_upper
        cutoff_measurable potential_lp cutoff_bound C_nonnegative])
  show
    "slp_cauchy_transform orientation potential \<in>
      borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[
          OF p_lower p_upper potential_lp])
next
  fix x :: slp_point
  show
    "ennreal (cmod (cutoff x)) *
        ennreal (cmod (slp_cauchy_transform orientation potential x)) \<le>
      ennreal (cmod (cutoff x)) *
        slp_positive_terminal_riesz_weight R potential x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[
          OF support_radius])
next
  show
    "aim_complex_lp_on_plane (slp_branch_holder_exponent p) output_factor"
    by (rule output_factor_lp)
qed

end

end
