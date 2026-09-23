theory Inverse_Schrodinger_Lp_Cauchy_Terminal_Branch_Functional_Finite
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Positive_Branch_Functional_Riesz_Terminal_Finite"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Packed_Positive_Amplitude"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Branch_Functional_Cutoff_Monotone"
begin

section \<open>Cauchy terminal measurability and fixed-root finiteness\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_cauchy_terminal_weight_measurable_below_two:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and potential_lp: "aim_complex_lp_on_plane p potential"
  shows
    "(\<lambda>x. ennreal (cmod
      (slp_cauchy_transform orientation potential x)))
      \<in> borel_measurable lborel"
proof -
  have transform_measurable[measurable]:
      "slp_cauchy_transform orientation potential
        \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper potential_lp])
  show ?thesis by measurable
qed

theorem slp_positive_branch_functional_cauchy_terminal_unit_finite:
  fixes R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and support_radius:
      "\<And>x y. \<lbrakk>cutoff x \<noteq> 0; potential y \<noteq> 0\<rbrakk> \<Longrightarrow>
        Real_Vector_Spaces.norm (x - y) \<le> R"
  shows
    "slp_positive_branch_functional R cutoff potential
      (\<lambda>x. ennreal (cmod
        (slp_cauchy_transform orientation potential x)))
      n origin (\<lambda>_. 1) < top_class.top"
proof -
  have terminal_le:
      "\<And>x. ennreal (cmod (cutoff x)) *
          ennreal (cmod
            (slp_cauchy_transform orientation potential x)) \<le>
        ennreal (cmod (cutoff x)) *
          slp_positive_terminal_riesz_weight R potential x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF
          support_radius])
  have functional_le:
      "slp_positive_branch_functional R cutoff potential
          (\<lambda>x. ennreal (cmod
            (slp_cauchy_transform orientation potential x)))
          n origin (\<lambda>_. 1) \<le>
        slp_positive_branch_functional R cutoff potential
          (slp_positive_terminal_riesz_weight R potential)
          n origin (\<lambda>_. 1)"
    by (rule slp_positive_branch_functional_cutoff_mono[OF terminal_le]) simp
  have majorant_finite:
      "slp_positive_branch_functional R cutoff potential
          (slp_positive_terminal_riesz_weight R potential)
          n origin (\<lambda>_. 1) < top_class.top"
    by (rule slp_positive_branch_functional_riesz_terminal_unit_finite[OF
          radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
          cutoff_bound C_nonnegative])
  show ?thesis
    by (rule le_less_trans[OF functional_le majorant_finite])
qed

end

end
