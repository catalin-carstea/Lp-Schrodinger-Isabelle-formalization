theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Coordinate_Integrable"
begin

section \<open>Complex Fubini for the natural-coordinate graph kernel\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_branch_oscillatory_graph_kernel_natural_integral_fubini_hls:
  fixes B C p tau :: real
    and center origin :: slp_point
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integral\<^sup>L
        (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
          (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
            \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential (\<lambda>_. 1) origin) =
      (\<integral>pos. (\<integral>neg. (\<integral>terminal.
        slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential (\<lambda>_. 1) origin ((pos, neg), terminal)
          \<partial>(lborel :: slp_point measure))
        \<partial>PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
      \<partial>PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))"
proof -
  let ?MP = "PiM {..<n}
    (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MF = "?MP \<Otimes>\<^sub>M ?MP"
  let ?M = "?MF \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?kernel =
    "slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
      potential (\<lambda>_. 1) origin"
  have joint_integrable: "integrable ?M ?kernel"
    by (rule
        slp_left_branch_oscillatory_graph_kernel_natural_integrable_hls[OF
          B_nonnegative origin_bound cutoff_support potential_support p_lower
          p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative])
  interpret product: product_sigma_finite
    "\<lambda>_::nat. (lborel :: slp_point measure)"
    by standard
  have MP_sigma: "sigma_finite_measure ?MP"
    by (rule product.sigma_finite) simp
  interpret MP: sigma_finite_measure ?MP
    by (rule MP_sigma)
  interpret family_pair: pair_sigma_finite ?MP ?MP ..
  have MF_sigma: "sigma_finite_measure ?MF"
    by standard
  interpret MF: sigma_finite_measure ?MF
    by (rule MF_sigma)
  interpret all_coordinates: pair_sigma_finite ?MF lborel ..
  have terminal_split:
      "(\<integral>families. (\<integral>terminal.
          ?kernel (families, terminal) \<partial>lborel) \<partial>?MF) =
        integral\<^sup>L ?M ?kernel"
    using all_coordinates.integral_fst'[OF joint_integrable]
    by simp
  have families_integrable:
      "integrable ?MF
        (\<lambda>families. \<integral>terminal.
          ?kernel (families, terminal) \<partial>lborel)"
    using all_coordinates.integrable_fst'[OF joint_integrable]
    by simp
  have family_split:
      "(\<integral>pos. (\<integral>neg. (\<integral>terminal.
          ?kernel ((pos, neg), terminal) \<partial>lborel) \<partial>?MP)
        \<partial>?MP) =
        (\<integral>families. (\<integral>terminal.
          ?kernel (families, terminal) \<partial>lborel) \<partial>?MF)"
    using family_pair.integral_fst'[OF families_integrable]
    by simp
  show ?thesis
    using terminal_split family_split by simp
qed

end

end
