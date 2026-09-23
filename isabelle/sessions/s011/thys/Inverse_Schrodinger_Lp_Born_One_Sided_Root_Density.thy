theory Inverse_Schrodinger_Lp_Born_One_Sided_Root_Density
  imports Inverse_Schrodinger_Lp_Born_Output_Integrable_All_Orders
begin

section \<open>Root-paired positive one-sided output densities\<close>

definition slp_positive_root_output_density ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_positive_root_output_density R cutoff potential terminal_weight n
      root_weight output =
    (\<integral>\<^sup>+ root.
      ennreal (norm (root_weight root)) *
        slp_positive_output_density R cutoff potential terminal_weight n
          root output
      \<partial>lborel)"

definition slp_left_one_sided_output_density ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_left_one_sided_output_density = slp_positive_root_output_density"

definition slp_right_one_sided_output_density ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_right_one_sided_output_density = slp_positive_root_output_density"

theorem slp_positive_root_output_density_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
  shows
    "slp_positive_root_output_density R cutoff potential terminal_weight n
        root_weight \<in> borel_measurable lborel"
proof -
  note [measurable] = slp_positive_output_density_joint_measurable[OF
    cutoff_measurable potential_measurable terminal_weight_measurable]
  show ?thesis
    unfolding slp_positive_root_output_density_def by measurable
qed

theorem slp_positive_root_output_density_mass:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ output.
        slp_positive_root_output_density R cutoff potential terminal_weight n
          root_weight output
        \<partial>lborel) =
      (\<integral>\<^sup>+ root.
        ennreal (norm (root_weight root)) *
          slp_positive_branch_functional R cutoff potential terminal_weight n
            root (\<lambda>_. 1)
        \<partial>lborel)"
proof -
  let ?joint = "\<lambda>root output.
    ennreal (norm (root_weight root)) *
      slp_positive_output_density R cutoff potential terminal_weight n
        root output"
  have density_joint[measurable]:
      "case_prod
          (slp_positive_output_density R cutoff potential terminal_weight n)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable[OF
          cutoff_measurable potential_measurable
          terminal_weight_measurable])
  have joint_measurable:
      "case_prod ?joint \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have swap:
      "(\<integral>\<^sup>+ output. \<integral>\<^sup>+ root.
          ?joint root output \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ root. \<integral>\<^sup>+ output.
          ?joint root output \<partial>lborel \<partial>lborel)"
    using lborel_pair.Fubini'[OF joint_measurable] by simp
  have density_slice[measurable]:
      "slp_positive_output_density R cutoff potential terminal_weight n root
        \<in> borel_measurable lborel"
    for root
    by (rule slp_positive_output_density_output_measurable[OF
          cutoff_measurable potential_measurable
          terminal_weight_measurable])
  have inner:
      "(\<integral>\<^sup>+ output. ?joint root output \<partial>lborel) =
        ennreal (norm (root_weight root)) *
          slp_positive_branch_functional R cutoff potential terminal_weight n
            root (\<lambda>_. 1)"
    for root
  proof -
    have extracted:
        "(\<integral>\<^sup>+ output.
            ennreal (norm (root_weight root)) *
              slp_positive_output_density R cutoff potential terminal_weight n
                root output
            \<partial>lborel) =
          ennreal (norm (root_weight root)) *
            (\<integral>\<^sup>+ output.
              slp_positive_output_density R cutoff potential terminal_weight n
                root output
              \<partial>lborel)"
      by (rule nn_integral_cmult[OF density_slice])
    have density_mass:
        "(\<integral>\<^sup>+ output.
            slp_positive_output_density R cutoff potential terminal_weight n
              root output
            \<partial>lborel) =
          slp_positive_branch_functional R cutoff potential terminal_weight n
            root (\<lambda>_. 1)"
      by (rule slp_positive_output_density_mass[OF cutoff_measurable
            potential_measurable terminal_weight_measurable])
    show ?thesis
      using extracted density_mass by simp
  qed
  show ?thesis
    unfolding slp_positive_root_output_density_def
    using swap by (simp only: inner)
qed

context aim_planar_riesz_hls
begin

theorem slp_positive_root_output_density_unweighted_mass_finite:
  fixes R C p :: real
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_weight_integrable: "integrable lborel root_weight"
  shows
    "(\<integral>\<^sup>+ output.
        slp_positive_root_output_density R cutoff potential (\<lambda>_. 1) n
          root_weight output
        \<partial>lborel) < top"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable by measurable
  have terminal_weight_measurable:
      "(\<lambda>_ :: slp_point. 1 :: ennreal) \<in> borel_measurable lborel"
    by measurable
  obtain M where M_finite: "M < top"
    and M_bound:
      "\<And>root.
        slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
          root (\<lambda>_. 1) \<le> M"
    using slp_positive_branch_mass_unweighted_uniform[OF radius_nonnegative
      p_lower p_upper cutoff_measurable potential_lp cutoff_bound
      C_nonnegative]
    by blast
  have root_norm_measurable[measurable]:
      "(\<lambda>root. ennreal (norm (root_weight root)))
        \<in> borel_measurable lborel"
    using root_weight_measurable by measurable
  have mass_bound:
      "(\<integral>\<^sup>+ root.
          ennreal (norm (root_weight root)) *
            slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
              root (\<lambda>_. 1)
          \<partial>lborel) \<le>
        (\<integral>\<^sup>+ root.
          ennreal (norm (root_weight root)) * M
          \<partial>lborel)"
  proof (rule nn_integral_mono)
    fix root :: slp_point
    assume "root \<in> space lborel"
    show "ennreal (norm (root_weight root)) *
          slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
            root (\<lambda>_. 1) \<le>
        ennreal (norm (root_weight root)) * M"
      by (rule mult_left_mono[OF M_bound]) simp
  qed
  have scaled_root:
      "(\<integral>\<^sup>+ root.
          ennreal (norm (root_weight root)) * M
          \<partial>lborel) =
        (\<integral>\<^sup>+ root. ennreal (norm (root_weight root))
          \<partial>lborel) * M"
    by (rule nn_integral_multc[OF root_norm_measurable])
  have root_norm_finite:
      "(\<integral>\<^sup>+ root. ennreal (norm (root_weight root))
        \<partial>lborel) < top"
    using root_weight_integrable
    unfolding integrable_iff_bounded
    by (simp add: norm_complex_def)
  have majorant_finite:
      "(\<integral>\<^sup>+ root.
          ennreal (norm (root_weight root)) * M
          \<partial>lborel) < top"
    using scaled_root root_norm_finite M_finite
    by (simp add: ennreal_mult_less_top)
  have exact_mass:
      "(\<integral>\<^sup>+ output.
          slp_positive_root_output_density R cutoff potential (\<lambda>_. 1) n
            root_weight output
          \<partial>lborel) =
        (\<integral>\<^sup>+ root.
          ennreal (norm (root_weight root)) *
            slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) n
              root (\<lambda>_. 1)
          \<partial>lborel)"
    by (rule slp_positive_root_output_density_mass[OF cutoff_measurable
          potential_measurable terminal_weight_measurable
          root_weight_measurable])
  show ?thesis
    using exact_mass le_less_trans[OF mass_bound majorant_finite] by simp
qed

corollary slp_left_one_sided_output_density_unweighted_mass_finite:
  fixes R C p :: real
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
  assumes "0 \<le> R" "1 < p" "p < 2"
    "cutoff \<in> borel_measurable lborel"
    "aim_complex_lp_on_plane p potential"
    "\<And>x. norm (cutoff x) \<le> C" "0 \<le> C"
    "integrable lborel root_weight"
  shows
    "(\<integral>\<^sup>+ output.
        slp_left_one_sided_output_density R cutoff potential (\<lambda>_. 1) n
          root_weight output
        \<partial>lborel) < top"
  unfolding slp_left_one_sided_output_density_def
  by (rule slp_positive_root_output_density_unweighted_mass_finite[OF assms])

corollary slp_right_one_sided_output_density_unweighted_mass_finite:
  fixes R C p :: real
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
  assumes "0 \<le> R" "1 < p" "p < 2"
    "cutoff \<in> borel_measurable lborel"
    "aim_complex_lp_on_plane p potential"
    "\<And>x. norm (cutoff x) \<le> C" "0 \<le> C"
    "integrable lborel root_weight"
  shows
    "(\<integral>\<^sup>+ output.
        slp_right_one_sided_output_density R cutoff potential (\<lambda>_. 1) n
          root_weight output
        \<partial>lborel) < top"
  unfolding slp_right_one_sided_output_density_def
  by (rule slp_positive_root_output_density_unweighted_mass_finite[OF assms])

end

end
