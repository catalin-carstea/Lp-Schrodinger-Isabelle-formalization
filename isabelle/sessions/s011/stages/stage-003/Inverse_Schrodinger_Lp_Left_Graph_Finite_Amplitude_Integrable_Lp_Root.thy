theory Inverse_Schrodinger_Lp_Left_Graph_Finite_Amplitude_Integrable_Lp_Root
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Output"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Bounded_Support_L1"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Smooth_Error_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Packed_Potential_Root"
begin

section \<open>Finite amplitudes for compactly supported root weights\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_positive_root_output_density_terminal_weighted_real_integrable_lp_root:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integrable lborel (\<lambda>output. enn2real
      (slp_positive_root_output_density R cutoff potential
        (slp_positive_terminal_riesz_weight R potential) n root_weight
        output))"
proof -
  let ?q = "slp_branch_power_exponent p"
  let ?F = "slp_positive_root_output_density R cutoff potential
    (slp_positive_terminal_riesz_weight R potential) n root_weight"
  have root_support_subset: "{x. root_weight x \<noteq> 0} \<subseteq> X"
    using root_weight_outside by blast
  have root_support: "bounded {x. root_weight x \<noteq> 0}"
    by (rule bounded_subset[OF X_bounded root_support_subset])
  note all_order =
    slp_positive_root_output_density_all_orders_terminal_weighted_lp_root[OF
      radius_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable potential_lp root_weight_lp root_weight_outside
      cutoff_bound C_nonnegative]
  have q_lower: "1 < ?q"
    using all_order(1) by blast
  obtain L where F_lp: "slp_positive_ennreal_lp_on_plane ?q ?F"
    using all_order(2)[of n] by blast
  have F_support: "bounded {x. ?F x \<noteq> 0}"
    by (rule slp_positive_root_output_density_bounded_support[OF
          radius_nonnegative root_support])
  show ?thesis
    by (rule slp_positive_ennreal_lp_integrable_bounded_support[OF
          less_imp_le[OF q_lower] F_lp F_support])
qed

theorem slp_positive_root_output_density_terminal_weighted_mass_finite_lp_root:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "(\<integral>\<^sup>+ output.
      slp_positive_root_output_density R cutoff potential
        (slp_positive_terminal_riesz_weight R potential) n root_weight output
      \<partial>lborel) < top_class.top"
proof -
  let ?q = "slp_branch_power_exponent p"
  let ?F = "slp_positive_root_output_density R cutoff potential
    (slp_positive_terminal_riesz_weight R potential) n root_weight"
  note all_order =
    slp_positive_root_output_density_all_orders_terminal_weighted_lp_root[OF
      radius_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable potential_lp root_weight_lp root_weight_outside
      cutoff_bound C_nonnegative]
  obtain L where F_lp: "slp_positive_ennreal_lp_on_plane ?q ?F"
    using all_order(2)[of n] by blast
  have F_ae_finite: "AE output in lborel. ?F output < top_class.top"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have F_lifted:
      "AE output in lborel. ?F output = ennreal (enn2real (?F output))"
    using F_ae_finite by eventually_elim simp
  have F_real_integrable:
      "integrable lborel (\<lambda>output. enn2real (?F output))"
    by (rule
      slp_positive_root_output_density_terminal_weighted_real_integrable_lp_root[
        OF radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp root_weight_lp root_weight_outside
          cutoff_bound C_nonnegative])
  have nonnegative:
      "AE output in lborel. 0 \<le> enn2real (?F output)"
    by simp
  have F_nn_lift:
      "(\<integral>\<^sup>+ output. ?F output \<partial>lborel) =
        (\<integral>\<^sup>+ output. ennreal (enn2real (?F output))
          \<partial>lborel)"
    by (rule nn_integral_cong_AE)
      (use F_lifted in eventually_elim; simp)
  have F_lift_eq:
      "(\<integral>\<^sup>+ output. ennreal (enn2real (?F output))
          \<partial>lborel) =
        ennreal (integral\<^sup>L lborel
          (\<lambda>output. enn2real (?F output)))"
    by (rule nn_integral_eq_integral[OF F_real_integrable nonnegative])
  show ?thesis
    using F_nn_lift F_lift_eq by simp
qed

theorem slp_left_branch_complex_amplitude_finite_unit_integrable_lp_root:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and root_weight cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and root_support:
      "\<And>x :: slp_point. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
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
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integrable lborel
      (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
        (\<lambda>_. 1) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
proof -
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable:
      "(\<lambda>_ :: slp_point. 1 :: complex) \<in> borel_measurable lborel"
    by measurable
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  have density_mass_finite:
      "(\<integral>\<^sup>+ output.
        slp_left_one_sided_output_density (2 * B) cutoff potential
          (\<lambda>_. 1) CARD('i) root_weight output
        \<partial>lborel) < top_class.top"
    by (rule
      slp_left_one_sided_output_density_unweighted_mass_finite_lp_root[OF
        radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable potential_lp root_weight_lp root_weight_outside
        cutoff_bound C_nonnegative])
  have majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential (\<lambda>_. 1) (\<lambda>_. 1))
          coordinates
        \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  proof -
    note pairing =
      slp_left_branch_positive_amplitude_packed_unit_terminal_pairing[
        where 'i = 'i and R = "2 * B" and root_weight = root_weight
          and cutoff = cutoff and potential = potential
          and output_factor = "\<lambda>_ :: slp_point. 1 :: complex",
        OF root_weight_measurable cutoff_measurable potential_measurable
          unit_measurable]
    show ?thesis
      using pairing density_mass_finite
      unfolding infinity_ennreal_def by simp
  qed
  show ?thesis
    by (rule slp_left_branch_complex_amplitude_finite_integrable[
          where B = B, OF B_nonnegative root_support cutoff_support
            potential_support root_weight_measurable cutoff_measurable
            potential_measurable unit_measurable unit_measurable
            majorant_finite])
qed

theorem slp_left_branch_complex_amplitude_finite_cauchy_integrable_lp_root:
  fixes branch_dummy :: "'i::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and root_weight cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and root_support:
      "\<And>x :: slp_point. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
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
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integrable lborel
      (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
        (slp_cauchy_transform orientation potential) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
proof -
  let ?terminal = "slp_cauchy_transform orientation potential"
  let ?terminal_weight = "\<lambda>x. ennreal (cmod (?terminal x))"
  let ?terminal_majorant = "slp_positive_terminal_riesz_weight (2 * B) potential"
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_measurable: "?terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper potential_lp])
  have terminal_weight_measurable:
      "?terminal_weight \<in> borel_measurable lborel"
    using terminal_measurable by measurable
  have terminal_majorant_measurable:
      "?terminal_majorant \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          potential_measurable])
  have unit_measurable:
      "(\<lambda>_ :: slp_point. 1 :: complex) \<in> borel_measurable lborel"
    by measurable
  have unit_weight_measurable:
      "(\<lambda>_ :: slp_point. 1 :: ennreal) \<in> borel_measurable lborel"
    by measurable
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  have support_radius:
      "\<And>x y :: slp_point. \<lbrakk>cutoff x \<noteq> 0; potential y \<noteq> 0\<rbrakk> \<Longrightarrow>
        Real_Vector_Spaces.norm (x - y) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          cutoff_support potential_support])
  have terminal_weight_le:
      "\<And>x. ennreal (cmod (cutoff x)) * ?terminal_weight x \<le>
        ennreal (cmod (cutoff x)) * ?terminal_majorant x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF
          support_radius])
  have majorant_mass_finite:
      "(\<integral>\<^sup>+ output.
        slp_positive_root_output_density (2 * B) cutoff potential
          ?terminal_majorant CARD('i) root_weight output
        \<partial>lborel) < top_class.top"
    by (rule
      slp_positive_root_output_density_terminal_weighted_mass_finite_lp_root[OF
        radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable potential_lp root_weight_lp root_weight_outside
        cutoff_bound C_nonnegative])
  have terminal_mass_le:
      "(\<integral>\<^sup>+ output.
        slp_positive_root_output_density (2 * B) cutoff potential
          ?terminal_weight CARD('i) root_weight output
        \<partial>lborel) \<le>
      (\<integral>\<^sup>+ output.
        slp_positive_root_output_density (2 * B) cutoff potential
          ?terminal_majorant CARD('i) root_weight output
        \<partial>lborel)"
    using slp_positive_root_output_density_pairing_cutoff_mono[
      where R = "2 * B" and cutoff = cutoff and potential = potential
        and terminal_weight = ?terminal_weight
        and terminal_majorant = ?terminal_majorant
        and n = "CARD('i)" and root_weight = root_weight
        and test = "\<lambda>_ :: slp_point. 1 :: ennreal",
      OF cutoff_measurable potential_measurable terminal_weight_measurable
        terminal_majorant_measurable root_weight_measurable
        unit_weight_measurable terminal_weight_le]
    by simp
  have terminal_mass_finite:
      "(\<integral>\<^sup>+ output.
        slp_positive_root_output_density (2 * B) cutoff potential
          ?terminal_weight CARD('i) root_weight output
        \<partial>lborel) < top_class.top"
    by (rule le_less_trans[OF terminal_mass_le majorant_mass_finite])
  have majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential ?terminal (\<lambda>_. 1)) coordinates
        \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  proof -
    note pairing = slp_left_branch_positive_amplitude_packed_terminal_pairing[
      where 'i = 'i and R = "2 * B" and root_weight = root_weight
        and cutoff = cutoff and potential = potential and terminal_value = ?terminal
        and output_factor = "\<lambda>_ :: slp_point. 1 :: complex",
      OF root_weight_measurable cutoff_measurable potential_measurable
        terminal_measurable unit_measurable]
    show ?thesis
      using pairing terminal_mass_finite
      unfolding slp_left_one_sided_output_density_def infinity_ennreal_def
      by simp
  qed
  show ?thesis
    by (rule slp_left_branch_complex_amplitude_finite_integrable[
          where B = B, OF B_nonnegative root_support cutoff_support
            potential_support root_weight_measurable cutoff_measurable
            potential_measurable terminal_measurable unit_measurable
            majorant_finite])
qed

end

end
