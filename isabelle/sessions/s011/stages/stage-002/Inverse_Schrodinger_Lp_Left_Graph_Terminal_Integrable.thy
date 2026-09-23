theory Inverse_Schrodinger_Lp_Left_Graph_Terminal_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Oscillatory_Graph_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Support"
begin

section \<open>Finite positive terminal mass controls the complex graph kernel\<close>

theorem slp_left_branch_complex_kernel_list_integrable_from_positive_mass:
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and positive_mass_finite:
      "(\<integral>\<^sup>+ terminal.
        slp_left_branch_positive_kernel_list (2 * B) cutoff potential
          terminal_value pairs origin terminal \<partial>lborel) < \<infinity>"
  shows
    "integrable lborel
      (slp_left_branch_complex_kernel_list cutoff potential terminal_value
        pairs origin)"
proof (unfold integrable_iff_bounded, intro conjI)
  show
    "slp_left_branch_complex_kernel_list cutoff potential terminal_value
        pairs origin \<in> borel_measurable lborel"
    by (rule slp_left_branch_complex_kernel_list_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable])
  have pointwise:
      "\<And>terminal. ennreal (norm
        (slp_left_branch_complex_kernel_list cutoff potential terminal_value
          pairs origin terminal)) \<le>
        slp_left_branch_positive_kernel_list (2 * B) cutoff potential
          terminal_value pairs origin terminal"
  proof -
    fix terminal
    show
      "ennreal (norm
          (slp_left_branch_complex_kernel_list cutoff potential terminal_value
            pairs origin terminal)) \<le>
        slp_left_branch_positive_kernel_list (2 * B) cutoff potential
          terminal_value pairs origin terminal"
    proof (cases
        "slp_left_branch_complex_kernel_list cutoff potential terminal_value
          pairs origin terminal = 0")
      case True
      then show ?thesis
        by (simp only: norm_zero ennreal_0 zero_le)
    next
      case False
      have chain:
          "slp_left_branch_radius_chain (2 * B) origin pairs terminal"
        by (rule slp_left_branch_complex_kernel_list_support_chain[OF
              B_nonnegative origin_bound cutoff_support potential_support
              False])
      have exact:
          "ennreal (norm
              (slp_left_branch_complex_kernel_list cutoff potential
                terminal_value pairs origin terminal)) =
            slp_left_branch_positive_kernel_list (2 * B) cutoff potential
              terminal_value pairs origin terminal"
        by (rule slp_left_branch_complex_kernel_list_positive_weight[OF chain])
      show ?thesis
        by (simp only: exact order_refl)
    qed
  qed
  have mass_bound:
      "(\<integral>\<^sup>+ terminal. ennreal (norm
          (slp_left_branch_complex_kernel_list cutoff potential terminal_value
            pairs origin terminal)) \<partial>lborel) \<le>
       (\<integral>\<^sup>+ terminal.
          slp_left_branch_positive_kernel_list (2 * B) cutoff potential
            terminal_value pairs origin terminal \<partial>lborel)"
  proof (rule nn_integral_mono_AE)
    show
      "AE terminal in lborel.
        ennreal (norm
          (slp_left_branch_complex_kernel_list cutoff potential terminal_value
            pairs origin terminal)) \<le>
        slp_left_branch_positive_kernel_list (2 * B) cutoff potential
          terminal_value pairs origin terminal"
      by (rule always_eventually) (rule allI, rule pointwise)
  qed
  show
    "(\<integral>\<^sup>+ terminal. ennreal (norm
        (slp_left_branch_complex_kernel_list cutoff potential terminal_value
          pairs origin terminal)) \<partial>lborel) < \<infinity>"
    by (rule le_less_trans[OF mass_bound positive_mass_finite])
qed

corollary slp_left_branch_oscillatory_graph_kernel_integrable_from_positive_mass:
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and positive_mass_finite:
      "(\<integral>\<^sup>+ terminal.
        slp_left_branch_positive_kernel_list (2 * B) cutoff potential
          terminal_value pairs origin terminal \<partial>lborel) < \<infinity>"
  shows
    "integrable lborel
      (slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
        terminal_value pairs origin)"
proof -
  have raw:
      "integrable lborel
        (slp_left_branch_complex_kernel_list cutoff potential terminal_value
          pairs origin)"
    by (rule slp_left_branch_complex_kernel_list_integrable_from_positive_mass[
          OF B_nonnegative origin_bound cutoff_support potential_support
            cutoff_measurable potential_measurable terminal_value_measurable
            positive_mass_finite])
  show ?thesis
    using slp_left_branch_oscillatory_graph_kernel_integrable_iff[OF
        cutoff_measurable potential_measurable terminal_value_measurable,
        of tau center pairs origin]
      raw
    by blast
qed

end
