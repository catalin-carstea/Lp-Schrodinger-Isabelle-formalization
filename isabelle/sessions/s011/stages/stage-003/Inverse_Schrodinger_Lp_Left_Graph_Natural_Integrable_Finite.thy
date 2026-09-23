theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Integrable_Finite
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Coordinate_Integrable"
begin

section \<open>Natural-coordinate graph integrability from finite positive mass\<close>

theorem slp_left_branch_oscillatory_graph_kernel_natural_integrable_finite:
  fixes B tau :: real
    and center origin :: slp_point
    and cutoff potential terminal_value :: "slp_point \<Rightarrow> complex"
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
    and functional_finite:
      "slp_positive_branch_functional (2 * B) cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) n origin
        (\<lambda>_. 1) < \<infinity>"
  shows
    "integrable
      (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
          \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential terminal_value origin)"
proof -
  let ?MP = "PiM {..<n}
    (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MF = "?MP \<Otimes>\<^sub>M ?MP"
  let ?M = "?MF \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?pos = "\<lambda>k coordinates.
    slp_left_branch_natural_value n (fst (fst coordinates)) k"
  let ?neg = "\<lambda>k coordinates.
    slp_left_branch_natural_value n (snd (fst coordinates)) k"
  let ?terminal = "\<lambda>coordinates. snd coordinates"
  let ?origin = "\<lambda>_::
    (((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
      slp_point). origin"
  let ?pair_functions = "map (\<lambda>k (coordinates::
    (((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
      slp_point)).
    (?pos k coordinates, ?neg k coordinates)) [0..<n]"
  have unit_measurable[measurable]:
      "(\<lambda>_::slp_point. 1::complex) \<in> borel_measurable lborel"
    by measurable
  have family_pos_measurable:
      "(\<lambda>coordinates. fst (fst coordinates)) \<in> measurable ?M ?MP"
    by measurable
  have family_neg_measurable:
      "(\<lambda>coordinates. snd (fst coordinates)) \<in> measurable ?M ?MP"
    by measurable
  have pos_measurable: "\<And>k. ?pos k \<in> borel_measurable ?M"
  proof -
    fix k
    show "?pos k \<in> borel_measurable ?M"
    proof (cases "k < n")
      case True
      have k_in: "k \<in> {..<n}"
        using True by simp
      have component:
          "(\<lambda>family::nat \<Rightarrow> slp_point. family k) \<in>
            measurable ?MP lborel"
        by (rule measurable_component_singleton[OF k_in])
      have composed:
          "(\<lambda>coordinates. fst (fst coordinates) k) \<in>
            measurable ?M lborel"
        using measurable_compose[OF family_pos_measurable component]
        by (simp only: comp_def)
      show ?thesis
        using composed True
        unfolding slp_left_branch_natural_value_def by simp
    next
      case False
      have zero_measurable:
          "(\<lambda>_::(((nat \<Rightarrow> slp_point) \<times>
            (nat \<Rightarrow> slp_point)) \<times> slp_point). 0::slp_point)
            \<in> borel_measurable ?M"
        by measurable
      show ?thesis
        using False zero_measurable
        unfolding slp_left_branch_natural_value_def by simp
    qed
  qed
  have neg_measurable: "\<And>k. ?neg k \<in> borel_measurable ?M"
  proof -
    fix k
    show "?neg k \<in> borel_measurable ?M"
    proof (cases "k < n")
      case True
      have k_in: "k \<in> {..<n}"
        using True by simp
      have component:
          "(\<lambda>family::nat \<Rightarrow> slp_point. family k) \<in>
            measurable ?MP lborel"
        by (rule measurable_component_singleton[OF k_in])
      have composed:
          "(\<lambda>coordinates. snd (fst coordinates) k) \<in>
            measurable ?M lborel"
        using measurable_compose[OF family_neg_measurable component]
        by (simp only: comp_def)
      show ?thesis
        using composed True
        unfolding slp_left_branch_natural_value_def by simp
    next
      case False
      have zero_measurable:
          "(\<lambda>_::(((nat \<Rightarrow> slp_point) \<times>
            (nat \<Rightarrow> slp_point)) \<times> slp_point). 0::slp_point)
            \<in> borel_measurable ?M"
        by measurable
      show ?thesis
        using False zero_measurable
        unfolding slp_left_branch_natural_value_def by simp
    qed
  qed
  have terminal_measurable[measurable]:
      "?terminal \<in> borel_measurable ?M"
    by measurable
  have origin_measurable[measurable]:
      "?origin \<in> borel_measurable ?M"
    by measurable
  have pair_first_measurable:
      "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
        (\<lambda>x. fst (pair x)) \<in> borel_measurable ?M"
  proof -
    fix pair
    assume "pair \<in> set ?pair_functions"
    then obtain k where pair:
        "pair = (\<lambda>coordinates.
          (?pos k coordinates, ?neg k coordinates))"
      by (auto simp only: set_map image_iff)
    show "(\<lambda>(x::(((nat \<Rightarrow> slp_point) \<times>
        (nat \<Rightarrow> slp_point)) \<times> slp_point)). fst (pair x))
        \<in> borel_measurable ?M"
      unfolding pair by (simp only: fst_conv pos_measurable)
  qed
  have pair_second_measurable:
      "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
        (\<lambda>x. snd (pair x)) \<in> borel_measurable ?M"
  proof -
    fix pair
    assume "pair \<in> set ?pair_functions"
    then obtain k where pair:
        "pair = (\<lambda>coordinates.
          (?pos k coordinates, ?neg k coordinates))"
      by (auto simp only: set_map image_iff)
    show "(\<lambda>(x::(((nat \<Rightarrow> slp_point) \<times>
        (nat \<Rightarrow> slp_point)) \<times> slp_point)). snd (pair x))
        \<in> borel_measurable ?M"
      unfolding pair by (simp only: snd_conv neg_measurable)
  qed
  have phase_measurable[measurable]:
      "(\<lambda>coordinates. slp_left_branch_phase center
        (map (\<lambda>pair. pair coordinates) ?pair_functions)
        (?terminal coordinates)) \<in> borel_measurable ?M"
    by (rule slp_left_branch_phase_param_measurable[OF terminal_measurable
          pair_first_measurable pair_second_measurable])
  have phase_direct[measurable]:
      "(\<lambda>coordinates. slp_left_branch_phase center
        (map (\<lambda>k. (?pos k coordinates, ?neg k coordinates)) [0..<n])
        (?terminal coordinates)) \<in> borel_measurable ?M"
    using phase_measurable
    by (simp only: map_map comp_def)
  have oscillation_measurable[measurable]:
      "(\<lambda>coordinates. exp (\<i> * of_real (tau *
        slp_left_branch_phase center
          (map (\<lambda>k. (?pos k coordinates, ?neg k coordinates)) [0..<n])
          (?terminal coordinates)))) \<in> borel_measurable ?M"
    by measurable
  have raw_measurable[measurable]:
      "(\<lambda>coordinates.
        slp_left_branch_complex_kernel_list cutoff potential terminal_value
          (map (\<lambda>k. (?pos k coordinates, ?neg k coordinates)) [0..<n])
          origin (?terminal coordinates)) \<in> borel_measurable ?M"
    by (rule slp_left_branch_complex_kernel_list_compose_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable
          origin_measurable pos_measurable neg_measurable
          terminal_measurable])
  have kernel_measurable:
      "slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential terminal_value origin \<in> borel_measurable ?M"
    unfolding slp_left_branch_oscillatory_graph_kernel_natural_def
      slp_left_branch_oscillatory_graph_kernel_def
      slp_left_branch_complex_kernel_joint_def
      slp_left_branch_complex_kernel_finite_def
    by (rule borel_measurable_times[OF oscillation_measurable raw_measurable])
  have pointwise:
      "\<And>coordinates.
        ennreal (norm
          (slp_left_branch_oscillatory_graph_kernel_natural n tau center
            cutoff potential terminal_value origin coordinates)) \<le>
        slp_left_branch_positive_kernel_list (2 * B) cutoff potential
          terminal_value
          (map (\<lambda>k.
            (slp_left_branch_natural_value n (fst (fst coordinates)) k,
             slp_left_branch_natural_value n (snd (fst coordinates)) k))
            [0..<n]) origin (snd coordinates)"
  proof -
    fix coordinates ::
      "((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
        slp_point"
    let ?pairs = "map (\<lambda>k.
      (slp_left_branch_natural_value n (fst (fst coordinates)) k,
       slp_left_branch_natural_value n (snd (fst coordinates)) k)) [0..<n]"
    show
      "ennreal (norm
        (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential terminal_value origin coordinates)) \<le>
        slp_left_branch_positive_kernel_list (2 * B) cutoff potential
          terminal_value ?pairs origin (snd coordinates)"
    proof (cases
        "slp_left_branch_complex_kernel_list cutoff potential terminal_value
          ?pairs origin (snd coordinates) = 0")
      case True
      show ?thesis
        unfolding slp_left_branch_oscillatory_graph_kernel_natural_def
        using True by (simp only:
          slp_left_branch_oscillatory_graph_kernel_norm norm_zero ennreal_0
          zero_le)
    next
      case False
      have chain:
          "slp_left_branch_radius_chain (2 * B) origin ?pairs
            (snd coordinates)"
        by (rule slp_left_branch_complex_kernel_list_support_chain[OF
              B_nonnegative origin_bound cutoff_support potential_support
              False])
      have exact:
          "ennreal (norm
            (slp_left_branch_complex_kernel_list cutoff potential terminal_value
              ?pairs origin (snd coordinates))) =
            slp_left_branch_positive_kernel_list (2 * B) cutoff potential
              terminal_value ?pairs origin (snd coordinates)"
        by (rule slp_left_branch_complex_kernel_list_positive_weight[OF chain])
      show ?thesis
        unfolding slp_left_branch_oscillatory_graph_kernel_natural_def
        by (simp only: slp_left_branch_oscillatory_graph_kernel_norm exact
            order_refl)
    qed
  qed
  have positive_param_measurable:
      "(\<lambda>coordinates.
        slp_left_branch_positive_kernel_list (2 * B) cutoff potential
          terminal_value
          (map (\<lambda>pair. pair coordinates) ?pair_functions)
          origin (?terminal coordinates)) \<in> borel_measurable ?M"
  proof -
    have origin_lborel: "?origin \<in> measurable ?M lborel"
      using origin_measurable by (simp only: measurable_lborel1)
    have terminal_lborel: "?terminal \<in> measurable ?M lborel"
      using terminal_measurable by (simp only: measurable_lborel1)
    have first_lborel:
        "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
          (\<lambda>x. fst (pair x)) \<in> measurable ?M lborel"
      using pair_first_measurable by (simp only: measurable_lborel1)
    have second_lborel:
        "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
          (\<lambda>x. snd (pair x)) \<in> measurable ?M lborel"
      using pair_second_measurable by (simp only: measurable_lborel1)
    show ?thesis
      by (rule slp_left_branch_positive_kernel_list_param_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable
          origin_lborel terminal_lborel first_lborel second_lborel])
  qed
  have positive_measurable:
      "(\<lambda>coordinates.
        slp_left_branch_positive_kernel_list (2 * B) cutoff potential
          terminal_value
          (map (\<lambda>k. (?pos k coordinates, ?neg k coordinates)) [0..<n])
          origin (?terminal coordinates)) \<in> borel_measurable ?M"
    using positive_param_measurable
    by (simp only: map_map comp_def)
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
      "nn_integral ?M
        (\<lambda>coordinates.
          slp_left_branch_positive_kernel_list (2 * B) cutoff potential
            terminal_value
            (map (\<lambda>k. (?pos k coordinates, ?neg k coordinates))
              [0..<n]) origin (?terminal coordinates)) =
        nn_integral ?MF (\<lambda>families. nn_integral lborel
          (\<lambda>terminal.
            slp_left_branch_positive_kernel_list (2 * B) cutoff potential
              terminal_value
              (map (\<lambda>k.
                (slp_left_branch_natural_value n (fst families) k,
                 slp_left_branch_natural_value n (snd families) k)) [0..<n])
              origin terminal))"
    using lborel.nn_integral_fst[OF positive_measurable]
    by (simp only: split_beta' fst_conv snd_conv)
  have family_integrand_measurable:
      "(\<lambda>families. nn_integral lborel
        (\<lambda>terminal.
          slp_left_branch_positive_kernel_list (2 * B) cutoff potential
            terminal_value
            (map (\<lambda>k.
              (slp_left_branch_natural_value n (fst families) k,
               slp_left_branch_natural_value n (snd families) k)) [0..<n])
            origin terminal)) \<in> borel_measurable ?MF"
    using lborel.borel_measurable_nn_integral_fst[OF positive_measurable]
    by (simp only: split_beta' fst_conv snd_conv)
  have family_split:
      "nn_integral ?MF (\<lambda>families. nn_integral lborel
          (\<lambda>terminal.
            slp_left_branch_positive_kernel_list (2 * B) cutoff potential
              terminal_value
              (map (\<lambda>k.
                (slp_left_branch_natural_value n (fst families) k,
                 slp_left_branch_natural_value n (snd families) k)) [0..<n])
              origin terminal)) =
        nn_integral ?MP (\<lambda>pos. nn_integral ?MP (\<lambda>neg.
          nn_integral lborel (\<lambda>terminal.
            slp_left_branch_positive_kernel_list (2 * B) cutoff potential
              terminal_value
              (map (\<lambda>k.
                (slp_left_branch_natural_value n pos k,
                 slp_left_branch_natural_value n neg k)) [0..<n])
              origin terminal)))"
    using MP.nn_integral_fst[OF family_integrand_measurable]
    by (simp only: split_beta' fst_conv snd_conv)
  have natural_pair_map:
      "\<And>pos neg.
        map (\<lambda>k. (slp_left_branch_natural_value n pos k,
                       slp_left_branch_natural_value n neg k)) [0..<n] =
        map (\<lambda>k. (pos k, neg k)) [0..<n]"
    by (simp add: slp_left_branch_natural_value_def)
  have positive_mass:
      "nn_integral ?M
        (\<lambda>coordinates.
          slp_left_branch_positive_kernel_list (2 * B) cutoff potential
            terminal_value
            (map (\<lambda>k. (?pos k coordinates, ?neg k coordinates))
              [0..<n]) origin (?terminal coordinates)) =
        slp_positive_branch_functional (2 * B) cutoff potential
          (\<lambda>x. ennreal (norm (terminal_value x))) n origin
          (\<lambda>_. 1)"
  proof -
    note functional =
      slp_left_branch_positive_kernel_list_integral_functional_distinct[
        where ks = "[0..<n]" and R = "2 * B" and cutoff = cutoff
          and potential = potential and terminal_value = terminal_value
          and output_factor = "\<lambda>_::slp_point. 1::complex"
          and origin = origin,
        OF distinct_upt cutoff_measurable potential_measurable
          terminal_value_measurable unit_measurable]
    show ?thesis
      using terminal_split family_split functional
      by (simp only: natural_pair_map set_upt atLeast0LessThan
          length_upt diff_zero
          norm_one ennreal_1 mult_1_right)
  qed
  show ?thesis
    unfolding integrable_iff_bounded
  proof (intro conjI)
    show
      "slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential terminal_value origin \<in> borel_measurable ?M"
      by (rule kernel_measurable)
    have mass_bound:
        "nn_integral ?M (\<lambda>coordinates. ennreal (norm
          (slp_left_branch_oscillatory_graph_kernel_natural n tau center
            cutoff potential terminal_value origin coordinates))) \<le>
        nn_integral ?M
          (\<lambda>coordinates.
            slp_left_branch_positive_kernel_list (2 * B) cutoff potential
              terminal_value
              (map (\<lambda>k. (?pos k coordinates, ?neg k coordinates))
                [0..<n]) origin (?terminal coordinates))"
      by (rule nn_integral_mono_AE)
        (rule always_eventually, rule allI, rule pointwise)
    show
      "nn_integral ?M (\<lambda>coordinates. ennreal (norm
        (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential terminal_value origin coordinates))) < \<infinity>"
      by (rule le_less_trans[OF mass_bound])
        (simp only: positive_mass functional_finite)
  qed
qed

end
