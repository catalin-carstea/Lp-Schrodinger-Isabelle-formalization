theory Inverse_Schrodinger_Lp_Born_Root_Terminal_Collapse
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Root_Density
    Inverse_Schrodinger_Lp_Born_One_Sided_Terminal_Collapse
begin

section \<open>Terminal collapse after root pairing\<close>

theorem slp_positive_root_output_density_positive_terminal_collapse:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "slp_positive_root_output_density R cutoff potential (\<lambda>_. 1)
        (Suc n) root_weight target \<le>
      ennreal (inverse (pi ^ 2)) * ennreal C *
        (\<integral>\<^sup>+terminal.
          ennreal (slp_localized_cauchy_kernel R (terminal - target)) *
          slp_positive_root_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n
            root_weight terminal
          \<partial>lborel)"
proof -
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
  let ?scale = "ennreal (inverse (pi ^ 2)) * ennreal C"
  let ?terminal_weight = "slp_positive_terminal_riesz_weight R potential"
  let ?density =
    "slp_positive_output_density R cutoff potential ?terminal_weight n"
  let ?kernel = "\<lambda>terminal.
    ennreal (slp_localized_cauchy_kernel R (terminal - target))"
  let ?root_norm = "\<lambda>root. ennreal (norm (root_weight root))"
  let ?convolution = "\<lambda>root.
    \<integral>\<^sup>+terminal. ?kernel terminal * ?density root terminal
      \<partial>lborel"
  have terminal_weight_measurable[measurable]:
      "?terminal_weight \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          potential_measurable])
  have density_joint[measurable]:
      "case_prod ?density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable;
        measurable)
  have convolution_measurable[measurable]:
      "?convolution \<in> borel_measurable lborel"
    using density_joint by measurable
  have pointwise:
      "?root_norm root *
          slp_positive_output_density R cutoff potential (\<lambda>_. 1)
            (Suc n) root target \<le>
        ?root_norm root * (?scale * ?convolution root)"
    for root
  proof -
    have collapse_root:
        "slp_positive_output_density R cutoff potential (\<lambda>_. 1)
            (Suc n) root target \<le> ?scale * ?convolution root"
      by (rule slp_positive_output_density_positive_terminal_collapse[OF
            cutoff_measurable potential_measurable cutoff_bound C_nonnegative])
    show ?thesis
      by (rule mult_left_mono[OF collapse_root]) simp
  qed
  have integrated:
      "(\<integral>\<^sup>+root.
          ?root_norm root *
            slp_positive_output_density R cutoff potential (\<lambda>_. 1)
              (Suc n) root target
          \<partial>lborel) \<le>
        (\<integral>\<^sup>+root.
          ?root_norm root * (?scale * ?convolution root)
          \<partial>lborel)"
    by (rule nn_integral_mono) (rule pointwise)
  have root_convolution_measurable:
      "(\<lambda>root. ?root_norm root * ?convolution root)
        \<in> borel_measurable lborel"
    by measurable
  have scale_extracted:
      "(\<integral>\<^sup>+root.
          ?root_norm root * (?scale * ?convolution root)
          \<partial>lborel) =
        ?scale *
          (\<integral>\<^sup>+root. ?root_norm root * ?convolution root
            \<partial>lborel)"
    using nn_integral_cmult[OF root_convolution_measurable, of ?scale]
    by (simp add: mult.commute mult.left_commute mult.assoc)
  have joint_measurable:
      "case_prod (\<lambda>root terminal.
          ?root_norm root * (?kernel terminal * ?density root terminal))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using density_joint by measurable
  have swap:
      "(\<integral>\<^sup>+root. \<integral>\<^sup>+terminal.
          ?root_norm root * (?kernel terminal * ?density root terminal)
          \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+terminal. \<integral>\<^sup>+root.
          ?root_norm root * (?kernel terminal * ?density root terminal)
          \<partial>lborel \<partial>lborel)"
    using lborel_pair.Fubini'[OF joint_measurable] by simp
  have density_slice_measurable:
      "(?density root) \<in> borel_measurable lborel"
    for root
    using density_joint by measurable
  have left_slice:
      "(\<integral>\<^sup>+terminal.
          ?root_norm root * (?kernel terminal * ?density root terminal)
          \<partial>lborel) =
        ?root_norm root * ?convolution root"
    for root
  proof -
    have integrand_measurable:
        "(\<lambda>terminal. ?kernel terminal * ?density root terminal)
          \<in> borel_measurable lborel"
      using density_slice_measurable[of root] by measurable
    show ?thesis
      using nn_integral_cmult[OF integrand_measurable, of "?root_norm root"]
      by simp
  qed
  have root_slice_measurable:
      "(\<lambda>root. ?root_norm root * ?density root terminal)
        \<in> borel_measurable lborel"
    for terminal
    using density_joint by measurable
  have right_slice:
      "(\<integral>\<^sup>+root.
          ?root_norm root * (?kernel terminal * ?density root terminal)
          \<partial>lborel) =
        ?kernel terminal *
          slp_positive_root_output_density R cutoff potential
            ?terminal_weight n root_weight terminal"
    for terminal
  proof -
    have extracted:
        "(\<integral>\<^sup>+root.
            ?kernel terminal * (?root_norm root * ?density root terminal)
            \<partial>lborel) =
          ?kernel terminal *
            (\<integral>\<^sup>+root.
              ?root_norm root * ?density root terminal \<partial>lborel)"
      by (rule nn_integral_cmult[OF root_slice_measurable])
    show ?thesis
      using extracted
      unfolding slp_positive_root_output_density_def
      by (simp add: mult.commute mult.left_commute mult.assoc)
  qed
  have root_convolution_swap:
      "(\<integral>\<^sup>+root. ?root_norm root * ?convolution root
          \<partial>lborel) =
        (\<integral>\<^sup>+terminal. ?kernel terminal *
          slp_positive_root_output_density R cutoff potential
            ?terminal_weight n root_weight terminal
          \<partial>lborel)"
    using swap by (simp only: left_slice right_slice)
  have integrated_root:
      "slp_positive_root_output_density R cutoff potential (\<lambda>_. 1)
          (Suc n) root_weight target \<le>
        (\<integral>\<^sup>+root.
          ?root_norm root * (?scale * ?convolution root)
          \<partial>lborel)"
    unfolding slp_positive_root_output_density_def
    by (rule integrated)
  have scaled_swap:
      "(\<integral>\<^sup>+root.
          ?root_norm root * (?scale * ?convolution root)
          \<partial>lborel) =
        ?scale *
          (\<integral>\<^sup>+terminal. ?kernel terminal *
            slp_positive_root_output_density R cutoff potential
              ?terminal_weight n root_weight terminal
            \<partial>lborel)"
    using scale_extracted root_convolution_swap by simp
  show ?thesis
    using integrated_root scaled_swap by simp
qed

end
