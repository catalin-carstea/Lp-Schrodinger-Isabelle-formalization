theory Inverse_Schrodinger_Lp_One_Sided_Packed_Unit_Terminal_Output_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Root_Density"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Inner_Mass_Functional"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Amplitude_Root_Factorization"
begin

section \<open>Exact unit-terminal output pairings for packed amplitudes\<close>

theorem slp_positive_root_output_density_pairing:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and test_measurable[measurable]:
      "test \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ output. test output *
        slp_positive_root_output_density R cutoff potential terminal_weight n
          root_weight output
        \<partial>lborel) =
      (\<integral>\<^sup>+ root. ennreal (norm (root_weight root)) *
        slp_positive_branch_functional R cutoff potential terminal_weight n
          root test
        \<partial>lborel)"
proof -
  let ?density =
    "slp_positive_output_density R cutoff potential terminal_weight n"
  let ?joint = "\<lambda>root output.
    ennreal (norm (root_weight root)) * test output * ?density root output"
  have density_joint[measurable]:
      "case_prod ?density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable[OF
          cutoff_measurable potential_measurable
          terminal_weight_measurable])
  have joint_measurable:
      "case_prod ?joint \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have root_slice_measurable:
      "(\<lambda>root. ennreal (norm (root_weight root)) *
          ?density root out) \<in> borel_measurable lborel"
    for out
    by measurable
  have expand_root_density:
      "(\<integral>\<^sup>+ output. test output *
          slp_positive_root_output_density R cutoff potential terminal_weight n
            root_weight output
          \<partial>lborel) =
        (\<integral>\<^sup>+ output. \<integral>\<^sup>+ root.
          ?joint root output \<partial>lborel \<partial>lborel)"
    unfolding slp_positive_root_output_density_def
  proof (rule nn_integral_cong)
    fix out
    have extracted:
        "(\<integral>\<^sup>+ root. test out *
            (ennreal (norm (root_weight root)) * ?density root out)
            \<partial>lborel) =
          test out *
            (\<integral>\<^sup>+ root.
              ennreal (norm (root_weight root)) * ?density root out
              \<partial>lborel)"
      by (rule nn_integral_cmult[OF root_slice_measurable])
    show "test out *
          (\<integral>\<^sup>+ root.
            ennreal (norm (root_weight root)) * ?density root out
            \<partial>lborel) =
        (\<integral>\<^sup>+ root. ?joint root out \<partial>lborel)"
      using extracted
      by (simp add: mult.assoc mult.commute mult.left_commute)
  qed
  have swap:
      "(\<integral>\<^sup>+ output. \<integral>\<^sup>+ root.
          ?joint root output \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ root. \<integral>\<^sup>+ output.
          ?joint root output \<partial>lborel \<partial>lborel)"
    using lborel_pair.Fubini'[OF joint_measurable] by simp
  have test_density_measurable:
      "(\<lambda>output. test output * ?density root output)
        \<in> borel_measurable lborel"
    for root
    by measurable
  have inner:
      "(\<integral>\<^sup>+ output. ?joint root output \<partial>lborel) =
        ennreal (norm (root_weight root)) *
          slp_positive_branch_functional R cutoff potential terminal_weight n
            root test"
    for root
  proof -
    have extracted:
        "(\<integral>\<^sup>+ output. ennreal (norm (root_weight root)) *
            (test output * ?density root output) \<partial>lborel) =
          ennreal (norm (root_weight root)) *
            (\<integral>\<^sup>+ output. test output * ?density root output
              \<partial>lborel)"
      by (rule nn_integral_cmult[OF test_density_measurable])
    have pushed:
        "(\<integral>\<^sup>+ output. test output * ?density root output
            \<partial>lborel) =
          slp_positive_branch_functional R cutoff potential terminal_weight n
            root test"
      by (rule slp_positive_output_density_pushforward[OF
            cutoff_measurable potential_measurable
            terminal_weight_measurable test_measurable])
    show ?thesis
      using extracted pushed by (simp add: mult.assoc)
  qed
  show ?thesis
    using expand_root_density swap by (simp only: inner)
qed

theorem slp_left_branch_positive_amplitude_packed_unit_terminal_pairing:
  fixes branch_dummy :: "'i::finite itself"
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable:
      "potential \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed R root_weight
          cutoff potential (\<lambda>_. 1) output_factor) coordinates
      \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) =
      (\<integral>\<^sup>+ output.
        slp_left_one_sided_output_density R cutoff potential (\<lambda>_. 1)
          CARD('i) root_weight output *
        ennreal (norm (output_factor output))
        \<partial>lborel)"
proof -
  have terminal_measurable:
      "(\<lambda>_ :: slp_point. 1 :: complex) \<in> borel_measurable lborel"
    by measurable
  have transport:
      "(\<integral>\<^sup>+ coordinates.
          case_prod (slp_left_branch_positive_amplitude_packed R root_weight
            cutoff potential (\<lambda>_. 1) output_factor) coordinates
        \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) =
        (\<integral>\<^sup>+ coordinates.
          slp_left_branch_positive_amplitude_finite R root_weight cutoff
            potential (\<lambda>_. 1) output_factor coordinates
        \<partial>(lborel :: ('i slp_left_branch_finite_coordinates) measure))"
    by (rule slp_left_branch_positive_amplitude_integral_transport[OF
          root_weight_measurable cutoff_measurable potential_measurable
          terminal_measurable output_factor_measurable])
  have factorized:
      "(\<integral>\<^sup>+ coordinates.
          slp_left_branch_positive_amplitude_finite R root_weight cutoff
            potential (\<lambda>_. 1) output_factor coordinates
        \<partial>(lborel :: ('i slp_left_branch_finite_coordinates) measure)) =
        (\<integral>\<^sup>+ root. ennreal (norm (root_weight root)) *
          slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
            potential (\<lambda>_. 1) output_factor root
          \<partial>lborel)"
    unfolding slp_left_branch_positive_inner_mass_finite_def
    by (rule slp_left_branch_positive_amplitude_finite_root_factorization[OF
          root_weight_measurable cutoff_measurable potential_measurable
          terminal_measurable output_factor_measurable])
  have functional:
      "slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff potential
          (\<lambda>_. 1) output_factor root =
        slp_positive_branch_functional R cutoff potential (\<lambda>_. 1)
          CARD('i) root (\<lambda>x. ennreal (norm (output_factor x)))"
    for root
  proof -
    note functional_identity =
      slp_left_branch_positive_inner_mass_finite_functional[
        where 'i = 'i and R = R and cutoff = cutoff and potential = potential
          and terminal_value = "\<lambda>_ :: slp_point. 1 :: complex"
          and output_factor = output_factor and origin = root,
        OF cutoff_measurable potential_measurable terminal_measurable
          output_factor_measurable]
    show ?thesis
      using functional_identity by simp
  qed
  have root_pairing:
      "(\<integral>\<^sup>+ output. ennreal (norm (output_factor output)) *
          slp_positive_root_output_density R cutoff potential (\<lambda>_. 1)
            CARD('i) root_weight output
          \<partial>lborel) =
        (\<integral>\<^sup>+ root. ennreal (norm (root_weight root)) *
          slp_positive_branch_functional R cutoff potential (\<lambda>_. 1)
            CARD('i) root (\<lambda>x. ennreal (norm (output_factor x)))
          \<partial>lborel)"
    by (rule slp_positive_root_output_density_pairing[OF
          cutoff_measurable potential_measurable _ root_weight_measurable])
      (use terminal_measurable output_factor_measurable in measurable)
  have finite_to_pairing:
      "(\<integral>\<^sup>+ coordinates.
          slp_left_branch_positive_amplitude_finite R root_weight cutoff
            potential (\<lambda>_. 1) output_factor coordinates
        \<partial>(lborel :: ('i slp_left_branch_finite_coordinates) measure)) =
        (\<integral>\<^sup>+ output. ennreal (norm (output_factor output)) *
          slp_positive_root_output_density R cutoff potential (\<lambda>_. 1)
            CARD('i) root_weight output
          \<partial>lborel)"
    using factorized root_pairing by (simp only: functional)
  show ?thesis
    using transport finite_to_pairing
    unfolding slp_left_one_sided_output_density_def
    by (simp add: mult.commute)
qed

end
