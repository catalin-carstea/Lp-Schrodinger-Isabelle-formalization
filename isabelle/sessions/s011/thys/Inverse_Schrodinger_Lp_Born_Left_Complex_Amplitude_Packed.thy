theory Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Packed
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_Packed_Weight"
begin

section \<open>Exact left amplitude on the packed one-sided carrier\<close>

definition slp_one_sided_packed_output_point ::
    "real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> slp_point"
where
  "slp_one_sided_packed_output_point branch =
    slp_complex_as_point
      (slp_signed_output slp_one_sided_branch_sign
        (slp_complex_family_unpack branch))"

lemma slp_one_sided_packed_output_point_measurable [measurable]:
  "(slp_one_sided_packed_output_point ::
      real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> slp_point)
    \<in> borel_measurable lborel"
proof -
  have coordinate_measurable[measurable]:
      "\<And>i. (\<lambda>branch ::
          real^((unit + ('i + 'i)) \<times> bool).
          Complex (branch $ (i, False)) (branch $ (i, True)))
        \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI)
      (intro continuous_intros)
  have output_measurable:
      "(\<lambda>branch :: real^((unit + ('i + 'i)) \<times> bool).
        slp_signed_output slp_one_sided_branch_sign
          (slp_complex_family_unpack branch))
        \<in> borel_measurable lborel"
    unfolding slp_signed_output_def slp_complex_family_unpack_def
    by measurable
  show ?thesis
    unfolding slp_one_sided_packed_output_point_def
    using measurable_comp[OF output_measurable
      slp_complex_as_point_measurable]
    by (simp only: comp_def)
qed

definition slp_left_branch_complex_amplitude_packed ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      real^bool \<Rightarrow>
      real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> complex"
where
  "slp_left_branch_complex_amplitude_packed root_weight cutoff potential
      terminal_value output_factor root_coord branch_coord =
    root_weight
        (slp_complex_as_point (slp_complex_coordinate_unpack root_coord)) *
      slp_left_branch_complex_kernel_packed cutoff potential terminal_value
        root_coord branch_coord *
      output_factor (slp_one_sided_packed_output_point branch_coord)"

definition slp_left_branch_positive_amplitude_packed ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      real^bool \<Rightarrow>
      real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> ennreal"
where
  "slp_left_branch_positive_amplitude_packed R root_weight cutoff potential
      terminal_value output_factor root_coord branch_coord =
    ennreal (norm (root_weight
        (slp_complex_as_point (slp_complex_coordinate_unpack root_coord)))) *
      slp_left_branch_positive_kernel_packed R cutoff potential terminal_value
        root_coord branch_coord *
      ennreal (norm
        (output_factor (slp_one_sided_packed_output_point branch_coord)))"

lemma slp_left_branch_complex_amplitude_packed_measurable:
  assumes root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable[measurable]:
      "output_factor \<in> borel_measurable lborel"
  shows
    "case_prod (slp_left_branch_complex_amplitude_packed root_weight cutoff
        potential terminal_value output_factor)
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have root_point_measurable:
      "(\<lambda>root :: real^bool.
          slp_complex_as_point (slp_complex_coordinate_unpack root))
        \<in> borel_measurable lborel"
  proof -
    have unpack_borel:
        "(\<lambda>root :: real^bool.
          Complex (root $ False) (root $ True))
          \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
        (intro continuous_intros)
    have unpack_measurable:
        "(\<lambda>root :: real^bool.
          Complex (root $ False) (root $ True))
          \<in> borel_measurable lborel"
      using unpack_borel by (simp only: measurable_lborel2)
    show ?thesis
      unfolding slp_complex_coordinate_unpack_def
      using measurable_comp[OF unpack_measurable
        slp_complex_as_point_measurable]
      by (simp only: comp_def)
  qed
  have root_factor_measurable:
      "(\<lambda>x :: (real^bool) \<times>
          (real^((unit + ('i::finite + 'i)) \<times> bool)).
          root_weight
            (slp_complex_as_point (slp_complex_coordinate_unpack (fst x))))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using root_point_measurable by measurable
  have kernel_measurable:
      "case_prod (slp_left_branch_complex_kernel_packed cutoff potential
          terminal_value) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_left_branch_complex_kernel_packed_measurable)
      (rule cutoff_measurable potential_measurable
        terminal_value_measurable)+
  have output_factor_joint_measurable:
      "(\<lambda>x :: (real^bool) \<times>
          (real^((unit + ('i::finite + 'i)) \<times> bool)).
          output_factor (slp_one_sided_packed_output_point (snd x)))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  show ?thesis
    unfolding slp_left_branch_complex_amplitude_packed_def
    using root_factor_measurable kernel_measurable
      output_factor_joint_measurable
    by measurable
qed

theorem slp_left_branch_complex_amplitude_packed_positive_weight:
  assumes chain:
    "slp_left_branch_radius_chain_packed R root_coord
      (branch_coord :: real^((unit + ('i::finite + 'i)) \<times> bool))"
  shows
    "ennreal (norm (slp_left_branch_complex_amplitude_packed root_weight
        cutoff potential terminal_value output_factor root_coord
        branch_coord)) =
      slp_left_branch_positive_amplitude_packed R root_weight cutoff potential
        terminal_value output_factor root_coord branch_coord"
proof -
  have kernel:
      "ennreal (norm (slp_left_branch_complex_kernel_packed cutoff potential
          terminal_value root_coord branch_coord)) =
        slp_left_branch_positive_kernel_packed R cutoff potential
          terminal_value root_coord branch_coord"
    by (rule slp_left_branch_complex_kernel_packed_positive_weight[OF chain])
  show ?thesis
    unfolding slp_left_branch_complex_amplitude_packed_def
      slp_left_branch_positive_amplitude_packed_def
    by (simp add: norm_mult ennreal_mult kernel)
qed

end
