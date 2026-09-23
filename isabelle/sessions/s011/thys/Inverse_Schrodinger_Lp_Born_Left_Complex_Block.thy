theory Inverse_Schrodinger_Lp_Born_Left_Complex_Block
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Branch_Functional"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Near_Center_Operator_Bridge"
begin

section \<open>Exact complex left-branch block\<close>

definition slp_left_branch_complex_block ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow>
      complex"
where
  "slp_left_branch_complex_block cutoff potential origin pos_point
      neg_point =
    slp_cauchy_kernel SLP_Partial_Inverse origin pos_point *
    cutoff pos_point *
    slp_cauchy_kernel SLP_Dbar_Inverse pos_point neg_point *
    potential neg_point"

lemma slp_left_branch_complex_block_joint_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
  shows
    "case_prod (slp_left_branch_complex_block cutoff potential origin)
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have cutoff_borel[measurable]: "cutoff \<in> borel_measurable borel"
    using cutoff_measurable by simp
  have potential_borel[measurable]: "potential \<in> borel_measurable borel"
    using potential_measurable by simp
  have block_borel:
      "case_prod (slp_left_branch_complex_block cutoff potential origin)
        \<in> borel_measurable
          ((borel :: slp_point measure) \<Otimes>\<^sub>M
            (borel :: slp_point measure))"
  proof -
    let ?product_borel =
      "(borel :: slp_point measure) \<Otimes>\<^sub>M
        (borel :: slp_point measure)"
    have fst_measurable:
        "fst \<in> measurable ?product_borel (borel :: slp_point measure)"
      by (rule measurable_fst)
    have snd_measurable:
        "snd \<in> measurable ?product_borel (borel :: slp_point measure)"
      by (rule measurable_snd)
    have first_kernel_borel:
        "slp_cauchy_kernel SLP_Partial_Inverse origin
          \<in> borel_measurable borel"
      using slp_cauchy_kernel_borel_measurable by simp
    have first_kernel_pair[measurable]:
        "(\<lambda>pair. slp_cauchy_kernel SLP_Partial_Inverse origin
            (fst pair)) \<in> borel_measurable ?product_borel"
      by (rule measurable_compose[OF fst_measurable first_kernel_borel])
    have cutoff_pair[measurable]:
        "(\<lambda>pair. cutoff (fst pair))
          \<in> borel_measurable ?product_borel"
      by (rule measurable_compose[OF fst_measurable cutoff_borel])
    have point_fst[measurable]:
        "(\<lambda>pair. slp_point_as_complex (fst pair))
          \<in> borel_measurable ?product_borel"
      by (rule measurable_compose[OF fst_measurable
            slp_point_as_complex_borel_measurable])
    have point_snd[measurable]:
        "(\<lambda>pair. slp_point_as_complex (snd pair))
          \<in> borel_measurable ?product_borel"
      by (rule measurable_compose[OF snd_measurable
            slp_point_as_complex_borel_measurable])
    have denominator_pair[measurable]:
        "(\<lambda>pair. slp_cauchy_denominator SLP_Dbar_Inverse
            (fst pair) (snd pair)) \<in> borel_measurable ?product_borel"
    proof -
      have denominator_eq:
          "(\<lambda>pair. slp_cauchy_denominator SLP_Dbar_Inverse
              (fst pair) (snd pair)) =
            (\<lambda>pair. slp_point_as_complex (fst pair) -
              slp_point_as_complex (snd pair))"
        by (rule ext)
          (simp only: slp_cauchy_denominator_def
            slp_cauchy_orientation.simps)
      show ?thesis
        unfolding denominator_eq by measurable
    qed
    have second_kernel_pair[measurable]:
        "(\<lambda>pair. slp_cauchy_kernel SLP_Dbar_Inverse
            (fst pair) (snd pair)) \<in> borel_measurable ?product_borel"
      unfolding slp_cauchy_kernel_def
      by measurable
    have potential_pair[measurable]:
        "(\<lambda>pair. potential (snd pair))
          \<in> borel_measurable ?product_borel"
      by (rule measurable_compose[OF snd_measurable potential_borel])
    show ?thesis
      unfolding slp_left_branch_complex_block_def
      by measurable
  qed
  have source_sets:
      "sets ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure)) =
        sets ((borel :: slp_point measure) \<Otimes>\<^sub>M
          (borel :: slp_point measure))"
    by (rule sets_pair_measure_cong; simp)
  have measurable_sets_eq:
      "measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure)) borel =
        measurable
          ((borel :: slp_point measure) \<Otimes>\<^sub>M
            (borel :: slp_point measure)) borel"
    by (rule measurable_cong_sets[OF source_sets refl])
  show ?thesis
    using block_borel measurable_sets_eq by blast
qed

lemma slp_left_branch_complex_block_norm:
  "norm (slp_left_branch_complex_block cutoff potential origin pos_point
      neg_point) =
    slp_radial_inverse (origin - pos_point) * norm (cutoff pos_point) *
    slp_radial_inverse (pos_point - neg_point) * norm (potential neg_point)"
  unfolding slp_left_branch_complex_block_def
  by (simp only: norm_mult slp_cauchy_kernel_norm)

lemma slp_left_branch_complex_block_positive_weight:
  assumes origin_pos_radius: "norm (origin - pos_point) \<le> R"
    and pos_neg_radius: "norm (pos_point - neg_point) \<le> R"
  shows
    "ennreal (norm (slp_left_branch_complex_block cutoff potential origin
        pos_point neg_point)) =
      slp_positive_branch_block_weight R cutoff potential origin pos_point
        neg_point"
proof -
  have first_kernel:
    "slp_localized_cauchy_kernel R (origin - pos_point) =
      slp_radial_inverse (origin - pos_point)"
    using slp_localized_cauchy_kernel_inside[OF origin_pos_radius]
    by (simp only: slp_radial_inverse_def)
  have second_kernel:
    "slp_localized_cauchy_kernel R (pos_point - neg_point) =
      slp_radial_inverse (pos_point - neg_point)"
    using slp_localized_cauchy_kernel_inside[OF pos_neg_radius]
    by (simp only: slp_radial_inverse_def)
  show ?thesis
    unfolding slp_positive_branch_block_weight_def
      slp_left_branch_complex_block_norm first_kernel second_kernel
    by (simp add: ennreal_mult)
qed

end
