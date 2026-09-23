theory Inverse_Schrodinger_Lp_Left_Neumann_Iterate_Joint_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Joint_Measurable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Exact_Neumann_Iterate_Bridge"
begin

section \<open>Joint measurability of finite left Neumann iterates\<close>

theorem slp_left_neumann_base_joint_measurable:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_left_neumann_base tau (fst pair) cutoff potential orientation
          (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have potential_joint[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point. potential (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using potential_measurable by measurable
  have transform_output[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_cauchy_transform orientation potential (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_cauchy_transform_joint_measurable[
          where field="\<lambda>_. potential", OF potential_joint])
  have diagonal_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point. (fst pair, fst pair)) \<in>
        measurable (lborel \<Otimes>\<^sub>M lborel)
          (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have transform_center[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_cauchy_transform orientation potential (fst pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using measurable_comp[OF diagonal_measurable transform_output]
    by (simp only: comp_def fst_conv snd_conv)
  have source_joint:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          cutoff (snd pair) *
            (slp_cauchy_transform orientation potential (snd pair) -
              slp_cauchy_transform orientation potential (fst pair))) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using cutoff_measurable by measurable
  show ?thesis
    unfolding slp_left_neumann_base_def
    by (rule slp_oscillatory_cauchy_inverses_joint_measurable(1)[
          where field="\<lambda>center terminal.
            cutoff terminal *
              (slp_cauchy_transform orientation potential terminal -
                slp_cauchy_transform orientation potential center)",
          OF source_joint])
qed

theorem slp_left_neumann_step_joint_measurable:
  fixes field :: "slp_point \<Rightarrow> slp_scalar_field"
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and field_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          field (fst pair) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_left_neumann_step tau (fst pair) cutoff potential
          (field (fst pair)) (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have inner_source:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          potential (snd pair) * field (fst pair) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using potential_measurable field_measurable by measurable
  have inner_inverse[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_dbar_psi_inverse tau (fst pair)
            (\<lambda>neg. potential neg * field (fst pair) neg)
            (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_oscillatory_cauchy_inverses_joint_measurable(2)[
          where field="\<lambda>center neg. potential neg * field center neg",
          OF inner_source])
  have outer_source:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          cutoff (snd pair) *
            slp_dbar_psi_inverse tau (fst pair)
              (\<lambda>neg. potential neg * field (fst pair) neg)
              (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using cutoff_measurable by measurable
  show ?thesis
    unfolding slp_left_neumann_step_def
    by (rule slp_oscillatory_cauchy_inverses_joint_measurable(1)[
          where field="\<lambda>center pos.
            cutoff pos *
              slp_dbar_psi_inverse tau center
                (\<lambda>neg. potential neg * field center neg) pos",
          OF outer_source])
qed

theorem slp_left_neumann_iterate_conull_zero_joint_measurable:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and centers_measurable: "centers \<in> sets lborel"
    and centers_conull: "AE center in lborel. center \<in> centers"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        if fst pair \<in> centers
        then slp_left_neumann_iterate n tau (fst pair) cutoff potential
          orientation (snd pair)
        else 0) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have iterate_joint:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_left_neumann_iterate n tau (fst pair) cutoff potential
            orientation (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  proof (induction n)
    case 0
    show ?case
      using slp_left_neumann_base_joint_measurable[
        OF cutoff_measurable potential_measurable, of tau orientation]
      by (simp only: slp_left_neumann_iterate_zero_eq_base)
  next
    case (Suc n)
    show ?case
      using slp_left_neumann_step_joint_measurable[
        OF cutoff_measurable potential_measurable Suc.IH, of tau]
      by (simp only: slp_left_neumann_iterate_Suc_eq_step)
  qed
  have center_predicate:
      "Measurable.pred (lborel \<Otimes>\<^sub>M lborel)
        (\<lambda>pair :: slp_point \<times> slp_point. fst pair \<in> centers)"
    using centers_measurable by measurable
  show ?thesis
    using iterate_joint center_predicate by measurable
qed

end
