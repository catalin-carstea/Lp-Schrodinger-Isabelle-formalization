theory Inverse_Schrodinger_Lp_CGO_Born_Remainder_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Carrier_Remainder_Integrability"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Left_Neumann_Iterate_Joint_Measurable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Right_Neumann_Iterate_Joint_Measurable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Global Borel measurability of the explicit Born remainder\<close>

lemma slp_left_neumann_iterate_joint_measurable:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_left_neumann_iterate n tau (fst pair) cutoff potential orientation
          (snd pair)) \<in>
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

lemma slp_right_neumann_iterate_joint_measurable:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_right_neumann_iterate n tau (fst pair) cutoff potential orientation
          (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof (induction n)
  case 0
  show ?case
    using slp_right_neumann_base_joint_measurable[
      OF cutoff_measurable potential_measurable, of tau orientation]
    by (simp only: slp_right_neumann_iterate_zero_eq_base)
next
  case (Suc n)
  show ?case
    using slp_right_neumann_step_joint_measurable[
      OF cutoff_measurable potential_measurable Suc.IH, of tau]
    by (simp only: slp_right_neumann_iterate_Suc_eq_step)
qed

lemma slp_left_neumann_restricted_term_joint_measurable:
  assumes X_measurable: "X \<in> sets lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_restrict_field X
          (slp_neumann_iterate
            (slp_left_neumann_step tau (fst pair) cutoff potential)
            (slp_left_neumann_base tau (fst pair) cutoff potential
              SLP_Dbar_Inverse) j)
          (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have exact_iterate:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_left_neumann_iterate j tau (fst pair) cutoff potential
            SLP_Dbar_Inverse (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_left_neumann_iterate_joint_measurable[
          OF cutoff_measurable potential_measurable])
  have abstract_iterate:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_neumann_iterate
            (slp_left_neumann_step tau (fst pair) cutoff potential)
            (slp_left_neumann_base tau (fst pair) cutoff potential
              SLP_Dbar_Inverse) j (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using exact_iterate
    by (simp only: slp_left_neumann_iterate_eq_abstract)
  show ?thesis
    unfolding slp_restrict_field_def
    using X_measurable abstract_iterate by measurable
qed

lemma slp_right_neumann_restricted_term_joint_measurable:
  assumes X_measurable: "X \<in> sets lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_restrict_field X
          (slp_neumann_iterate
            (slp_right_neumann_step tau (fst pair) cutoff potential)
            (slp_right_neumann_base tau (fst pair) cutoff potential
              SLP_Partial_Inverse) j)
          (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have exact_iterate:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_right_neumann_iterate j tau (fst pair) cutoff potential
            SLP_Partial_Inverse (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_right_neumann_iterate_joint_measurable[
          OF cutoff_measurable potential_measurable])
  have abstract_iterate:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_neumann_iterate
            (slp_right_neumann_step tau (fst pair) cutoff potential)
            (slp_right_neumann_base tau (fst pair) cutoff potential
              SLP_Partial_Inverse) j (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using exact_iterate
    by (simp only: slp_right_neumann_iterate_eq_abstract)
  show ?thesis
    unfolding slp_restrict_field_def
    using X_measurable abstract_iterate by measurable
qed

theorem slp_left_neumann_series_sum_joint_measurable:
  assumes X_measurable: "X \<in> sets lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_left_neumann_series_sum X tau (fst pair) cutoff potential
          (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  unfolding slp_left_neumann_series_sum_def
  by (rule borel_measurable_suminf)
    (rule slp_left_neumann_restricted_term_joint_measurable[OF assms])

theorem slp_right_neumann_series_sum_joint_measurable:
  assumes X_measurable: "X \<in> sets lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_right_neumann_series_sum X tau (fst pair) cutoff potential
          (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  unfolding slp_right_neumann_series_sum_def
  by (rule borel_measurable_suminf)
    (rule slp_right_neumann_restricted_term_joint_measurable[OF assms])

lemma slp_left_neumann_partial_sum_joint_measurable:
  assumes X_measurable: "X \<in> sets lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_left_neumann_partial_sum X N tau (fst pair) cutoff potential
          (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  unfolding slp_left_neumann_partial_sum_def
  by (rule borel_measurable_sum)
    (rule slp_left_neumann_restricted_term_joint_measurable[OF assms])

lemma slp_right_neumann_partial_sum_joint_measurable:
  assumes X_measurable: "X \<in> sets lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_right_neumann_partial_sum X N tau (fst pair) cutoff potential
          (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  unfolding slp_right_neumann_partial_sum_def
  by (rule borel_measurable_sum)
    (rule slp_right_neumann_restricted_term_joint_measurable[OF assms])

theorem slp_cgo_born_neumann_remainder_joint_measurable:
  assumes X_measurable: "X \<in> sets lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_cgo_born_neumann_remainder X N M tau (fst pair) cutoff q qt
          (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have left_series[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_left_neumann_series_sum X tau (fst pair) cutoff q
            (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_left_neumann_series_sum_joint_measurable[OF
          X_measurable cutoff_measurable q_measurable])
  have right_series[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_right_neumann_series_sum X tau (fst pair) cutoff qt
            (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_right_neumann_series_sum_joint_measurable[OF
          X_measurable cutoff_measurable qt_measurable])
  have left_partial[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_left_neumann_partial_sum X N tau (fst pair) cutoff q
            (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_left_neumann_partial_sum_joint_measurable[OF
          X_measurable cutoff_measurable q_measurable])
  have right_partial[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_right_neumann_partial_sum X M tau (fst pair) cutoff qt
            (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_right_neumann_partial_sum_joint_measurable[OF
          X_measurable cutoff_measurable qt_measurable])
  have center_lift:
      "(\<lambda>pair :: slp_point \<times> slp_point. fst pair) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have root_lift:
      "(\<lambda>pair :: slp_point \<times> slp_point. snd pair) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have center_nth[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point. fst pair $ i) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)" for i :: 2
    using measurable_comp[OF center_lift borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have root_nth[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point. snd pair $ i) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)" for i :: 2
    using measurable_comp[OF root_lift borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have kernel[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_center_kernel (- tau) (fst pair) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding slp_center_kernel_def slp_center_phase_def by measurable
  show ?thesis
    unfolding slp_cgo_born_neumann_remainder_def
      slp_left_neumann_series_tail_def slp_right_neumann_series_tail_def
    by measurable
qed

theorem slp_cgo_born_tested_neumann_remainder_outer_measurable:
  assumes X_measurable: "X \<in> sets lborel"
    and phi_measurable: "phi \<in> borel_measurable lborel"
    and Q_measurable: "Q \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
  shows
    "(\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z))
      \<in> borel_measurable lborel"
proof -
  have remainder_joint[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_cgo_born_neumann_remainder X N M tau (fst pair) cutoff q qt
            (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_cgo_born_neumann_remainder_joint_measurable[OF
          X_measurable cutoff_measurable q_measurable qt_measurable])
  have weighted_joint:
      "(\<lambda>pair :: slp_point \<times> slp_point. Q (snd pair) *
          slp_cgo_born_neumann_remainder X N M tau (fst pair) cutoff q qt
            (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using Q_measurable by measurable
  have root_integral_measurable:
      "(\<lambda>c. integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z))
        \<in> borel_measurable lborel"
    by (rule lborel.borel_measurable_lebesgue_integral[
          where f="\<lambda>c z. Q z *
            slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z"])
      (use weighted_joint in simp)
  show ?thesis
    using phi_measurable root_integral_measurable by measurable
qed

end
