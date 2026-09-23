theory Inverse_Schrodinger_Lp_Natural_Mixed_Oscillatory_Norm_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Unit_Transpose"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Natural mixed oscillatory integrals controlled by density masses\<close>

theorem slp_natural_mixed_weighted_amplitude_norm_mass_bound:
  fixes n m :: nat and Q cutoff q T qt U H :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and qt_measurable[measurable]: "qt \<in> borel_measurable lborel"
    and U_measurable[measurable]: "U \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and H_measurable[measurable]: "H \<in> borel_measurable lborel"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
  shows "nn_integral
    (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M
      (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
      \<Otimes>\<^sub>M lborel)
    (\<lambda>z. ennreal (norm (slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H z))) \<le>
    nn_integral lborel (\<lambda>c. ennreal (norm (H c)) *
      slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c)"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?F = "slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H"
  let ?lp = "\<lambda>z. map (\<lambda>k. (fst (fst (fst (fst z))) k,
    snd (fst (fst (fst z))) k)) [0..<n]"
  let ?rp = "\<lambda>z. map (\<lambda>k. (fst (fst (snd (fst z))) k,
    snd (fst (snd (fst z))) k)) [0..<m]"
  let ?s = "\<lambda>z. snd (fst (fst z))"
  let ?t = "\<lambda>z. snd (snd (fst z))"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z) (?lp z) (?s z) (?rp z) (?t z)"
  let ?K = "\<lambda>z. ennreal (norm (Q (snd z))) *
    slp_left_branch_positive_kernel_list (2 * R) cutoff q T (?lp z) (snd z) (?s z) *
    slp_left_branch_positive_kernel_list (2 * R) cutoff qt U (?rp z) (snd z) (?t z) *
    ennreal (norm (H (?center z)))"
  have positive_conjugate:
    "slp_left_branch_positive_kernel_list (2 * R)
      (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (qt x)) (\<lambda>x. cnj (U x))
      pairs origin terminal =
     slp_left_branch_positive_kernel_list (2 * R) cutoff qt U pairs origin terminal"
    for pairs origin terminal
  proof (induction pairs arbitrary: origin)
    case Nil
    then show ?case by simp
  next
    case (Cons pair pairs)
    then show ?case by (simp add: slp_positive_branch_block_weight_def)
  qed
  have majorant: "ennreal (norm (?F z)) \<le> ?K z" for z
  proof (cases "?F z = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have root_nonzero: "Q (snd z) \<noteq> 0"
      using False unfolding slp_natural_mixed_weighted_amplitude_def Let_def by auto
    have left_nonzero:
      "slp_left_branch_complex_kernel_list cutoff q T (?lp z) (snd z) (?s z) \<noteq> 0"
      using False unfolding slp_natural_mixed_weighted_amplitude_def Let_def by auto
    have right_nonzero:
      "slp_left_branch_complex_kernel_list
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (qt x)) (\<lambda>x. cnj (U x))
        (?rp z) (snd z) (?t z) \<noteq> 0"
      using False unfolding slp_natural_mixed_weighted_amplitude_def Let_def by auto
    have root_bound: "norm (snd z) \<le> R" by (rule Q_support[OF root_nonzero])
    have left_chain: "slp_left_branch_radius_chain (2 * R) (snd z) (?lp z) (?s z)"
      by (rule slp_left_branch_complex_kernel_list_support_chain[
            OF R_nonnegative root_bound cutoff_support q_support left_nonzero])
    have cutoff_conjugate_support: "\<And>x. cnj (cutoff x) \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      using cutoff_support by simp
    have qt_conjugate_support: "\<And>x. cnj (qt x) \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      using qt_support by simp
    have right_chain: "slp_left_branch_radius_chain (2 * R) (snd z) (?rp z) (?t z)"
      by (rule slp_left_branch_complex_kernel_list_support_chain[
            OF R_nonnegative root_bound cutoff_conjugate_support qt_conjugate_support right_nonzero])
    have left_weight:
      "ennreal (norm (slp_left_branch_complex_kernel_list cutoff q T
        (?lp z) (snd z) (?s z))) =
       slp_left_branch_positive_kernel_list (2 * R) cutoff q T (?lp z) (snd z) (?s z)"
      by (rule slp_left_branch_complex_kernel_list_positive_weight[OF left_chain])
    have right_weight:
      "ennreal (norm (slp_left_branch_complex_kernel_list
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (qt x)) (\<lambda>x. cnj (U x))
        (?rp z) (snd z) (?t z))) =
       slp_left_branch_positive_kernel_list (2 * R) cutoff qt U (?rp z) (snd z) (?t z)"
      using slp_left_branch_complex_kernel_list_positive_weight[
        OF right_chain, of "\<lambda>x. cnj (cutoff x)" "\<lambda>x. cnj (qt x)" "\<lambda>x. cnj (U x)"]
      by (simp only: positive_conjugate)
    have exact: "ennreal (norm (?F z)) = ?K z"
      unfolding slp_natural_mixed_weighted_amplitude_def Let_def
      by (simp add: norm_mult ennreal_mult left_weight right_weight)
    then show ?thesis by simp
  qed
  have test_measurable: "(\<lambda>c. ennreal (norm (H c))) \<in> borel_measurable lborel"
    by measurable
  have pairing:
    "nn_integral ?MJ ?K =
     nn_integral lborel (\<lambda>c. ennreal (norm (H c)) *
       slp_mixed_center_density (2 * R) cutoff q qt
         (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c)"
    using slp_natural_mixed_positive_density_pairing[
      OF cutoff_measurable q_measurable qt_measurable T_measurable
        U_measurable Q_measurable test_measurable, where R="2 * R" and n=n and m=m]
    by (simp only: case_prod_unfold)
  have integral_bound: "nn_integral ?MJ (\<lambda>z. ennreal (norm (?F z))) \<le> nn_integral ?MJ ?K"
    by (rule nn_integral_mono) (rule majorant)
  show ?thesis using integral_bound by (simp only: pairing)
qed

theorem slp_natural_mixed_oscillatory_integral_bound:
  fixes n m :: nat and Q cutoff q T qt U H :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and qt_measurable[measurable]: "qt \<in> borel_measurable lborel"
    and U_measurable[measurable]: "U \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and H_measurable[measurable]: "H \<in> borel_measurable lborel"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phase_measurable[measurable]: "psi \<in> borel_measurable
      (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M
      (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
      \<Otimes>\<^sub>M lborel)"
    and density_mass: "nn_integral lborel (\<lambda>c. ennreal (norm (H c)) *
      slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c) < top_class.top"
  shows "integrable (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M
      (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
      \<Otimes>\<^sub>M lborel)
    (\<lambda>z. exp (\<i> * of_real (psi z)) *
      slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H z)"
    and "ennreal (norm (integral\<^sup>L (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M
      (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
      \<Otimes>\<^sub>M lborel)
    (\<lambda>z. exp (\<i> * of_real (psi z)) *
      slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H z))) \<le> nn_integral lborel (\<lambda>c. ennreal (norm (H c)) *
      slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c)"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?A = "slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H"
  let ?f = "\<lambda>z. exp (\<i> * of_real (psi z)) * ?A z"
  let ?mass = "nn_integral lborel (\<lambda>c. ennreal (norm (H c)) *
    slp_mixed_center_density (2 * R) cutoff q qt
      (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c)"
  have amplitude_measurable[measurable]: "?A \<in> borel_measurable ?MJ"
    by (rule slp_natural_mixed_weighted_amplitude_measurable[
          OF cutoff_measurable q_measurable T_measurable qt_measurable
            U_measurable Q_measurable H_measurable])
  have f_measurable: "?f \<in> borel_measurable ?MJ" by measurable
  have norm_eq: "norm (?f z) = norm (?A z)" for z
    by (simp add: norm_mult norm_exp_i_times)
  have amplitude_bound: "nn_integral ?MJ (\<lambda>z. ennreal (norm (?A z))) \<le> ?mass"
    by (rule slp_natural_mixed_weighted_amplitude_norm_mass_bound[
          OF R_nonnegative cutoff_measurable q_measurable T_measurable
            qt_measurable U_measurable Q_measurable H_measurable
            Q_support cutoff_support q_support qt_support])
       (use assms in auto)
  have f_bound: "nn_integral ?MJ (\<lambda>z. ennreal (norm (?f z))) \<le> ?mass"
    using amplitude_bound by (simp only: norm_eq)
  have finite_norm: "nn_integral ?MJ (\<lambda>z. ennreal (norm (?f z))) < top_class.top"
    by (rule le_less_trans[OF f_bound density_mass])
  have f_integrable: "integrable ?MJ ?f"
    using f_measurable finite_norm by (simp add: integrable_iff_bounded)
  show "integrable ?MJ ?f" by (rule f_integrable)
  show "ennreal (norm (integral\<^sup>L ?MJ ?f)) \<le> ?mass"
    by (rule order_trans[OF
          Bochner_Integration.integral_norm_bound_ennreal[OF f_integrable] f_bound])
qed

theorem slp_natural_mixed_oscillatory_integral_tendsto_zero:
  fixes n m :: nat and Q cutoff q T qt U :: slp_scalar_field
    and H :: "real \<Rightarrow> slp_scalar_field"
  assumes R_nonnegative: "0 \<le> R"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and qt_measurable[measurable]: "qt \<in> borel_measurable lborel"
    and U_measurable[measurable]: "U \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and H_measurable: "\<And>tau. H tau \<in> borel_measurable lborel"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phase_measurable: "\<And>tau. psi tau \<in> borel_measurable
      (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M
      (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
      \<Otimes>\<^sub>M lborel)"
    and mass_decay: "((\<lambda>tau. nn_integral lborel (\<lambda>c. ennreal (norm (H tau c)) *
      slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c)) \<longlongrightarrow> 0) at_top"
  shows "eventually (\<lambda>tau. integrable (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M
      (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
      \<Otimes>\<^sub>M lborel)
    (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
      slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U (H tau) z)) at_top"
    and "((\<lambda>tau. integral\<^sup>L (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M
      (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
      \<Otimes>\<^sub>M lborel)
    (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
      slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U (H tau) z)) \<longlongrightarrow> 0) at_top"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?f = "\<lambda>tau z. exp (\<i> * of_real (psi tau z)) *
    slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U (H tau) z"
  let ?mass = "\<lambda>tau. nn_integral lborel (\<lambda>c. ennreal (norm (H tau c)) *
    slp_mixed_center_density (2 * R) cutoff q qt
      (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c)"
  let ?I = "\<lambda>tau. integral\<^sup>L ?MJ (?f tau)"
  have finite_case: "integrable ?MJ (?f tau) \<and> ennreal (norm (?I tau)) \<le> ?mass tau"
    if finite: "?mass tau < top_class.top" for tau
    using slp_natural_mixed_oscillatory_integral_bound[
      OF R_nonnegative cutoff_measurable q_measurable T_measurable
        qt_measurable U_measurable Q_measurable H_measurable[of tau]
        Q_support cutoff_support q_support qt_support phase_measurable[of tau] finite]
    by blast
  have eventually_mass: "eventually (\<lambda>tau. ?mass tau < (1::ennreal)) at_top"
    using order_tendstoD(2)[OF mass_decay, of "1::ennreal"] by simp
  have eventually_data:
    "eventually (\<lambda>tau. integrable ?MJ (?f tau) \<and>
      ennreal (norm (?I tau)) \<le> ?mass tau) at_top"
    using eventually_mass
  proof eventually_elim
    fix tau
    assume mass_small: "?mass tau < (1::ennreal)"
    have finite: "?mass tau < top_class.top"
      by (rule less_trans[OF mass_small]) simp
    show "integrable ?MJ (?f tau) \<and> ennreal (norm (?I tau)) \<le> ?mass tau"
      by (rule finite_case[OF finite])
  qed
  show "eventually (\<lambda>tau. integrable ?MJ (?f tau)) at_top"
    using eventually_data by eventually_elim auto
  have eventually_bound: "eventually (\<lambda>tau. ennreal (norm (?I tau)) \<le> ?mass tau) at_top"
    using eventually_data by eventually_elim auto
  have ennreal_norm_decay:
    "((\<lambda>tau. ennreal (norm (?I tau))) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_sandwich[where f="\<lambda>_. 0" and h="?mass"])
       (use eventually_bound mass_decay in auto)
  have cast_decay:
    "((\<lambda>tau. ennreal (norm (?I tau))) \<longlongrightarrow> ennreal 0) at_top"
    using ennreal_norm_decay by simp
  have norm_decay: "((\<lambda>tau. norm (?I tau)) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_ennrealD[OF cast_decay]) (simp_all add: eventuallyI)
  show "(?I \<longlongrightarrow> 0) at_top"
    by (rule tendsto_norm_zero_cancel[OF norm_decay])
qed

end
