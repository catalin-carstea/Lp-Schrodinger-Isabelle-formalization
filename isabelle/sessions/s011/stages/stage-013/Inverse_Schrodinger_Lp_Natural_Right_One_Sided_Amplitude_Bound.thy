theory Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Amplitude_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Amplitude"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Cauchy_Error"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Born_Conjugation_Invariance"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Generic natural right one-sided oscillatory bounds\<close>

theorem slp_natural_right_one_sided_oscillatory_integral_bound:
  fixes n :: nat and Q cutoff q T H :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and H_measurable[measurable]: "H \<in> borel_measurable lborel"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phase_measurable[measurable]: "psi \<in> borel_measurable
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)"
    and density_mass: "nn_integral lborel (\<lambda>u. ennreal (norm (H u)) *
      slp_positive_root_output_density (2 * R) cutoff q
        (\<lambda>s. ennreal (norm (T s))) n Q u) < top_class.top"
  shows "integrable
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T H z)"
    and "ennreal (norm (integral\<^sup>L
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T H z))) \<le>
      nn_integral lborel (\<lambda>u. ennreal (norm (H u)) *
        slp_positive_root_output_density (2 * R) cutoff q
          (\<lambda>s. ennreal (norm (T s))) n Q u)"
proof -
  let ?Qc = "\<lambda>x. cnj (Q x)"
  let ?cutoffc = "\<lambda>x. cnj (cutoff x)"
  let ?qc = "\<lambda>x. cnj (q x)"
  let ?Tc = "\<lambda>x. cnj (T x)"
  let ?Hc = "\<lambda>x. cnj (H x)"
  let ?psic = "\<lambda>z. - psi z"
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MJ = "((?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M
    (lborel :: slp_point measure)) \<Otimes>\<^sub>M lborel"
  let ?left = "\<lambda>z. exp (\<i> * of_real (?psic z)) *
    slp_natural_one_sided_weighted_amplitude n
      ?Qc ?cutoffc ?qc ?Tc ?Hc z"
  let ?right = "\<lambda>z. exp (\<i> * of_real (psi z)) *
    slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T H z"
  have cnj_borel: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          continuous_on_cnj[OF continuous_on_id]])
  have cutoffc_measurable[measurable]: "?cutoffc \<in> borel_measurable lborel"
    using measurable_comp[OF cutoff_measurable cnj_borel]
    by (simp only: comp_def)
  have qc_measurable[measurable]: "?qc \<in> borel_measurable lborel"
    using measurable_comp[OF q_measurable cnj_borel]
    by (simp only: comp_def)
  have Tc_measurable[measurable]: "?Tc \<in> borel_measurable lborel"
    using measurable_comp[OF T_measurable cnj_borel]
    by (simp only: comp_def)
  have Qc_measurable[measurable]: "?Qc \<in> borel_measurable lborel"
    using measurable_comp[OF Q_measurable cnj_borel]
    by (simp only: comp_def)
  have Hc_measurable[measurable]: "?Hc \<in> borel_measurable lborel"
    using measurable_comp[OF H_measurable cnj_borel]
    by (simp only: comp_def)
  have Qc_support: "norm x \<le> R" if "?Qc x \<noteq> 0" for x
    by (rule Q_support) (use that in simp)
  have cutoffc_support: "norm x \<le> R" if "?cutoffc x \<noteq> 0" for x
    by (rule cutoff_support) (use that in simp)
  have qc_support: "norm x \<le> R" if "?qc x \<noteq> 0" for x
    by (rule q_support) (use that in simp)
  have psic_measurable[measurable]: "?psic \<in> borel_measurable ?MJ"
    using phase_measurable by measurable
  have density_mass_c:
    "nn_integral lborel (\<lambda>u. ennreal (norm (?Hc u)) *
      slp_positive_root_output_density (2 * R) ?cutoffc ?qc
        (\<lambda>s. ennreal (norm (?Tc s))) n ?Qc u) < top_class.top"
    using density_mass
    by (simp add: slp_positive_root_output_density_conjugate)
  note left_bound = slp_natural_one_sided_oscillatory_integral_bound[
    where n=n and Q="?Qc" and cutoff="?cutoffc" and q="?qc" and T="?Tc"
      and H="?Hc" and psi="?psic",
    OF R_nonnegative cutoffc_measurable qc_measurable Tc_measurable
      Qc_measurable Hc_measurable Qc_support cutoffc_support qc_support
      psic_measurable density_mass_c]
  have right_left:
    "slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T H z =
      cnj (slp_natural_one_sided_weighted_amplitude n
        ?Qc ?cutoffc ?qc ?Tc ?Hc z)" for z
    by (rule slp_natural_right_one_sided_weighted_amplitude_conjugate)
  have phase_conjugate:
    "exp (\<i> * of_real (psi z)) =
      cnj (exp (\<i> * of_real (?psic z)))" for z
    by (simp add: exp_cnj algebra_simps)
  have pointwise: "?right z = cnj (?left z)" for z
    by (simp only: right_left[of z] phase_conjugate[of z]
        complex_cnj_mult)
  have integrand_eq: "?right = (\<lambda>z. cnj (?left z))"
    by (rule ext) (rule pointwise)
  have conjugate_integrable: "integrable ?MJ (\<lambda>z. cnj (?left z))"
    by (rule integrable_cnj[OF left_bound(1)])
  show "integrable ?MJ ?right"
    using conjugate_integrable by (simp only: integrand_eq)
  have integral_eq:
    "integral\<^sup>L ?MJ ?right = cnj (integral\<^sup>L ?MJ ?left)"
  proof -
    have rewrite:
      "integral\<^sup>L ?MJ ?right = integral\<^sup>L ?MJ (\<lambda>z. cnj (?left z))"
      by (simp only: integrand_eq)
    have move:
      "integral\<^sup>L ?MJ (\<lambda>z. cnj (?left z)) =
        cnj (integral\<^sup>L ?MJ ?left)"
      by (rule Bochner_Integration.integral_cnj)
    show ?thesis using rewrite move by simp
  qed
  show "ennreal (norm (integral\<^sup>L ?MJ ?right)) \<le>
      nn_integral lborel (\<lambda>u. ennreal (norm (H u)) *
        slp_positive_root_output_density (2 * R) cutoff q
          (\<lambda>s. ennreal (norm (T s))) n Q u)"
    using left_bound(2) density_mass_c
    by (simp add: integral_eq slp_positive_root_output_density_conjugate)
qed


theorem slp_natural_right_one_sided_oscillatory_integral_tendsto_zero:
  fixes n :: nat and Q cutoff q T :: slp_scalar_field
    and H :: "real \<Rightarrow> slp_scalar_field"
  assumes R_nonnegative: "0 \<le> R"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_measurable[measurable]: "q \<in> borel_measurable lborel"
    and T_measurable[measurable]: "T \<in> borel_measurable lborel"
    and Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    and H_measurable: "\<And>tau. H tau \<in> borel_measurable lborel"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phase_measurable: "\<And>tau. psi tau \<in> borel_measurable
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)"
    and mass_decay: "((\<lambda>tau. nn_integral lborel
      (\<lambda>u. ennreal (norm (H tau u)) *
        slp_positive_root_output_density (2 * R) cutoff q
          (\<lambda>s. ennreal (norm (T s))) n Q u)) \<longlongrightarrow> 0) at_top"
  shows "eventually (\<lambda>tau. integrable
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T
          (H tau) z)) at_top"
    and "((\<lambda>tau. integral\<^sup>L
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T
          (H tau) z)) \<longlongrightarrow> 0) at_top"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MJ = "((?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M
    (lborel :: slp_point measure)) \<Otimes>\<^sub>M lborel"
  let ?f = "\<lambda>tau z. exp (\<i> * of_real (psi tau z)) *
    slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T (H tau) z"
  let ?mass = "\<lambda>tau. nn_integral lborel
    (\<lambda>u. ennreal (norm (H tau u)) *
      slp_positive_root_output_density (2 * R) cutoff q
        (\<lambda>s. ennreal (norm (T s))) n Q u)"
  let ?I = "\<lambda>tau. integral\<^sup>L ?MJ (?f tau)"
  have finite_case:
    "integrable ?MJ (?f tau) \<and> ennreal (norm (?I tau)) \<le> ?mass tau"
    if finite: "?mass tau < top_class.top" for tau
    using slp_natural_right_one_sided_oscillatory_integral_bound[
      where n=n, OF R_nonnegative cutoff_measurable q_measurable T_measurable
        Q_measurable H_measurable[of tau] Q_support cutoff_support q_support
        phase_measurable[of tau] finite]
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
  have eventually_bound:
    "eventually (\<lambda>tau. ennreal (norm (?I tau)) \<le> ?mass tau) at_top"
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
