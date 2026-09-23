theory Inverse_Schrodinger_Lp_Natural_One_Sided_Cauchy_Error
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Amplitude_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Error_Mass"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Natural one-sided oscillatory Cauchy-product error\<close>

theorem slp_natural_one_sided_oscillatory_integral_tendsto_zero:
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
    and phase_measurable: "\<And>tau. psi tau \<in> borel_measurable ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)"
    and mass_decay: "((\<lambda>tau. nn_integral lborel
      (\<lambda>u. ennreal (norm (H tau u)) *
        slp_positive_root_output_density (2 * R) cutoff q
          (\<lambda>s. ennreal (norm (T s))) n Q u)) \<longlongrightarrow> 0) at_top"
  shows "eventually (\<lambda>tau. integrable ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)
    (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
      slp_natural_one_sided_weighted_amplitude n Q cutoff q T (H tau) z)) at_top"
    and "((\<lambda>tau. integral\<^sup>L ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_one_sided_weighted_amplitude n Q cutoff q T (H tau) z))
        \<longlongrightarrow> 0) at_top"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?f = "\<lambda>tau z. exp (\<i> * of_real (psi tau z)) *
    slp_natural_one_sided_weighted_amplitude n Q cutoff q T (H tau) z"
  let ?mass = "\<lambda>tau. nn_integral lborel (\<lambda>u. ennreal (norm (H tau u)) *
    slp_positive_root_output_density (2 * R) cutoff q
      (\<lambda>s. ennreal (norm (T s))) n Q u)"
  let ?I = "\<lambda>tau. integral\<^sup>L ?MJ (?f tau)"
  have finite_case: "integrable ?MJ (?f tau) \<and> ennreal (norm (?I tau)) \<le> ?mass tau"
    if finite: "?mass tau < top_class.top" for tau
    using slp_natural_one_sided_oscillatory_integral_bound[
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


context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_one_sided_cauchy_error_decay:
  fixes R C p :: real and X :: "slp_point set"
    and cutoff q Q phi :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and fourier_plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and phi_test: "slp_test_function_on UNIV phi"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phase_measurable: "\<And>tau. psi tau \<in> borel_measurable ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)"
  shows "eventually (\<lambda>tau. integrable ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)
    (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
      slp_natural_one_sided_weighted_amplitude n Q cutoff q (\<lambda>_. 1)
        (\<lambda>u. slp_center_average tau
        (\<lambda>x. phi x * slp_cauchy_transform orientation q x) u -
        phi u * slp_cauchy_transform orientation q u) z)) at_top"
    and "((\<lambda>tau. integral\<^sup>L ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_one_sided_weighted_amplitude n Q cutoff q (\<lambda>_. 1)
          (\<lambda>u. slp_center_average tau
        (\<lambda>x. phi x * slp_cauchy_transform orientation q x) u -
        phi u * slp_cauchy_transform orientation q u) z)) \<longlongrightarrow> 0) at_top"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?h = "\<lambda>x. phi x * slp_cauchy_transform orientation q x"
  let ?E = "\<lambda>tau u. slp_center_average tau ?h u - ?h u"
  have radius_nonnegative: "0 \<le> 2 * R" using R_nonnegative by simp
  have q_measurable[measurable]: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable: "(\<lambda>_::slp_point. 1::complex) \<in> borel_measurable lborel"
    by measurable
  have h_integrable: "integrable lborel ?h"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have h_measurable[measurable]: "?h \<in> borel_measurable lborel"
    using h_integrable by measurable
  have E_measurable: "?E tau \<in> borel_measurable lborel" for tau
  proof -
    have average[measurable]: "slp_center_average tau ?h \<in> borel_measurable lborel"
      by (rule slp_center_average_measurable[OF h_integrable])
    show ?thesis by measurable
  qed
  have mass_decay: "((\<lambda>tau. nn_integral lborel (\<lambda>u.
    slp_positive_root_output_density (2 * R) cutoff q (\<lambda>_. 1) n Q u *
      ennreal (norm (?E tau u)))) \<longlongrightarrow> 0) at_top"
    by (rule slp_natural_one_sided_cauchy_error_mass_decay[
      OF radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        fourier_plancherel phi_test])
  have ordered_mass: "((\<lambda>tau. nn_integral lborel (\<lambda>u.
    ennreal (norm (?E tau u)) *
      slp_positive_root_output_density (2 * R) cutoff q
        (\<lambda>s. ennreal (norm ((\<lambda>_::slp_point. 1::complex) s))) n Q u))
      \<longlongrightarrow> 0) at_top"
    using mass_decay by (simp add: mult.commute)
  note transfer = slp_natural_one_sided_oscillatory_integral_tendsto_zero[
    where n=n and psi=psi, OF R_nonnegative cutoff_measurable q_measurable
      unit_measurable Q_measurable E_measurable Q_support cutoff_support
      q_support phase_measurable ordered_mass]
  show "eventually (\<lambda>tau. integrable ?MJ
    (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
      slp_natural_one_sided_weighted_amplitude n Q cutoff q (\<lambda>_. 1) (?E tau) z)) at_top"
    by (rule transfer(1))
  show "((\<lambda>tau. integral\<^sup>L ?MJ
    (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
      slp_natural_one_sided_weighted_amplitude n Q cutoff q (\<lambda>_. 1) (?E tau) z))
      \<longlongrightarrow> 0) at_top"
    by (rule transfer(2))
qed

end

end
