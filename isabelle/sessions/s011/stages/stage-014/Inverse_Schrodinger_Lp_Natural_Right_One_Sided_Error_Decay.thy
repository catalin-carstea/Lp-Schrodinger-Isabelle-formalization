theory Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Error_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Amplitude_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Smooth_Error_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Physical natural right one-sided averaging errors\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_right_one_sided_smooth_error_decay:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q Q phi :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
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
    and phase_measurable: "\<And>tau. psi tau \<in> borel_measurable
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)"
  shows "eventually (\<lambda>tau. integrable
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q
          (slp_cauchy_transform orientation q)
          (\<lambda>u. slp_center_average tau phi u - phi u) z)) at_top"
    and "((\<lambda>tau. integral\<^sup>L
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q
          (slp_cauchy_transform orientation q)
          (\<lambda>u. slp_center_average tau phi u - phi u) z))
      \<longlongrightarrow> 0) at_top"
proof -
  interpret hf: hormander_euclidean_l2_fourier_plancherel
    by standard (rule fourier_plancherel)
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?E = "\<lambda>tau u. slp_center_average tau phi u - phi u"
  let ?DA = "slp_positive_root_output_density (2 * R) cutoff q
    (\<lambda>s. ennreal (norm (?A s))) n Q"
  have q_measurable[measurable]: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have A_measurable[measurable]: "?A \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper q_lp])
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable[measurable]: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have average_measurable:
      "slp_center_average tau phi \<in> borel_measurable lborel" for tau
    by (rule slp_center_average_measurable[OF phi_integrable])
  have E_measurable: "?E tau \<in> borel_measurable lborel" for tau
    using average_measurable[of tau] by measurable
  have DA_measurable: "?DA \<in> borel_measurable lborel"
    by (rule slp_positive_root_output_density_measurable[
      OF cutoff_measurable q_measurable _ Q_measurable]) measurable
  have DA_mass: "nn_integral lborel ?DA < top_class.top"
    by (rule slp_natural_one_sided_cauchy_terminal_density_mass_finite[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        cutoff_support q_support])
  have DA_finite: "AE u in lborel. ?DA u < top_class.top"
  proof -
    have integral_not_infinity: "nn_integral lborel ?DA \<noteq> \<infinity>"
      using DA_mass by simp
    have raw: "AE u in lborel. ?DA u \<noteq> \<infinity>"
      by (rule nn_integral_PInf_AE[OF DA_measurable integral_not_infinity])
    show ?thesis using raw by (simp add: less_top)
  qed
  have DA_real_measurable:
      "(\<lambda>u. enn2real (?DA u)) \<in> borel_measurable lborel"
    using DA_measurable by measurable
  have DA_real_mass:
      "nn_integral lborel (\<lambda>u. enn2real (?DA u)) = nn_integral lborel ?DA"
    by (rule nn_integral_cong_AE)
      (use DA_finite in \<open>eventually_elim, simp\<close>)
  have DA_real_integrable:
      "integrable lborel (\<lambda>u. enn2real (?DA u))"
  proof (rule integrableI_nonneg)
    show "(\<lambda>u. enn2real (?DA u)) \<in> borel_measurable lborel"
      by (rule DA_real_measurable)
    show "AE u in lborel. 0 \<le> enn2real (?DA u)" by simp
    show "nn_integral lborel (\<lambda>u. enn2real (?DA u)) < \<infinity>"
      using DA_real_mass DA_mass by simp
  qed
  have uniform:
      "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi at_top"
    by (rule hf.slp_center_average_smooth_uniform_limit[OF phi_test])
  have mass_decay:
      "((\<lambda>tau. nn_integral lborel (\<lambda>u. ?DA u *
        ennreal (norm (?E tau u)))) \<longlongrightarrow> 0) at_top"
    by (rule slp_positive_ennreal_uniform_difference_nn_integral_tendsto_zero[
      OF DA_finite DA_real_integrable average_measurable phi_measurable uniform])
  have ordered_mass:
      "((\<lambda>tau. nn_integral lborel (\<lambda>u.
        ennreal (norm (?E tau u)) *
          slp_positive_root_output_density (2 * R) cutoff q
            (\<lambda>s. ennreal (norm (?A s))) n Q u)) \<longlongrightarrow> 0) at_top"
    using mass_decay by (simp only: mult.commute)
  note transfer = slp_natural_right_one_sided_oscillatory_integral_tendsto_zero[
    where n=n and psi=psi, OF R_nonnegative cutoff_measurable q_measurable
      A_measurable Q_measurable E_measurable Q_support cutoff_support
      q_support phase_measurable ordered_mass]
  show "eventually (\<lambda>tau. integrable ?MJ
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q ?A (?E tau) z)) at_top"
    by (rule transfer(1))
  show "((\<lambda>tau. integral\<^sup>L ?MJ
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q ?A (?E tau) z))
      \<longlongrightarrow> 0) at_top"
    by (rule transfer(2))
qed


theorem slp_natural_right_one_sided_cauchy_error_decay:
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
    and phase_measurable: "\<And>tau. psi tau \<in> borel_measurable
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)"
  shows "eventually (\<lambda>tau. integrable
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q (\<lambda>_. 1)
          (\<lambda>u. slp_center_average tau
            (\<lambda>x. phi x * slp_cauchy_transform orientation q x) u -
            phi u * slp_cauchy_transform orientation q u) z)) at_top"
    and "((\<lambda>tau. integral\<^sup>L
      ((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M lborel)
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q (\<lambda>_. 1)
          (\<lambda>u. slp_center_average tau
            (\<lambda>x. phi x * slp_cauchy_transform orientation q x) u -
            phi u * slp_cauchy_transform orientation q u) z))
      \<longlongrightarrow> 0) at_top"
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
  have unit_measurable:
      "(\<lambda>_::slp_point. 1::complex) \<in> borel_measurable lborel"
    by measurable
  have h_integrable: "integrable lborel ?h"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have h_measurable[measurable]: "?h \<in> borel_measurable lborel"
    using h_integrable by measurable
  have E_measurable: "?E tau \<in> borel_measurable lborel" for tau
  proof -
    have average[measurable]:
        "slp_center_average tau ?h \<in> borel_measurable lborel"
      by (rule slp_center_average_measurable[OF h_integrable])
    show ?thesis by measurable
  qed
  have mass_decay:
      "((\<lambda>tau. nn_integral lborel (\<lambda>u.
        slp_positive_root_output_density (2 * R) cutoff q (\<lambda>_. 1) n Q u *
          ennreal (norm (?E tau u)))) \<longlongrightarrow> 0) at_top"
    by (rule slp_natural_one_sided_cauchy_error_mass_decay[
      OF radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        fourier_plancherel phi_test])
  have ordered_mass:
      "((\<lambda>tau. nn_integral lborel (\<lambda>u.
        ennreal (norm (?E tau u)) *
          slp_positive_root_output_density (2 * R) cutoff q
            (\<lambda>s. ennreal (norm ((\<lambda>_::slp_point. 1::complex) s))) n Q u))
        \<longlongrightarrow> 0) at_top"
    using mass_decay by (simp add: mult.commute)
  note transfer = slp_natural_right_one_sided_oscillatory_integral_tendsto_zero[
    where n=n and psi=psi, OF R_nonnegative cutoff_measurable q_measurable
      unit_measurable Q_measurable E_measurable Q_support cutoff_support
      q_support phase_measurable ordered_mass]
  show "eventually (\<lambda>tau. integrable ?MJ
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q
          (\<lambda>_. 1) (?E tau) z)) at_top"
    by (rule transfer(1))
  show "((\<lambda>tau. integral\<^sup>L ?MJ
      (\<lambda>z. exp (\<i> * of_real (psi tau z)) *
        slp_natural_right_one_sided_weighted_amplitude n Q cutoff q
          (\<lambda>_. 1) (?E tau) z)) \<longlongrightarrow> 0) at_top"
    by (rule transfer(2))
qed

end

end
