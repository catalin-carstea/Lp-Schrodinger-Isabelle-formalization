theory Inverse_Schrodinger_Lp_Natural_Mixed_Smooth_Cross_Error_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Oscillatory_Norm_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Center_Average_Smooth_Convergence"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Center_Error_L2_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_L2_Error_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Finite_Center_Transpose_Bound"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Physical center errors against positive L2 densities\<close>

theorem slp_positive_l2_center_error_mass_decay:
  fixes D :: "slp_point \<Rightarrow> ennreal" and h :: slp_scalar_field
  assumes fourier_plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and density_l2: "slp_positive_ennreal_lp_on_plane 2 D"
    and h_integrable: "integrable lborel h"
    and h_l2: "aim_complex_lp_on_plane 2 h"
  shows "((\<lambda>tau. nn_integral lborel (\<lambda>c. D c *
    ennreal (norm (slp_center_average tau h c - h c)))) \<longlongrightarrow> 0) at_top"
proof -
  interpret hf: hormander_euclidean_l2_fourier_plancherel
    by standard (rule fourier_plancherel)
  let ?E = "\<lambda>tau c. slp_center_average tau h c - h c"
  let ?aux = "\<lambda>tau. if 0 < tau then ?E tau else (\<lambda>_. 0)"
  have aux_l2: "aim_complex_lp_on_plane 2 (?aux tau)" for tau
  proof (cases "0 < tau")
    case True
    have actual: "aim_complex_lp_on_plane 2 (?E tau)"
      by (rule hf.slp_center_average_error_l2_l1_l2[OF True h_integrable h_l2])
    show ?thesis using True actual by simp
  next
    case False
    show ?thesis using False unfolding aim_complex_lp_on_plane_def by simp
  qed
  have actual_square:
    "((\<lambda>tau. nn_integral lborel (\<lambda>c. ennreal (norm (?E tau c)) ^ 2))
      \<longlongrightarrow> 0) at_top"
    by (rule hf.slp_center_average_error_square_nn_integral_tendsto_zero[
          OF h_integrable h_l2])
  have positive: "eventually (\<lambda>tau::real. 0 < tau) at_top" by simp
  have square_eq:
    "eventually (\<lambda>tau. nn_integral lborel (\<lambda>c. ennreal (norm (?aux tau c)) ^ 2) =
      nn_integral lborel (\<lambda>c. ennreal (norm (?E tau c)) ^ 2)) at_top"
    using positive by eventually_elim simp
  have aux_square:
    "((\<lambda>tau. nn_integral lborel (\<lambda>c. ennreal (norm (?aux tau c)) ^ 2))
      \<longlongrightarrow> 0) at_top"
    by (rule tendsto_cong[OF square_eq, THEN iffD2]) (rule actual_square)
  have aux_mass:
    "((\<lambda>tau. nn_integral lborel (\<lambda>c. D c * ennreal (norm (?aux tau c))))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_positive_ennreal_complex_l2_pairing_tendsto_zero[
          OF density_l2 aux_l2 aux_square])
  have mass_eq:
    "eventually (\<lambda>tau. nn_integral lborel (\<lambda>c. D c * ennreal (norm (?E tau c))) =
      nn_integral lborel (\<lambda>c. D c * ennreal (norm (?aux tau c)))) at_top"
    using positive by eventually_elim simp
  show ?thesis
    by (rule tendsto_cong[OF mass_eq, THEN iffD2]) (rule aux_mass)
qed

section \<open>Natural mixed cross error masses\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_mixed_cauchy_cross_error_mass_decay:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes fourier_plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
  shows left_cross:
    "((\<lambda>tau. nn_integral lborel (\<lambda>c.
      slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>s. ennreal (norm (slp_cauchy_transform lo q s))) (\<lambda>_. 1) n m Q c *
      ennreal (norm (slp_center_average tau
        (\<lambda>x. phi x * slp_cauchy_transform ro qt x) c -
        phi c * slp_cauchy_transform ro qt c)))) \<longlongrightarrow> 0) at_top"
    and right_cross:
    "((\<lambda>tau. nn_integral lborel (\<lambda>c.
      slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>_. 1) (\<lambda>t. ennreal (norm (slp_cauchy_transform ro qt t))) n m Q c *
      ennreal (norm (slp_center_average tau
        (\<lambda>x. phi x * slp_cauchy_transform lo q x) c -
        phi c * slp_cauchy_transform lo q c)))) \<longlongrightarrow> 0) at_top"
proof -
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?DA = "slp_mixed_center_density (2 * R) cutoff q qt
    (\<lambda>s. ennreal (norm (?A s))) (\<lambda>_. 1) n m Q"
  let ?DB = "slp_mixed_center_density (2 * R) cutoff q qt
    (\<lambda>_. 1) (\<lambda>t. ennreal (norm (?B t))) n m Q"
  have DA_l2: "slp_positive_ennreal_lp_on_plane 2 ?DA"
    by (rule slp_natural_mixed_cauchy_cross_density_l2(1)[OF
          R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
          cutoff_support q_support qt_support, where n=n and m=m and lo=lo])
       (use assms in auto)
  have DB_l2: "slp_positive_ennreal_lp_on_plane 2 ?DB"
    by (rule slp_natural_mixed_cauchy_cross_density_l2(2)[OF
          R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
          cutoff_support q_support qt_support, where n=n and m=m and ro=ro])
       (use assms in auto)
  have source_A_integrable: "integrable lborel (\<lambda>x. phi x * ?A x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have source_B_integrable: "integrable lborel (\<lambda>x. phi x * ?B x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper qt_lp phi_test])
  have source_A_l2: "aim_complex_lp_on_plane 2 (\<lambda>x. phi x * ?A x)"
    by (rule slp_test_cauchy_product_l2[OF p_lower p_upper q_lp phi_test])
  have source_B_l2: "aim_complex_lp_on_plane 2 (\<lambda>x. phi x * ?B x)"
    by (rule slp_test_cauchy_product_l2[OF p_lower p_upper qt_lp phi_test])
  show "((\<lambda>tau. nn_integral lborel (\<lambda>c. ?DA c *
    ennreal (norm (slp_center_average tau (\<lambda>x. phi x * ?B x) c - phi c * ?B c))))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_positive_l2_center_error_mass_decay[
          OF fourier_plancherel DA_l2 source_B_integrable source_B_l2])
  show "((\<lambda>tau. nn_integral lborel (\<lambda>c. ?DB c *
    ennreal (norm (slp_center_average tau (\<lambda>x. phi x * ?A x) c - phi c * ?A c))))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_positive_l2_center_error_mass_decay[
          OF fourier_plancherel DB_l2 source_A_integrable source_A_l2])
qed

theorem slp_natural_mixed_smooth_cross_error_decay:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes fourier_plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
  shows "let PL = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             PR = PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((((PL \<Otimes>\<^sub>M PL) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
               ((PR \<Otimes>\<^sub>M PR) \<Otimes>\<^sub>M lborel)) \<Otimes>\<^sub>M lborel);
             lp = (\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]);
             rp = (\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]);
             phase = (\<lambda>z. slp_mixed_branch_residual (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             A = slp_cauchy_transform lo q; B = slp_cauchy_transform ro qt;
             one = (\<lambda>_::slp_point. (1::complex));
             F = (\<lambda>T U h tau z. exp (\<i> * of_real (tau * phase z)) *
               slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U
                 (\<lambda>c. slp_center_average tau h c - h c) z)
    in eventually (\<lambda>tau. integrable MJ (F A B phi tau) \<and>
         integrable MJ (F A one (\<lambda>x. phi x * B x) tau) \<and>
         integrable MJ (F one B (\<lambda>x. phi x * A x) tau)) at_top \<and>
       ((\<lambda>tau. integral\<^sup>L MJ (F A B phi tau)) \<longlongrightarrow> 0) at_top \<and>
       ((\<lambda>tau. integral\<^sup>L MJ (F A one (\<lambda>x. phi x * B x) tau))
         \<longlongrightarrow> 0) at_top \<and>
       ((\<lambda>tau. integral\<^sup>L MJ (F one B (\<lambda>x. phi x * A x) tau))
         \<longlongrightarrow> 0) at_top"
proof -
  interpret hf: hormander_euclidean_l2_fourier_plancherel
    by standard (rule fourier_plancherel)
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?phase = "\<lambda>z. slp_mixed_branch_residual (snd z)
    (?lp (fst z)) (snd (fst (fst z))) (?rp (fst z)) (snd (snd (fst z)))"
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?F = "\<lambda>T U h tau z. exp (\<i> * of_real (tau * ?phase z)) *
    slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U
      (\<lambda>c. slp_center_average tau h c - h c) z"
  have q_measurable[measurable]: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have qt_measurable[measurable]: "qt \<in> borel_measurable lborel"
    using qt_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have A_measurable[measurable]: "?A \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper q_lp])
  have B_measurable[measurable]: "?B \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper qt_lp])
  have one_measurable: "?one \<in> borel_measurable lborel" by measurable
  have Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> X"
    using Q_outside by blast
  have p_at_least_one: "1 \<le> p" using p_lower by simp
  have Q_integrable: "integrable lborel Q"
    by (rule slp_bounded_supported_lp_integrable[
          OF p_at_least_one X_measurable X_bounded Q_lp Q_in])
  have phase_measurable[measurable]: "?phase \<in> borel_measurable ?MJ"
    using slp_natural_mixed_unit_integration_data[
      OF R_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp
        cutoff_bound C_nonnegative Q_integrable Q_support cutoff_support q_support qt_support,
      where n=n and m=m]
    by (auto simp only: Let_def)
  have phase_parameter: "(\<lambda>z. tau * ?phase z) \<in> borel_measurable ?MJ" for tau::real
    by measurable
  have error_data:
    "eventually (\<lambda>tau. integrable ?MJ (?F T U h tau)) at_top \<and>
      ((\<lambda>tau. integral\<^sup>L ?MJ (?F T U h tau)) \<longlongrightarrow> 0) at_top"
    if T_measurable: "T \<in> borel_measurable lborel"
      and U_measurable: "U \<in> borel_measurable lborel"
      and h_integrable: "integrable lborel h"
      and mass_decay: "((\<lambda>tau. nn_integral lborel (\<lambda>c.
        slp_mixed_center_density (2 * R) cutoff q qt
          (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c *
        ennreal (norm (slp_center_average tau h c - h c)))) \<longlongrightarrow> 0) at_top"
    for T U h
  proof -
    let ?E = "\<lambda>tau c. slp_center_average tau h c - h c"
    have h_measurable[measurable]: "h \<in> borel_measurable lborel"
      using h_integrable by measurable
    have E_measurable: "?E tau \<in> borel_measurable lborel" for tau
    proof -
      have average[measurable]: "slp_center_average tau h \<in> borel_measurable lborel"
        by (rule slp_center_average_measurable[OF h_integrable])
      show ?thesis by measurable
    qed
    have ordered_mass:
      "((\<lambda>tau. nn_integral lborel (\<lambda>c. ennreal (norm (?E tau c)) *
        slp_mixed_center_density (2 * R) cutoff q qt
          (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q c))
        \<longlongrightarrow> 0) at_top"
      using mass_decay by (simp only: mult.commute)
    note transfer = slp_natural_mixed_oscillatory_integral_tendsto_zero[
      where psi="\<lambda>tau z. tau * ?phase z",
      OF R_nonnegative cutoff_measurable q_measurable T_measurable
        qt_measurable U_measurable Q_measurable E_measurable
        Q_support cutoff_support q_support qt_support phase_parameter ordered_mass]
    show ?thesis using transfer by blast
  qed
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have source_A_integrable: "integrable lborel (\<lambda>x. phi x * ?A x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have source_B_integrable: "integrable lborel (\<lambda>x. phi x * ?B x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper qt_lp phi_test])
  have uniform: "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi at_top"
    by (rule hf.slp_center_average_smooth_uniform_limit[OF phi_test])
  have smooth_mass:
    "((\<lambda>tau. nn_integral lborel (\<lambda>c.
      slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>s. ennreal (norm (?A s))) (\<lambda>t. ennreal (norm (?B t))) n m Q c *
      ennreal (norm (slp_center_average tau phi c - phi c)))) \<longlongrightarrow> 0) at_top"
    by (rule slp_mixed_center_density_cauchy_terminal_smooth_error_mass_decay[
          OF R_nonnegative p_lower p_upper X_measurable X_bounded
            cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound C_nonnegative
            cutoff_support q_support qt_support phi_integrable uniform,
          where left_orientation=lo and right_orientation=ro
            and left_order=n and right_order=m])
       (use assms in auto)
  note cross_mass = slp_natural_mixed_cauchy_cross_error_mass_decay[
    OF fourier_plancherel R_nonnegative C_nonnegative p_lower p_upper X_measurable
      X_bounded cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
      cutoff_support q_support qt_support phi_test, where n=n and m=m and lo=lo and ro=ro]
  have smooth:
    "eventually (\<lambda>tau. integrable ?MJ (?F ?A ?B phi tau)) at_top \<and>
      ((\<lambda>tau. integral\<^sup>L ?MJ (?F ?A ?B phi tau)) \<longlongrightarrow> 0) at_top"
    by (rule error_data[OF A_measurable B_measurable phi_integrable smooth_mass])
  have left_mass:
    "((\<lambda>tau. nn_integral lborel (\<lambda>c.
      slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>s. ennreal (norm (?A s))) (\<lambda>t. ennreal (norm (?one t))) n m Q c *
      ennreal (norm (slp_center_average tau (\<lambda>x. phi x * ?B x) c - phi c * ?B c))))
      \<longlongrightarrow> 0) at_top"
    using cross_mass(1) by simp
  have right_mass:
    "((\<lambda>tau. nn_integral lborel (\<lambda>c.
      slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>s. ennreal (norm (?one s))) (\<lambda>t. ennreal (norm (?B t))) n m Q c *
      ennreal (norm (slp_center_average tau (\<lambda>x. phi x * ?A x) c - phi c * ?A c))))
      \<longlongrightarrow> 0) at_top"
    using cross_mass(2) by simp
  have left:
    "eventually (\<lambda>tau. integrable ?MJ (?F ?A ?one (\<lambda>x. phi x * ?B x) tau)) at_top \<and>
      ((\<lambda>tau. integral\<^sup>L ?MJ (?F ?A ?one (\<lambda>x. phi x * ?B x) tau))
        \<longlongrightarrow> 0) at_top"
    by (rule error_data[OF A_measurable one_measurable source_B_integrable left_mass])
  have right:
    "eventually (\<lambda>tau. integrable ?MJ (?F ?one ?B (\<lambda>x. phi x * ?A x) tau)) at_top \<and>
      ((\<lambda>tau. integral\<^sup>L ?MJ (?F ?one ?B (\<lambda>x. phi x * ?A x) tau))
        \<longlongrightarrow> 0) at_top"
    by (rule error_data[OF one_measurable B_measurable source_A_integrable right_mass])
  show ?thesis using smooth left right by (auto simp: Let_def eventually_conj_iff)
qed

end

end
