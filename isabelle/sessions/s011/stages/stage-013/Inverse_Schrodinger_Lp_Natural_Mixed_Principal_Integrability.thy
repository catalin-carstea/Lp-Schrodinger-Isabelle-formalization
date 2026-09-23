theory Inverse_Schrodinger_Lp_Natural_Mixed_Principal_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Amplitude_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_One_Terminal"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Density_Cauchy_Terminal_Mass_Finite"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Test_Cauchy_Product_L2"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Test_Two_Cauchy_Product_Half_HLS"
begin

hide_const (open) Commutative_Ring.norm

section \<open>All-natural principal mixed amplitude integrability\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_mixed_cauchy_cross_density_l2:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
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
  shows left_cross:
    "slp_positive_ennreal_lp_on_plane 2
      (slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>s. ennreal (norm (slp_cauchy_transform lo q s))) (\<lambda>_. 1) n m Q)"
    and right_cross:
    "slp_positive_ennreal_lp_on_plane 2
      (slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>_. 1) (\<lambda>t. ennreal (norm (slp_cauchy_transform ro qt t))) n m Q)"
proof -
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?DA = "slp_mixed_center_density (2 * R) cutoff q qt
    (\<lambda>s. ennreal (norm (?A s))) (\<lambda>_. 1) n m Q"
  let ?DB = "slp_mixed_center_density (2 * R) cutoff q qt
    (\<lambda>_. 1) (\<lambda>t. ennreal (norm (?B t))) n m Q"
  let ?MA = "slp_mixed_center_density (2 * R) cutoff q qt
    (slp_positive_terminal_riesz_weight (2 * R) q) (\<lambda>_. 1) n m Q"
  let ?MB = "slp_mixed_center_density (2 * R) cutoff q qt
    (\<lambda>_. 1) (slp_positive_terminal_riesz_weight (2 * R) qt) n m Q"
  have radius_nonnegative: "0 \<le> 2 * R" using R_nonnegative by simp
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
  have density_measurable:
    "slp_mixed_center_density (2 * R) cutoff q qt F G n m Q \<in> borel_measurable lborel"
    if F: "F \<in> borel_measurable lborel" and G: "G \<in> borel_measurable lborel"
    for F G :: "slp_point \<Rightarrow> ennreal"
    by (rule slp_mixed_center_density_measurable[
          OF cutoff_measurable q_measurable qt_measurable F G Q_measurable])
  have DA_measurable: "?DA \<in> borel_measurable lborel"
    by (rule density_measurable; measurable)
  have DB_measurable: "?DB \<in> borel_measurable lborel"
    by (rule density_measurable; measurable)
  have q_radius:
    "\<And>x y::slp_point. \<lbrakk>cutoff x \<noteq> 0; q y \<noteq> 0\<rbrakk> \<Longrightarrow> norm (x-y) \<le> 2 * R"
    by (rule slp_norm_sub_le_two_radius[OF R_nonnegative cutoff_support q_support])
  have qt_radius:
    "\<And>x y::slp_point. \<lbrakk>cutoff x \<noteq> 0; qt y \<noteq> 0\<rbrakk> \<Longrightarrow> norm (x-y) \<le> 2 * R"
    by (rule slp_norm_sub_le_two_radius[OF R_nonnegative cutoff_support qt_support])
  have A_bound:
    "\<And>x. ennreal (norm (cutoff x)) * ennreal (norm (?A x)) \<le>
      ennreal (norm (cutoff x)) * slp_positive_terminal_riesz_weight (2 * R) q x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF q_radius])
  have B_bound:
    "\<And>x. ennreal (norm (cutoff x)) * ennreal (norm (?B x)) \<le>
      ennreal (norm (cutoff x)) * slp_positive_terminal_riesz_weight (2 * R) qt x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF qt_radius])
  have DA_le: "?DA c \<le> ?MA c" for c
    by (rule slp_mixed_center_density_cutoff_terminal_mono) (use A_bound in simp_all)
  have DB_le: "?DB c \<le> ?MB c" for c
    by (rule slp_mixed_center_density_cutoff_terminal_mono) (use B_bound in simp_all)
  have MA_L2: "slp_positive_ennreal_lp_on_plane 2 ?MA"
    by (rule slp_mixed_center_density_all_orders_membership_clauses(4)[
          OF radius_nonnegative p_lower p_upper X_measurable X_bounded
            cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound C_nonnegative])
  have MB_L2: "slp_positive_ennreal_lp_on_plane 2 ?MB"
    by (rule slp_mixed_center_density_all_orders_membership_clauses(5)[
          OF radius_nonnegative p_lower p_upper X_measurable X_bounded
            cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound C_nonnegative])
  show "slp_positive_ennreal_lp_on_plane 2 ?DA"
    by (rule slp_positive_ennreal_lp_mono_AE[OF _ MA_L2 DA_measurable])
      (use DA_le in simp_all)
  show "slp_positive_ennreal_lp_on_plane 2 ?DB"
    by (rule slp_positive_ennreal_lp_mono_AE[OF _ MB_L2 DB_measurable])
      (use DB_le in simp_all)
qed

theorem slp_natural_mixed_principal_density_masses:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
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
  shows "let A = slp_cauchy_transform lo q;
             B = slp_cauchy_transform ro qt;
             D = (\<lambda>T U::slp_scalar_field. slp_mixed_center_density (2 * R) cutoff q qt
               (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q)
    in nn_integral lborel (\<lambda>c. ennreal (norm (phi c)) * D A B c) < top_class.top \<and>
       nn_integral lborel (\<lambda>c. ennreal (norm (phi c * B c)) * D A (\<lambda>_. 1) c) < top_class.top \<and>
       nn_integral lborel (\<lambda>c. ennreal (norm (phi c * A c)) * D (\<lambda>_. 1) B c) < top_class.top \<and>
       nn_integral lborel (\<lambda>c. ennreal (norm (phi c * (A c * B c))) *
         D (\<lambda>_. 1) (\<lambda>_. 1) c) < top_class.top"
proof -
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?D = "\<lambda>T U::slp_scalar_field. slp_mixed_center_density (2 * R) cutoff q qt
    (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q"
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
  have DAB_measurable: "?D ?A ?B \<in> borel_measurable lborel"
    by (rule slp_mixed_center_density_measurable[
          OF cutoff_measurable q_measurable qt_measurable _ _ Q_measurable]; measurable)
  have DAB_finite: "nn_integral lborel (?D ?A ?B) < top_class.top"
    by (rule slp_mixed_center_density_cauchy_terminal_all_orders_mass_finite[
          OF R_nonnegative p_lower p_upper X_measurable X_bounded
            cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound C_nonnegative
            cutoff_support q_support qt_support])
  have phi_bounded: "bounded (range phi)"
    by (rule slp_test_function_integrable_bounded(2)[OF phi_test])
  obtain K where phi_bound: "\<And>x. norm (phi x) \<le> K"
    using phi_bounded unfolding bounded_iff by auto
  have tt_bound:
    "nn_integral lborel (\<lambda>c. ennreal (norm (phi c)) * ?D ?A ?B c) \<le>
      nn_integral lborel (\<lambda>c. ennreal K * ?D ?A ?B c)"
  proof (rule nn_integral_mono)
    fix c :: slp_point
    assume "c \<in> space (lborel :: slp_point measure)"
    show "ennreal (norm (phi c)) * ?D ?A ?B c \<le> ennreal K * ?D ?A ?B c"
      by (rule mult_right_mono[OF ennreal_leI[OF phi_bound]]) simp
  qed
  have tt_constant:
    "nn_integral lborel (\<lambda>c. ennreal K * ?D ?A ?B c) =
      ennreal K * nn_integral lborel (?D ?A ?B)"
    by (rule nn_integral_cmult[OF DAB_measurable])
  have tt_finite:
    "nn_integral lborel (\<lambda>c. ennreal (norm (phi c)) * ?D ?A ?B c) < top_class.top"
    by (rule le_less_trans[OF tt_bound])
      (use DAB_finite tt_constant in \<open>simp add: ennreal_mult_less_top\<close>)
  note left_cross = slp_natural_mixed_cauchy_cross_density_l2(1)[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
      cutoff_support q_support qt_support, where n=n and m=m and lo=lo]
  note right_cross = slp_natural_mixed_cauchy_cross_density_l2(2)[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
      cutoff_support q_support qt_support, where n=n and m=m and ro=ro]
  have phiB_L2: "aim_complex_lp_on_plane 2 (\<lambda>c. phi c * ?B c)"
    by (rule slp_test_cauchy_product_l2[OF p_lower p_upper qt_lp phi_test])
  have phiA_L2: "aim_complex_lp_on_plane 2 (\<lambda>c. phi c * ?A c)"
    by (rule slp_test_cauchy_product_l2[OF p_lower p_upper q_lp phi_test])
  have DA_L2: "slp_positive_ennreal_lp_on_plane 2 (?D ?A ?one)"
    using left_cross by simp
  have DB_L2: "slp_positive_ennreal_lp_on_plane 2 (?D ?one ?B)"
    using right_cross by simp
  have lc_raw:
    "nn_integral lborel (\<lambda>c. ?D ?A ?one c * ennreal (norm (phi c * ?B c))) < top_class.top"
    by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[OF _ _ _ DA_L2 phiB_L2]) simp_all
  have rc_raw:
    "nn_integral lborel (\<lambda>c. ?D ?one ?B c * ennreal (norm (phi c * ?A c))) < top_class.top"
    by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[OF _ _ _ DB_L2 phiA_L2]) simp_all
  have lc_finite:
    "nn_integral lborel (\<lambda>c. ennreal (norm (phi c * ?B c)) * ?D ?A ?one c) < top_class.top"
    using lc_raw by (simp add: mult.commute)
  have rc_finite:
    "nn_integral lborel (\<lambda>c. ennreal (norm (phi c * ?A c)) * ?D ?one ?B c) < top_class.top"
    using rc_raw by (simp add: mult.commute)
  let ?r = "aim_hls_target_exponent p / 2"
  let ?s = "slp_holder_conjugate ?r"
  have r_lower: "1 < ?r"
    using slp_hls_target_exponent_above_two[OF p_lower p_upper] by linarith
  have s_lower: "1 < ?s"
    by (rule slp_holder_conjugate_lower_and_pair(1)[OF r_lower])
  have pair: "1 / ?s + 1 / ?r = 1"
    by (rule slp_holder_conjugate_lower_and_pair(2)[OF r_lower])
  have radius_nonnegative: "0 \<le> 2 * R" using R_nonnegative by simp
  have D11_Ls: "slp_positive_ennreal_lp_on_plane ?s (?D ?one ?one)"
    using slp_mixed_center_density_unit_terminal_all_orders_finite_target[
      OF radius_nonnegative p_lower p_upper s_lower X_measurable X_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound C_nonnegative,
      of n m]
    by simp
  have phiAB_Lr: "aim_complex_lp_on_plane ?r (\<lambda>c. phi c * (?A c * ?B c))"
    by (rule slp_test_two_cauchy_product_half_hls_target_lp[
          OF p_lower p_upper q_lp qt_lp phi_test])
  have uu_raw:
    "nn_integral lborel (\<lambda>c. ?D ?one ?one c *
      ennreal (norm (phi c * (?A c * ?B c)))) < top_class.top"
    by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[
          OF s_lower r_lower pair D11_Ls phiAB_Lr])
  have uu_finite:
    "nn_integral lborel (\<lambda>c. ennreal (norm (phi c * (?A c * ?B c))) *
      ?D ?one ?one c) < top_class.top"
    using uu_raw by (simp add: mult.commute)
  show ?thesis
    unfolding Let_def
    using tt_finite lc_finite rc_finite uu_finite by blast
qed

theorem slp_natural_mixed_principal_components_integrable:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
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
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "let A = slp_cauchy_transform lo q;
             B = slp_cauchy_transform ro qt;
             MJ = (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
                 (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
               \<Otimes>\<^sub>M
               (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
                 (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
               \<Otimes>\<^sub>M lborel);
             W = (\<lambda>T U H. slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H)
    in integrable MJ (W A B phi) \<and>
       integrable MJ (W A (\<lambda>_. 1) (\<lambda>c. phi c * B c)) \<and>
       integrable MJ (W (\<lambda>_. 1) B (\<lambda>c. phi c * A c)) \<and>
       integrable MJ (W (\<lambda>_. 1) (\<lambda>_. 1) (\<lambda>c. phi c * (A c * B c)))"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?W = "\<lambda>T U H. slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H"
  let ?D = "\<lambda>T U::slp_scalar_field. slp_mixed_center_density (2 * R) cutoff q qt
    (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q"
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
  have phi_measurable[measurable]: "phi \<in> borel_measurable lborel"
    using slp_test_function_integrable_bounded(1)[OF phi_test] by measurable
  have one_measurable: "?one \<in> borel_measurable lborel" by measurable
  have phiB_measurable: "(\<lambda>c. phi c * ?B c) \<in> borel_measurable lborel" by measurable
  have phiA_measurable: "(\<lambda>c. phi c * ?A c) \<in> borel_measurable lborel" by measurable
  have phiAB_measurable: "(\<lambda>c. phi c * (?A c * ?B c)) \<in> borel_measurable lborel"
    by measurable
  have component_integrable: "integrable ?MJ (?W T U H)"
    if T: "T \<in> borel_measurable lborel"
      and U: "U \<in> borel_measurable lborel"
      and H: "H \<in> borel_measurable lborel"
      and mass: "nn_integral lborel (\<lambda>c. ennreal (norm (H c)) * ?D T U c) < top_class.top"
    for T U H :: slp_scalar_field
    by (rule slp_natural_mixed_weighted_amplitude_integrable_from_density[
          OF R_nonnegative cutoff_measurable q_measurable T qt_measurable U
            Q_measurable H Q_support cutoff_support q_support qt_support mass])
  note masses = slp_natural_mixed_principal_density_masses[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound cutoff_support
      q_support qt_support phi_test, where n=n and m=m and lo=lo and ro=ro]
  have tt: "integrable ?MJ (?W ?A ?B phi)"
    by (rule component_integrable[OF A_measurable B_measurable phi_measurable])
      (use masses in \<open>auto simp only: Let_def\<close>)
  have lc: "integrable ?MJ (?W ?A ?one (\<lambda>c. phi c * ?B c))"
    by (rule component_integrable[OF A_measurable one_measurable phiB_measurable])
      (use masses in \<open>auto simp only: Let_def\<close>)
  have rc: "integrable ?MJ (?W ?one ?B (\<lambda>c. phi c * ?A c))"
    by (rule component_integrable[OF one_measurable B_measurable phiA_measurable])
      (use masses in \<open>auto simp only: Let_def\<close>)
  have uu: "integrable ?MJ (?W ?one ?one (\<lambda>c. phi c * (?A c * ?B c)))"
    by (rule component_integrable[OF one_measurable one_measurable phiAB_measurable])
      (use masses in \<open>auto simp only: Let_def\<close>)
  show ?thesis unfolding Let_def using tt lc rc uu by blast
qed

end

end
