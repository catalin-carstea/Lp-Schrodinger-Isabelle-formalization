theory Inverse_Schrodinger_Lp_Natural_Mixed_Raw_Amplitudes
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Product_Error_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Center_Support_Mass"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Bounded_Support_Lp_Norm"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Natural mixed center densities with unit center weight\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_mixed_total_density_masses:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field and lo ro :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
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
  shows "let A = slp_cauchy_transform lo q;
             B = slp_cauchy_transform ro qt;
             D = (\<lambda>T U::slp_scalar_field. slp_mixed_center_density (2 * R) cutoff q qt
               (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q)
    in nn_integral lborel (D A B) < top_class.top \<and>
       nn_integral lborel (D A (\<lambda>_. 1)) < top_class.top \<and>
       nn_integral lborel (D (\<lambda>_. 1) B) < top_class.top \<and>
       nn_integral lborel (D (\<lambda>_. 1) (\<lambda>_. 1)) < top_class.top"
proof -
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?D = "\<lambda>T U::slp_scalar_field. slp_mixed_center_density (2 * R) cutoff q qt
    (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q"
  let ?radius = "R + (real (Suc n) + real (Suc m)) * (2 * R)"
  let ?S = "cball (0::slp_point) ?radius"
  let ?indicator = "slp_restrict_field ?S ?one"
  have radius_nonnegative: "0 \<le> 2 * R" using R_nonnegative by simp
  have two_positive: "0 < (2::real)" by simp
  have two_lower: "1 < (2::real)" by simp
  have conjugate: "1 / (2::real) + 1 / 2 = 1" by simp
  have S_measurable: "?S \<in> sets lborel" by simp
  have S_bounded: "bounded ?S" by simp
  have indicator_l2: "aim_complex_lp_on_plane 2 ?indicator"
    by (rule slp_complex_indicator_lp_norm(1)[OF two_positive S_measurable S_bounded])
  have density_outside: "?D T U c = 0" if outside: "c \<notin> ?S" for T U c
  proof -
    have far: "?radius < norm c" using outside by simp
    show ?thesis
      by (rule slp_mixed_center_density_outside[OF radius_nonnegative Q_support far])
  qed
  have mass_of_l2: "nn_integral lborel F < top_class.top"
    if F_l2: "slp_positive_ennreal_lp_on_plane 2 F"
      and F_outside: "\<And>c. c \<notin> ?S \<Longrightarrow> F c = 0"
    for F :: "slp_point \<Rightarrow> ennreal"
  proof -
    have pairing: "nn_integral lborel (\<lambda>c. F c * ennreal (norm (?indicator c))) < top_class.top"
      by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[
            OF two_lower two_lower conjugate F_l2 indicator_l2])
    have pointwise: "F c * ennreal (norm (?indicator c)) = F c" for c
      by (cases "c \<in> ?S") (simp_all add: slp_restrict_field_def F_outside)
    show ?thesis using pairing by (simp only: pointwise)
  qed
  have DA_l2: "slp_positive_ennreal_lp_on_plane 2 (?D ?A ?one)"
    using slp_natural_mixed_cauchy_cross_density_l2(1)[
      OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
        cutoff_support q_support qt_support, where n=n and m=m and lo=lo]
    by simp
  have DB_l2: "slp_positive_ennreal_lp_on_plane 2 (?D ?one ?B)"
    using slp_natural_mixed_cauchy_cross_density_l2(2)[
      OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
        cutoff_support q_support qt_support, where n=n and m=m and ro=ro]
    by simp
  have left_mass: "nn_integral lborel (?D ?A ?one) < top_class.top"
    by (rule mass_of_l2[OF DA_l2]) (erule density_outside)
  have right_mass: "nn_integral lborel (?D ?one ?B) < top_class.top"
    by (rule mass_of_l2[OF DB_l2]) (erule density_outside)
  have both_mass: "nn_integral lborel (?D ?A ?B) < top_class.top"
    by (rule slp_mixed_center_density_cauchy_terminal_all_orders_mass_finite[
          OF R_nonnegative p_lower p_upper X_measurable X_bounded cutoff_measurable
            q_lp qt_lp Q_lp Q_outside cutoff_bound C_nonnegative
            cutoff_support q_support qt_support])
  have p_at_least_one: "1 \<le> p" using p_lower by simp
  have Q_in: "x \<in> X" if "Q x \<noteq> 0" for x using that Q_outside[of x] by blast
  have Q_integrable: "integrable lborel Q"
    by (rule slp_bounded_supported_lp_integrable[
          OF p_at_least_one X_measurable X_bounded Q_lp]) (erule Q_in)
  have unit_mass: "nn_integral lborel (?D ?one ?one) < top_class.top"
    using slp_mixed_center_density_unweighted_mass_finite[
      OF radius_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp
        cutoff_bound C_nonnegative Q_integrable, where left_order=n and right_order=m]
    by simp
  show ?thesis using both_mass left_mass right_mass unit_mass by (auto simp only: Let_def)
qed


section \<open>Four raw natural mixed amplitudes are integrable\<close>

theorem slp_natural_mixed_raw_amplitudes_integrable:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field and lo ro :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
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
  shows "let PL = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             PR = PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((((PL \<Otimes>\<^sub>M PL) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
               ((PR \<Otimes>\<^sub>M PR) \<Otimes>\<^sub>M lborel)) \<Otimes>\<^sub>M lborel);
             A = slp_cauchy_transform lo q;
             B = slp_cauchy_transform ro qt;
             W = (\<lambda>T U. slp_natural_mixed_weighted_amplitude n m Q cutoff
               q T qt U (\<lambda>_. 1))
    in integrable MJ (W A B) \<and> integrable MJ (W A (\<lambda>_. 1)) \<and>
       integrable MJ (W (\<lambda>_. 1) B) \<and> integrable MJ (W (\<lambda>_. 1) (\<lambda>_. 1))"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?W = "\<lambda>T U. slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U ?one"
  let ?D = "\<lambda>T U::slp_scalar_field. slp_mixed_center_density (2 * R) cutoff q qt
    (\<lambda>s. ennreal (norm (T s))) (\<lambda>t. ennreal (norm (U t))) n m Q"
  have q_measurable[measurable]: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have qt_measurable[measurable]: "qt \<in> borel_measurable lborel"
    using qt_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have A_measurable: "?A \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper q_lp])
  have B_measurable: "?B \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper qt_lp])
  have one_measurable: "?one \<in> borel_measurable lborel" by measurable
  have component_integrable: "integrable ?MJ (?W T U)"
    if T: "T \<in> borel_measurable lborel" and U: "U \<in> borel_measurable lborel"
      and mass: "nn_integral lborel (?D T U) < top_class.top" for T U
    by (rule slp_natural_mixed_weighted_amplitude_integrable_from_density[
          OF R_nonnegative cutoff_measurable q_measurable T qt_measurable U
            Q_measurable one_measurable Q_support cutoff_support q_support qt_support])
      (use mass in simp_all)
  note masses = slp_natural_mixed_total_density_masses[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
      cutoff_support q_support qt_support, where n=n and m=m and lo=lo and ro=ro]
  have both: "integrable ?MJ (?W ?A ?B)"
    by (rule component_integrable[OF A_measurable B_measurable])
      (use masses in \<open>auto simp: Let_def\<close>)
  have left: "integrable ?MJ (?W ?A ?one)"
    by (rule component_integrable[OF A_measurable one_measurable])
      (use masses in \<open>auto simp: Let_def\<close>)
  have right: "integrable ?MJ (?W ?one ?B)"
    by (rule component_integrable[OF one_measurable B_measurable])
      (use masses in \<open>auto simp: Let_def\<close>)
  have unit: "integrable ?MJ (?W ?one ?one)"
    by (rule component_integrable[OF one_measurable one_measurable])
      (use masses in \<open>auto simp: Let_def\<close>)
  show ?thesis using both left right unit by (auto simp only: Let_def)
qed


end

end
