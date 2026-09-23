theory Inverse_Schrodinger_Lp_Natural_Mixed_Preaverage_Integration
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Raw_Amplitudes"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Natural preaverage terminal factors and Fubini\<close>

theorem slp_natural_mixed_amplitude_terminal_factor:
  fixes n m :: nat and Q cutoff q qt T U H :: slp_scalar_field
  shows "slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H z =
    (let lp = map (\<lambda>j. (fst (fst (fst (fst z))) j,
                              snd (fst (fst (fst z))) j)) [0..<n];
         rp = map (\<lambda>j. (fst (fst (snd (fst z))) j,
                              snd (fst (snd (fst z))) j)) [0..<m];
         s = snd (fst (fst z)); t = snd (snd (fst z));
         center = slp_mixed_branch_center (snd z) lp s rp t
     in slp_natural_mixed_weighted_amplitude n m Q cutoff q (\<lambda>_. 1)
          qt (\<lambda>_. 1) (\<lambda>_. 1) z * T s * U t * H center)"
proof -
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?s = "snd (fst (fst z))"
  let ?t = "snd (snd (fst z))"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  have left_factor:
    "slp_left_branch_complex_kernel_list cutoff q T (?lp (fst z)) (snd z) ?s =
      T ?s * slp_left_branch_complex_kernel_list cutoff q ?one
        (?lp (fst z)) (snd z) ?s"
    by (rule slp_left_branch_list_terminal_factor)
  have right_factor:
    "slp_left_branch_complex_kernel_list (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (qt x)) (\<lambda>x. cnj (U x)) (?rp (fst z)) (snd z) ?t =
      cnj (U ?t) * slp_left_branch_complex_kernel_list (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (qt x)) ?one (?rp (fst z)) (snd z) ?t"
    by (rule slp_left_branch_list_terminal_factor)
  show ?thesis
    unfolding slp_natural_mixed_weighted_amplitude_def Let_def
    by (simp add: left_factor right_factor algebra_simps)
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_mixed_fixed_preaverage_integrable:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and tau :: real and y :: slp_point
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
             lp = (\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]);
             rp = (\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]);
             center = (\<lambda>z. slp_mixed_branch_center (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             phase = (\<lambda>z. slp_mixed_branch_residual (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             A = slp_cauchy_transform lo q;
             B = slp_cauchy_transform ro qt;
             a = slp_natural_mixed_weighted_amplitude n m Q cutoff q (\<lambda>_. 1)
               qt (\<lambda>_. 1) (\<lambda>_. 1);
             F = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_center_kernel tau (center z) y *
               (A (snd (fst (fst z))) - A y) * (B (snd (snd (fst z))) - B y))
    in integrable MJ F"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?N = "?BL \<Otimes>\<^sub>M ?BR"
  let ?MJ = "?N \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MY = "?MJ \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?s = "\<lambda>z. snd (fst (fst z))"
  let ?t = "\<lambda>z. snd (snd (fst z))"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?phase = "\<lambda>z. slp_mixed_branch_residual (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?W = "\<lambda>T U H. slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H"
  let ?a = "?W ?one ?one ?one"
  let ?e = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z))"
  let ?F = "\<lambda>z. ?e z * ?a z * slp_center_kernel tau (?center z) y *
    (?A (?s z) - ?A y) * (?B (?t z) - ?B y)"
  let ?D = "\<lambda>z. ?W ?A ?B ?one z - ?B y * ?W ?A ?one ?one z -
    ?A y * ?W ?one ?B ?one z + (?A y * ?B y) * ?a z"
  have p_at_least_one: "1 \<le> p" using p_lower by simp
  have Q_in: "x \<in> X" if "Q x \<noteq> 0" for x using that Q_outside[of x] by blast
  have Q_integrable: "integrable lborel Q"
    by (rule slp_bounded_supported_lp_integrable[
          OF p_at_least_one X_measurable X_bounded Q_lp]) (erule Q_in)
  note data = slp_natural_mixed_unit_integration_data[
    OF R_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp cutoff_bound
      C_nonnegative Q_integrable Q_support cutoff_support q_support qt_support,
    where n=n and m=m]
  have center_map: "?center \<in> measurable ?MJ lborel"
    using data by (auto simp only: Let_def)
  have center_borel[measurable]: "?center \<in> borel_measurable ?MJ"
    using center_map by (simp only: measurable_lborel1)
  have phase_borel[measurable]: "?phase \<in> borel_measurable ?MJ"
    using data by (auto simp only: Let_def)
  note raw = slp_natural_mixed_raw_amplitudes_integrable[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
      cutoff_support q_support qt_support, where n=n and m=m and lo=lo and ro=ro]
  have raw0: "integrable ?MJ (?W ?A ?B ?one)"
    using raw by (auto simp only: Let_def)
  have raw1: "integrable ?MJ (?W ?A ?one ?one)"
    using raw by (auto simp only: Let_def)
  have raw2: "integrable ?MJ (?W ?one ?B ?one)"
    using raw by (auto simp only: Let_def)
  have raw3: "integrable ?MJ ?a"
    using raw by (auto simp only: Let_def)
  have raw_factor: "?W T U ?one z = ?a z * T (?s z) * U (?t z)" for T U z
    using slp_natural_mixed_amplitude_terminal_factor[
      where n=n and m=m and Q=Q and cutoff=cutoff and q=q and qt=qt
        and T=T and U=U and H="?one" and z=z]
    by (simp only: Let_def mult_1_right)
  have D_integrable: "integrable ?MJ ?D"
    by (intro Bochner_Integration.integrable_add Bochner_Integration.integrable_diff
        Bochner_Integration.integrable_mult_right raw0 raw1 raw2 raw3)
  have D_borel[measurable]: "?D \<in> borel_measurable ?MJ"
    using D_integrable by measurable
  have center_nth[measurable]: "(\<lambda>z. ?center z $ i) \<in> borel_measurable ?MJ"
    for i :: 2
    using measurable_comp[OF center_borel borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have kernel_borel[measurable]:
    "(\<lambda>z. slp_center_kernel tau (?center z) y) \<in> borel_measurable ?MJ"
    unfolding slp_center_kernel_def slp_center_phase_def by measurable
  have phased: "integrable ?MJ (\<lambda>z. ?e z * slp_center_kernel tau (?center z) y * ?D z)"
  proof (rule Bochner_Integration.integrable_bound[OF D_integrable])
    show "(\<lambda>z. ?e z * slp_center_kernel tau (?center z) y * ?D z) \<in> borel_measurable ?MJ"
      by measurable
    show "AE z in ?MJ. norm (?e z * slp_center_kernel tau (?center z) y * ?D z) \<le> norm (?D z)"
      by (simp add: norm_mult norm_exp_i_times)
  qed
  have expansion:
    "?F z = ?e z * slp_center_kernel tau (?center z) y * ?D z" for z
  proof -
    note f0 = raw_factor[of ?A ?B z]
    note f1 = raw_factor[of ?A ?one z]
    note f2 = raw_factor[of ?one ?B z]
    show ?thesis by (simp only: f0 f1 f2; simp add: algebra_simps)
  qed
  show ?thesis unfolding Let_def using phased by (simp only: expansion)
qed

theorem slp_natural_mixed_preaverage_bracket_fubini:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and tau :: real and phi :: slp_scalar_field
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
    and phi_test: "slp_test_function_on UNIV phi"
  shows "let PL = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             PR = PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((((PL \<Otimes>\<^sub>M PL) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
               ((PR \<Otimes>\<^sub>M PR) \<Otimes>\<^sub>M lborel)) \<Otimes>\<^sub>M lborel);
             lp = (\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]);
             rp = (\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]);
             center = (\<lambda>z. slp_mixed_branch_center (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             phase = (\<lambda>z. slp_mixed_branch_residual (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             A = slp_cauchy_transform lo q;
             B = slp_cauchy_transform ro qt;
             a = slp_natural_mixed_weighted_amplitude n m Q cutoff q (\<lambda>_. 1)
               qt (\<lambda>_. 1) (\<lambda>_. 1);
             F = (\<lambda>z y. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_center_kernel tau (center z) y *
               (A (snd (fst (fst z))) - A y) * (B (snd (snd (fst z))) - B y));
             G = (\<lambda>z y. F z y * phi y);
             I = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_mixed_center_average_bracket tau phi A B (center z)
                 (snd (fst (fst z))) (snd (snd (fst z))))
    in (\<forall>y. integrable MJ (\<lambda>z. F z y)) \<and>
       integrable (MJ \<Otimes>\<^sub>M lborel) (case_prod G) \<and>
       integrable MJ I \<and>
       integrable lborel (\<lambda>y. integral\<^sup>L MJ (\<lambda>z. G z y)) \<and>
       of_real (tau / pi) * integral\<^sup>L lborel
         (\<lambda>y. integral\<^sup>L MJ (\<lambda>z. G z y)) = integral\<^sup>L MJ I"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?N = "?BL \<Otimes>\<^sub>M ?BR"
  let ?MJ = "?N \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MY = "?MJ \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?s = "\<lambda>z. snd (fst (fst z))"
  let ?t = "\<lambda>z. snd (snd (fst z))"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?phase = "\<lambda>z. slp_mixed_branch_residual (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?W = "\<lambda>T U H. slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H"
  let ?a = "?W ?one ?one ?one"
  let ?e = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z))"
  let ?F = "\<lambda>z y. ?e z * ?a z * slp_center_kernel tau (?center z) y *
    (?A (?s z) - ?A y) * (?B (?t z) - ?B y)"
  let ?G = "\<lambda>z y. ?F z y * phi y"
  let ?I = "\<lambda>z. ?e z * ?a z *
    slp_mixed_center_average_bracket tau phi ?A ?B (?center z) (?s z) (?t z)"
  let ?scale = "of_real (tau / pi) :: complex"
  let ?Tensor = "\<lambda>w h z y. ?e z * w z * slp_center_kernel tau (?center z) y * h y"
  have p_at_least_one: "1 \<le> p" using p_lower by simp
  have Q_in: "x \<in> X" if "Q x \<noteq> 0" for x using that Q_outside[of x] by blast
  have Q_integrable: "integrable lborel Q"
    by (rule slp_bounded_supported_lp_integrable[
          OF p_at_least_one X_measurable X_bounded Q_lp]) (erule Q_in)
  note data = slp_natural_mixed_unit_integration_data[
    OF R_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp cutoff_bound
      C_nonnegative Q_integrable Q_support cutoff_support q_support qt_support,
    where n=n and m=m]
  have center_map: "?center \<in> measurable ?MJ lborel"
    using data by (auto simp only: Let_def)
  have center_borel[measurable]: "?center \<in> borel_measurable ?MJ"
    using center_map by (simp only: measurable_lborel1)
  have phase_borel[measurable]: "?phase \<in> borel_measurable ?MJ"
    using data by (auto simp only: Let_def)
  note raw = slp_natural_mixed_raw_amplitudes_integrable[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
      cutoff_support q_support qt_support, where n=n and m=m and lo=lo and ro=ro]
  have raw0: "integrable ?MJ (?W ?A ?B ?one)"
    using raw by (auto simp only: Let_def)
  have raw1: "integrable ?MJ (?W ?A ?one ?one)"
    using raw by (auto simp only: Let_def)
  have raw2: "integrable ?MJ (?W ?one ?B ?one)"
    using raw by (auto simp only: Let_def)
  have raw3: "integrable ?MJ ?a"
    using raw by (auto simp only: Let_def)
  have raw_factor: "?W T U ?one z = ?a z * T (?s z) * U (?t z)" for T U z
    using slp_natural_mixed_amplitude_terminal_factor[
      where n=n and m=m and Q=Q and cutoff=cutoff and q=q and qt=qt
        and T=T and U=U and H="?one" and z=z]
    by (simp only: Let_def mult_1_right)
  have phi0: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi1: "integrable lborel (\<lambda>y. phi y * ?B y)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper qt_lp phi_test])
  have phi2: "integrable lborel (\<lambda>y. phi y * ?A y)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have phi3: "integrable lborel (\<lambda>y. phi y * (?A y * ?B y))"
    by (rule slp_test_two_cauchy_product_integrable[OF p_lower p_upper q_lp qt_lp phi_test])
  have center_lift: "(\<lambda>zy. ?center (fst zy)) \<in> borel_measurable ?MY"
    by measurable
  have target_lift: "snd \<in> borel_measurable ?MY" by measurable
  have center_nth[measurable]:
    "(\<lambda>zy. ?center (fst zy) $ i) \<in> borel_measurable ?MY" for i :: 2
    using measurable_comp[OF center_lift borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have target_nth[measurable]:
    "(\<lambda>zy. snd zy $ i) \<in> borel_measurable ?MY" for i :: 2
    using measurable_comp[OF target_lift borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have kernel_joint_borel[measurable]:
    "(\<lambda>zy. slp_center_kernel tau (?center (fst zy)) (snd zy)) \<in> borel_measurable ?MY"
    unfolding slp_center_kernel_def slp_center_phase_def by measurable
  interpret natural_product: product_sigma_finite
    "(\<lambda>_::nat. (lborel :: slp_point measure))" by standard
  interpret left_family: sigma_finite_measure ?PL
    by (rule natural_product.sigma_finite) simp
  interpret right_family: sigma_finite_measure ?PR
    by (rule natural_product.sigma_finite) simp
  interpret left_arrays: pair_sigma_finite ?PL ?PL ..
  interpret right_arrays: pair_sigma_finite ?PR ?PR ..
  interpret left_array_measure: sigma_finite_measure "(?PL \<Otimes>\<^sub>M ?PL)" by standard
  interpret right_array_measure: sigma_finite_measure "(?PR \<Otimes>\<^sub>M ?PR)" by standard
  interpret left_coordinates: pair_sigma_finite
    "(?PL \<Otimes>\<^sub>M ?PL)" "(lborel :: slp_point measure)" ..
  interpret right_coordinates: pair_sigma_finite
    "(?PR \<Otimes>\<^sub>M ?PR)" "(lborel :: slp_point measure)" ..
  interpret left_measure: sigma_finite_measure ?BL by standard
  interpret right_measure: sigma_finite_measure ?BR by standard
  interpret branches: pair_sigma_finite ?BL ?BR ..
  interpret branch_measure: sigma_finite_measure ?N by standard
  interpret joint: pair_sigma_finite ?N "(lborel :: slp_point measure)" ..
  interpret joint_measure: sigma_finite_measure ?MJ by standard
  interpret averaging: pair_sigma_finite ?MJ "(lborel :: slp_point measure)" ..
  have product_integrable: "integrable ?MY (case_prod (?Tensor w h))"
    if w_integrable: "integrable ?MJ w" and h_integrable: "integrable lborel h"
    for w h
  proof -
    have w_borel[measurable]: "w \<in> borel_measurable ?MJ"
      using w_integrable by measurable
    have h_borel[measurable]: "h \<in> borel_measurable lborel"
      using h_integrable by measurable
    have P_borel: "case_prod (?Tensor w h) \<in> borel_measurable ?MY"
      unfolding case_prod_unfold by measurable
    have P_norm: "norm (?Tensor w h z y) = norm (w z) * norm (h y)" for z y
      by (simp add: norm_mult norm_exp_i_times)
    have outer_norm:
      "integrable ?MJ (\<lambda>z. integral\<^sup>L lborel (\<lambda>y. norm (?Tensor w h z y)))"
      by (simp only: P_norm Bochner_Integration.integral_mult_right_zero;
          intro Bochner_Integration.integrable_mult_left
            Bochner_Integration.integrable_norm w_integrable)
    have section_L1: "integrable lborel (?Tensor w h z)" for z
      by (simp only: mult.assoc;
          intro Bochner_Integration.integrable_mult_right
            slp_center_kernel_integrable_mult h_integrable)
    have sections: "AE z in ?MJ. integrable lborel (?Tensor w h z)"
      by (intro AE_I2 section_L1)
    show ?thesis
      by (rule averaging.Fubini_integrable[OF P_borel])
        (simp_all only: case_prod_conv outer_norm sections)
  qed
  let ?P0 = "?Tensor (?W ?A ?B ?one) phi"
  let ?P1 = "?Tensor (?W ?A ?one ?one) (\<lambda>y. phi y * ?B y)"
  let ?P2 = "?Tensor (?W ?one ?B ?one) (\<lambda>y. phi y * ?A y)"
  let ?P3 = "?Tensor ?a (\<lambda>y. phi y * (?A y * ?B y))"
  have P0: "integrable ?MY (case_prod ?P0)" by (rule product_integrable[OF raw0 phi0])
  have P1: "integrable ?MY (case_prod ?P1)" by (rule product_integrable[OF raw1 phi1])
  have P2: "integrable ?MY (case_prod ?P2)" by (rule product_integrable[OF raw2 phi2])
  have P3: "integrable ?MY (case_prod ?P3)" by (rule product_integrable[OF raw3 phi3])
  have combined: "integrable ?MY (\<lambda>zy. ?P0 (fst zy) (snd zy) -
    ?P1 (fst zy) (snd zy) - ?P2 (fst zy) (snd zy) + ?P3 (fst zy) (snd zy))"
    using P0 P1 P2 P3 unfolding case_prod_unfold
    by (intro Bochner_Integration.integrable_add Bochner_Integration.integrable_diff)
  have expansion: "?G z y = ?P0 z y - ?P1 z y - ?P2 z y + ?P3 z y" for z y
  proof -
    note f0 = raw_factor[of ?A ?B z]
    note f1 = raw_factor[of ?A ?one z]
    note f2 = raw_factor[of ?one ?B z]
    show ?thesis by (simp only: f0 f1 f2; simp add: algebra_simps)
  qed
  have G_integrable: "integrable ?MY (case_prod ?G)"
    using combined by (simp only: case_prod_unfold expansion)
  have fixed_integrable: "integrable ?MJ (\<lambda>z. ?F z y)" for y
    using slp_natural_mixed_fixed_preaverage_integrable[
      OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
        cutoff_support q_support qt_support,
      where n=n and m=m and lo=lo and ro=ro and tau=tau and y=y]
    by (auto simp only: Let_def)
  have inner_identity: "?I z = ?scale * integral\<^sup>L lborel (?G z)" for z
  proof -
    have factor: "?G z y = (?e z * ?a z) * (slp_center_kernel tau (?center z) y *
      phi y * (?A (?s z) - ?A y) * (?B (?t z) - ?B y))" for y
      by (simp add: algebra_simps)
    have scalar:
      "slp_mixed_center_average_bracket tau phi ?A ?B (?center z) (?s z) (?t z) =
        ?scale * integral\<^sup>L lborel (\<lambda>y. slp_center_kernel tau (?center z) y *
          phi y * (?A (?s z) - ?A y) * (?B (?t z) - ?B y))"
      by (rule slp_center_average_terminal_difference_integral(2)[OF phi0 phi1 phi2 phi3])
    show ?thesis by (simp only: factor scalar Bochner_Integration.integral_mult_right_zero;
      simp only: mult_ac)
  qed
  have I_integrable: "integrable ?MJ ?I"
    unfolding inner_identity
    by (intro Bochner_Integration.integrable_mult_right averaging.integrable_fst[OF G_integrable])
  have outer_integrable: "integrable lborel (\<lambda>y. integral\<^sup>L ?MJ (\<lambda>z. ?G z y))"
    by (rule averaging.integrable_snd[OF G_integrable])
  have exact: "?scale * integral\<^sup>L lborel
      (\<lambda>y. integral\<^sup>L ?MJ (\<lambda>z. ?G z y)) = integral\<^sup>L ?MJ ?I"
    by (simp only: inner_identity Bochner_Integration.integral_mult_right_zero
      averaging.Fubini_integral[OF G_integrable])
  show ?thesis unfolding Let_def
    using fixed_integrable G_integrable I_integrable outer_integrable exact by blast
qed

end

end
