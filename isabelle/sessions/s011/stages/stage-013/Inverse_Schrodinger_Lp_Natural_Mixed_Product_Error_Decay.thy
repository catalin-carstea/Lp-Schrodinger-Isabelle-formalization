theory Inverse_Schrodinger_Lp_Natural_Mixed_Product_Error_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Unit_Approximation_Data"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Center_Error_Approximation_Transfer"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Supported L1 approximation of the natural averaged-unit functional\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_natural_mixed_supported_l1_average_decay:
  fixes n m :: nat and p :: real and Y :: "slp_point set"
    and cutoff q qt Q h :: slp_scalar_field and Z :: "slp_point set"
  assumes stationary: "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and fourier_plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and Y_bounded: "bounded Y"
    and Y_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
    and h_integrable: "integrable lborel h"
    and Z_measurable: "Z \<in> sets lborel"
    and Z_bounded: "bounded Z"
    and h_support: "\<And>x. h x \<noteq> 0 \<Longrightarrow> x \<in> Z"
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
             a = slp_natural_mixed_weighted_amplitude n m Q cutoff q (\<lambda>_. 1)
               qt (\<lambda>_. 1) (\<lambda>_. 1);
             F = (\<lambda>h tau z. exp (\<i> * of_real (tau * phase z)) *
               a z * slp_center_average tau h (center z));
             I = (\<lambda>h tau. integral\<^sup>L MJ (F h tau))
    in (\<forall>tau. integrable MJ (F h tau)) \<and>
       ((\<lambda>tau. I h tau) \<longlongrightarrow> 0) at_top"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z)
    (?lp (fst z)) (snd (fst (fst z))) (?rp (fst z)) (snd (snd (fst z)))"
  let ?phase = "\<lambda>z. slp_mixed_branch_residual (snd z)
    (?lp (fst z)) (snd (fst (fst z))) (?rp (fst z)) (snd (snd (fst z)))"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?a = "slp_natural_mixed_weighted_amplitude n m Q cutoff q ?one qt ?one ?one"
  let ?F = "\<lambda>h tau z. exp (\<i> * of_real (tau * ?phase z)) *
    ?a z * slp_center_average tau h (?center z)"
  let ?I = "\<lambda>h tau. integral\<^sup>L ?MJ (?F h tau)"
  have data:
    "(\<forall>g tau. integrable lborel g \<longrightarrow> integrable ?MJ (?F g tau)) \<and>
     (\<forall>g. integrable lborel g \<and> aim_complex_lp_on_plane 2 g \<longrightarrow>
       ((\<lambda>tau. ?I g tau) \<longlongrightarrow> 0) at_top) \<and>
     (\<exists>K::real. 0 \<le> K \<and> (\<forall>g tau. integrable lborel g \<and> 2 \<le> tau \<longrightarrow>
       norm (?I g tau) \<le> K * aim_complex_lp_norm 1 g))"
    by (rule slp_natural_mixed_unit_average_approximation_data[
          unfolded Let_def, OF stationary density fourier_plancherel p_lower p_upper
            Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp cutoff_q cutoff_qt,
          where n=n and m=m]) (erule Q_in)
  note integration_data = data[THEN conjunct1]
  note decay_data = data[THEN conjunct2, THEN conjunct1]
  note uniform_data = data[THEN conjunct2, THEN conjunct2]
  have averaged_integrable: "integrable ?MJ (?F g tau)"
    if g_integrable: "integrable lborel g" for g tau
    by (rule integration_data[THEN spec, of g, THEN spec, of tau, THEN mp, OF g_integrable])
  obtain K :: real where K_nonnegative: "0 \<le> K"
    and K_all: "\<forall>g tau. integrable lborel g \<and> 2 \<le> tau \<longrightarrow>
      norm (?I g tau) \<le> K * aim_complex_lp_norm 1 g"
    using uniform_data by (elim exE conjE) (rule that; assumption)
  have h_measurable: "h \<in> borel_measurable lborel"
    by (rule borel_measurable_integrable[OF h_integrable])
  have h_norm_integrable: "integrable lborel (\<lambda>x. norm (h x))"
    by (rule integrable_norm[OF h_integrable])
  have h_lp1: "aim_complex_lp_on_plane 1 h"
    using h_measurable h_norm_integrable by (simp add: aim_complex_lp_on_plane_def)
  have one_positive: "0 < (1::real)" by simp
  have approximation_data:
    "\<exists>g::nat \<Rightarrow> slp_scalar_field.
      (\<forall>k. aim_complex_lp_on_plane 1 (g k) \<and>
        integrable lborel (g k) \<and> aim_complex_lp_on_plane 2 (g k) \<and>
        (\<forall>x. g k x \<noteq> 0 \<longrightarrow> x \<in> Z)) \<and>
      ((\<lambda>k. aim_complex_lp_norm 1 (\<lambda>x. h x - g k x)) \<longlonglongrightarrow> 0)"
    by (rule slp_supported_l1_l2_value_approximation[
          OF one_positive Z_measurable Z_bounded h_lp1]) (erule h_support)
  obtain g :: "nat \<Rightarrow> slp_scalar_field"
    where g_data: "\<forall>k. aim_complex_lp_on_plane 1 (g k) \<and>
      integrable lborel (g k) \<and> aim_complex_lp_on_plane 2 (g k) \<and>
      (\<forall>x. g k x \<noteq> 0 \<longrightarrow> x \<in> Z)"
    and error_decay: "(\<lambda>k. aim_complex_lp_norm 1 (\<lambda>x. h x - g k x)) \<longlonglongrightarrow> 0"
    using approximation_data
    by (elim exE conjE) (rule that; assumption)
  have g_integrable: "integrable lborel (g k)" for k
    by (rule g_data[THEN spec, of k, THEN conjunct2, THEN conjunct1])
  have g_l2: "aim_complex_lp_on_plane 2 (g k)" for k
    by (rule g_data[THEN spec, of k, THEN conjunct2, THEN conjunct2, THEN conjunct1])
  have approximant_decay: "((\<lambda>tau. ?I (g k) tau) \<longlongrightarrow> 0) at_top" for k
    by (rule decay_data[THEN spec, of "g k", THEN mp])
      (rule conjI[OF g_integrable g_l2])
  have difference_bound:
    "norm (?I h tau - ?I (g k) tau) \<le>
      K * aim_complex_lp_norm 1 (\<lambda>x. h x - g k x)"
    if tau_lower: "2 \<le> tau" for tau k
  proof -
    let ?d = "\<lambda>x. h x - g k x"
    have d_integrable: "integrable lborel ?d"
      by (rule Bochner_Integration.integrable_diff[OF h_integrable g_integrable])
    have pointwise: "?F ?d tau z = ?F h tau z - ?F (g k) tau z" for z
      by (simp only: slp_center_average_diff[OF h_integrable g_integrable]
          right_diff_distrib)
    have difference: "?I h tau - ?I (g k) tau = ?I ?d tau"
      by (simp only: pointwise Bochner_Integration.integral_diff[
            OF averaged_integrable[OF h_integrable] averaged_integrable[OF g_integrable]])
    have bound: "norm (?I ?d tau) \<le> K * aim_complex_lp_norm 1 ?d"
      by (rule K_all[THEN spec, of ?d, THEN spec, of tau, THEN mp])
        (rule conjI[OF d_integrable tau_lower])
    show ?thesis using bound by (simp only: difference)
  qed
  have decay: "((\<lambda>tau. ?I h tau) \<longlongrightarrow> 0) at_top"
    by (rule slp_uniform_pairing_sequence_limit[
          OF error_decay difference_bound approximant_decay])
  have all_integrable: "\<forall>tau. integrable ?MJ (?F h tau)"
    by (intro allI) (rule averaged_integrable[OF h_integrable])
  show ?thesis using all_integrable decay by (auto simp only: Let_def)
qed


section \<open>The actual two-Cauchy product error at every natural branch order\<close>

theorem slp_natural_mixed_product_error_decay:
  fixes n m :: nat and p :: real and Y :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field and lo ro :: slp_cauchy_orientation
  assumes stationary: "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and fourier_plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and Y_bounded: "bounded Y"
    and Y_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
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
             H = (\<lambda>c. phi c * (A c * B c));
             W = (\<lambda>G. slp_natural_mixed_weighted_amplitude n m Q cutoff
               q (\<lambda>_. 1) qt (\<lambda>_. 1) G);
             F = (\<lambda>tau z. exp (\<i> * of_real (tau * phase z)) *
               W (\<lambda>c. slp_center_average tau H c - H c) z)
    in (\<forall>tau. integrable MJ (F tau)) \<and>
       ((\<lambda>tau. integral\<^sup>L MJ (F tau)) \<longlongrightarrow> 0) at_top"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z)
    (?lp (fst z)) (snd (fst (fst z))) (?rp (fst z)) (snd (snd (fst z)))"
  let ?phase = "\<lambda>z. slp_mixed_branch_residual (snd z)
    (?lp (fst z)) (snd (fst (fst z))) (?rp (fst z)) (snd (snd (fst z)))"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?a = "slp_natural_mixed_weighted_amplitude n m Q cutoff q ?one qt ?one ?one"
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?H = "\<lambda>c. phi c * (?A c * ?B c)"
  let ?W = "\<lambda>G. slp_natural_mixed_weighted_amplitude n m Q cutoff q ?one qt ?one G"
  let ?average = "\<lambda>tau z. exp (\<i> * of_real (tau * ?phase z)) *
    ?a z * slp_center_average tau ?H (?center z)"
  let ?raw = "\<lambda>tau z. exp (\<i> * of_real (tau * ?phase z)) * ?W ?H z"
  let ?E = "\<lambda>tau c. slp_center_average tau ?H c - ?H c"
  let ?error = "\<lambda>tau z. exp (\<i> * of_real (tau * ?phase z)) * ?W (?E tau) z"
  let ?Z = "closure {x. phi x \<noteq> 0}"
  have H_integrable: "integrable lborel ?H"
    by (rule slp_test_two_cauchy_product_integrable[OF p_lower p_upper q_lp qt_lp phi_test])
  have Z_compact: "compact ?Z"
    using phi_test unfolding slp_test_function_on_def by blast
  have Z_bounded: "bounded ?Z" by (rule compact_imp_bounded[OF Z_compact])
  have Z_borel: "?Z \<in> sets borel" by (rule borel_closed[OF closed_closure])
  have Z_measurable: "?Z \<in> sets lborel" using Z_borel by (simp only: sets_lborel)
  have H_support: "x \<in> ?Z" if "?H x \<noteq> 0" for x
    using that closure_subset[of "{x. phi x \<noteq> 0}"] by auto
  have averaged_data: "(\<forall>tau. integrable ?MJ (?average tau)) \<and>
    ((\<lambda>tau. integral\<^sup>L ?MJ (?average tau)) \<longlongrightarrow> 0) at_top"
    by (rule slp_natural_mixed_supported_l1_average_decay[
          unfolded Let_def, OF stationary density fourier_plancherel p_lower p_upper
            Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp cutoff_q cutoff_qt,
          where n=n and m=m and h="?H" and Z="?Z"])
      (auto intro: Q_in H_integrable Z_measurable Z_bounded H_support)
  have averaged_integrable: "integrable ?MJ (?average tau)" for tau
    by (rule averaged_data[THEN conjunct1, THEN spec, of tau])
  have averaged_decay:
    "((\<lambda>tau. integral\<^sup>L ?MJ (?average tau)) \<longlongrightarrow> 0) at_top"
    by (rule conjunct2[OF averaged_data])
  obtain R M :: real where R_nonnegative: "0 \<le> R" and M_nonnegative: "0 \<le> M"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> M"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
  proof (rule slp_test_cutoff_bounded_geometry[
      where Y=Y and cutoff=cutoff and q=q and qt=qt and Q=Q,
      OF Y_bounded cutoff_test cutoff_q cutoff_qt Q_in])
    fix R M :: real
    assume R: "0 \<le> R" and M: "0 \<le> M"
      and measurable: "cutoff \<in> borel_measurable lborel"
      and bound: "\<And>x. norm (cutoff x) \<le> M"
      and Q: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and cutoff: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and q: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and qt: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    show thesis by (rule that[OF R M measurable bound Q cutoff q qt])
  qed
  have Q_outside: "Q x = 0" if "x \<notin> Y" for x
    using that Q_in[of x] by blast
  interpret mixed_hls: aim_planar_riesz_hls_cauchy by unfold_locales
  have H_amplitude_integrable: "integrable ?MJ (?W ?H)"
    using mixed_hls.slp_natural_mixed_principal_components_integrable[
      OF R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
        Q_support cutoff_support q_support qt_support phi_test,
      where n=n and m=m and lo=lo and ro=ro]
    by (auto simp: Let_def)
  have raw_data: "(\<forall>tau. integrable ?MJ (?raw tau)) \<and>
    ((\<lambda>tau. integral\<^sup>L ?MJ (?raw tau)) \<longlongrightarrow> 0) at_top"
    using slp_natural_mixed_residual_integrable_decay[
      OF stationary density H_amplitude_integrable]
    by (auto simp only: Let_def)
  have raw_integrable: "integrable ?MJ (?raw tau)" for tau
    by (rule raw_data[THEN conjunct1, THEN spec, of tau])
  have raw_decay: "((\<lambda>tau. integral\<^sup>L ?MJ (?raw tau)) \<longlongrightarrow> 0) at_top"
    by (rule conjunct2[OF raw_data])
  have terminal_factor: "?W G z = ?a z * G (?center z)" for G z
    by (simp add: slp_natural_mixed_weighted_amplitude_def Let_def algebra_simps)
  have error_identity: "?error tau z = ?average tau z - ?raw tau z" for tau z
    by (simp only: terminal_factor[of "?E tau" z] terminal_factor[of ?H z]
        right_diff_distrib mult.assoc)
  have error_integrable: "integrable ?MJ (?error tau)" for tau
    by (simp only: error_identity;
        rule Bochner_Integration.integrable_diff[OF averaged_integrable raw_integrable])
  have error_integral: "integral\<^sup>L ?MJ (?error tau) =
    integral\<^sup>L ?MJ (?average tau) - integral\<^sup>L ?MJ (?raw tau)" for tau
    by (simp only: error_identity
        Bochner_Integration.integral_diff[OF averaged_integrable raw_integrable])
  have difference_decay:
    "((\<lambda>tau. integral\<^sup>L ?MJ (?average tau) - integral\<^sup>L ?MJ (?raw tau))
      \<longlongrightarrow> (0 - 0)) at_top"
    by (rule tendsto_diff[OF averaged_decay raw_decay])
  have decay: "((\<lambda>tau. integral\<^sup>L ?MJ (?error tau)) \<longlongrightarrow> 0) at_top"
    using difference_decay by (simp only: error_integral diff_self)
  have all_integrable: "\<forall>tau. integrable ?MJ (?error tau)"
    by (intro allI) (rule error_integrable)
  show ?thesis using all_integrable decay by (auto simp only: Let_def)
qed


end

end
