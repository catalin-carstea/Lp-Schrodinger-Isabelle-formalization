theory Inverse_Schrodinger_Lp_Natural_Mixed_Unit_Approximation_Data
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Smooth_Cross_Error_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Density_Unit_Terminal_Finite_Target"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Finite_Kernel_L2_Dominator"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Decay of the natural averaged-unit functional on L1 intersect L2\<close>

context aim_planar_riesz_hls
begin

theorem slp_natural_mixed_unit_average_l2_decay:
  fixes n m :: nat and R C p :: real
    and cutoff q qt Q h :: slp_scalar_field
  assumes stationary: "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and fourier_plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and Q_integrable: "integrable lborel Q"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and h_integrable: "integrable lborel h"
    and h_l2: "aim_complex_lp_on_plane 2 h"
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
               qt (\<lambda>_. 1) (\<lambda>_. 1)
    in ((\<lambda>tau. integral\<^sup>L MJ (\<lambda>z. exp (\<i> * of_real (tau * phase z)) *
      a z * slp_center_average tau h (center z))) \<longlongrightarrow> 0) at_top"
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
  let ?D = "slp_mixed_center_density (2 * R) cutoff q qt (\<lambda>_. 1) (\<lambda>_. 1) n m Q"
  let ?E = "\<lambda>tau c. slp_center_average tau h c - h c"
  let ?raw = "\<lambda>tau z. exp (\<i> * of_real (tau * ?phase z)) *
    slp_natural_mixed_weighted_amplitude n m Q cutoff q ?one qt ?one h z"
  let ?error = "\<lambda>tau z. exp (\<i> * of_real (tau * ?phase z)) *
    slp_natural_mixed_weighted_amplitude n m Q cutoff q ?one qt ?one (?E tau) z"
  let ?average = "\<lambda>tau z. exp (\<i> * of_real (tau * ?phase z)) *
    ?a z * slp_center_average tau h (?center z)"
  have q_measurable[measurable]: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have qt_measurable[measurable]: "qt \<in> borel_measurable lborel"
    using qt_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    using Q_integrable by measurable
  have h_measurable[measurable]: "h \<in> borel_measurable lborel"
    using h_integrable by measurable
  have one_measurable: "?one \<in> borel_measurable lborel" by measurable
  have radius_nonnegative: "0 \<le> 2 * R" using R_nonnegative by simp
  have D_l2: "slp_positive_ennreal_lp_on_plane 2 ?D"
    by (rule slp_mixed_center_density_unit_terminal_finite_target[
          OF radius_nonnegative p_lower p_upper _ cutoff_measurable q_lp qt_lp
            Q_integrable cutoff_bound C_nonnegative]) simp
  have pair_finite: "nn_integral lborel (\<lambda>c. ?D c * ennreal (norm (h c))) < top_class.top"
    by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[
          where q=2 and r=2, OF _ _ _ D_l2 h_l2]) simp_all
  have mass_finite: "nn_integral lborel (\<lambda>c. ennreal (norm (h c)) * ?D c) < top_class.top"
    using pair_finite by (simp only: mult.commute)
  have weighted_integrable: "integrable ?MJ
    (slp_natural_mixed_weighted_amplitude n m Q cutoff q ?one qt ?one h)"
    by (rule slp_natural_mixed_weighted_amplitude_integrable_from_density[
          OF R_nonnegative cutoff_measurable q_measurable one_measurable
            qt_measurable one_measurable Q_measurable h_measurable
            Q_support cutoff_support q_support qt_support])
       (use mass_finite in auto)
  have raw_data:
    "(\<forall>tau::real. integrable ?MJ (?raw tau)) \<and>
      ((\<lambda>tau. integral\<^sup>L ?MJ (?raw tau)) \<longlongrightarrow> 0) at_top"
    using slp_natural_mixed_residual_integrable_decay[
      OF stationary density weighted_integrable]
    by (auto simp only: Let_def)
  have raw_integrable: "integrable ?MJ (?raw tau)" for tau
    using raw_data by blast
  have raw_decay: "((\<lambda>tau. integral\<^sup>L ?MJ (?raw tau)) \<longlongrightarrow> 0) at_top"
    using raw_data by blast
  have phase_measurable[measurable]: "?phase \<in> borel_measurable ?MJ"
    using slp_natural_mixed_unit_integration_data[
      OF R_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp
        cutoff_bound C_nonnegative Q_integrable Q_support cutoff_support q_support qt_support,
      where n=n and m=m]
    by (auto simp only: Let_def)
  have phase_parameter: "(\<lambda>z. tau * ?phase z) \<in> borel_measurable ?MJ" for tau::real
    by measurable
  have E_measurable: "?E tau \<in> borel_measurable lborel" for tau
  proof -
    have average[measurable]: "slp_center_average tau h \<in> borel_measurable lborel"
      by (rule slp_center_average_measurable[OF h_integrable])
    show ?thesis by measurable
  qed
  have physical_mass:
    "((\<lambda>tau. nn_integral lborel (\<lambda>c. ?D c * ennreal (norm (?E tau c))))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_positive_l2_center_error_mass_decay[
          OF fourier_plancherel D_l2 h_integrable h_l2])
  have error_mass:
    "((\<lambda>tau. nn_integral lborel (\<lambda>c. ennreal (norm (?E tau c)) *
      slp_mixed_center_density (2 * R) cutoff q qt
        (\<lambda>s. ennreal (norm (?one s))) (\<lambda>t. ennreal (norm (?one t))) n m Q c))
      \<longlongrightarrow> 0) at_top"
    using physical_mass by (simp add: mult.commute)
  note error_transfer = slp_natural_mixed_oscillatory_integral_tendsto_zero[
    where psi="\<lambda>tau z. tau * ?phase z",
    OF R_nonnegative cutoff_measurable q_measurable one_measurable qt_measurable
      one_measurable Q_measurable E_measurable Q_support cutoff_support q_support qt_support
      phase_parameter error_mass]
  have eventually_error: "eventually (\<lambda>tau. integrable ?MJ (?error tau)) at_top"
    using error_transfer(1) by blast
  have error_decay: "((\<lambda>tau. integral\<^sup>L ?MJ (?error tau)) \<longlongrightarrow> 0) at_top"
    using error_transfer(2) by blast
  have terminal_factor:
    "slp_natural_mixed_weighted_amplitude n m Q cutoff q ?one qt ?one H z =
      ?a z * H (?center z)" for H z
    by (simp add: slp_natural_mixed_weighted_amplitude_def Let_def)
  have average_split: "?average tau z = ?raw tau z + ?error tau z" for tau z
    by (simp only: terminal_factor[of h z] terminal_factor[of "?E tau" z];
        simp add: algebra_simps)
  have eventually_integral:
    "eventually (\<lambda>tau. integral\<^sup>L ?MJ (?average tau) =
      integral\<^sup>L ?MJ (?raw tau) + integral\<^sup>L ?MJ (?error tau)) at_top"
    using eventually_error
  proof eventually_elim
    fix tau
    assume error_integrable: "integrable ?MJ (?error tau)"
    show "integral\<^sup>L ?MJ (?average tau) =
      integral\<^sup>L ?MJ (?raw tau) + integral\<^sup>L ?MJ (?error tau)"
      by (simp only: average_split
            Bochner_Integration.integral_add[OF raw_integrable error_integrable])
  qed
  have sum_decay:
    "((\<lambda>tau. integral\<^sup>L ?MJ (?raw tau) + integral\<^sup>L ?MJ (?error tau))
      \<longlongrightarrow> 0) at_top"
    using tendsto_add[OF raw_decay error_decay] by simp
  show ?thesis unfolding Let_def
    by (rule tendsto_cong[OF eventually_integral, THEN iffD2]) (rule sum_decay)
qed

end

section \<open>Approximation-ready bounds for the averaged-unit functional\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_natural_mixed_unit_average_approximation_data:
  fixes n m :: nat and p :: real and Y :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field
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
    in (\<forall>h tau. integrable lborel h \<longrightarrow> integrable MJ (F h tau)) \<and>
       (\<forall>h. integrable lborel h \<and> aim_complex_lp_on_plane 2 h \<longrightarrow>
         ((\<lambda>tau. I h tau) \<longlongrightarrow> 0) at_top) \<and>
       (\<exists>K::real. 0 \<le> K \<and> (\<forall>h tau. integrable lborel h \<and> 2 \<le> tau \<longrightarrow>
         norm (I h tau) \<le> K * aim_complex_lp_norm 1 h))"
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
  let ?root = "\<lambda>tau y. of_real (tau / pi) * integral\<^sup>L lborel
    (\<lambda>x. Q x * slp_center_kernel (-tau) y x *
      slp_left_recursive_branch n tau y cutoff q ?one x *
      slp_right_recursive_branch m tau y cutoff qt ?one x)"
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
  have p_at_least_one: "1 \<le> p" using p_lower by simp
  have Q_integrable: "integrable lborel Q"
    by (rule slp_bounded_supported_lp_integrable[
          OF p_at_least_one Y_measurable Y_bounded Q_lp Q_in])
  have transpose:
    "integrable ?MJ (?F h tau) \<and> integrable lborel (\<lambda>y. h y * ?root tau y) \<and>
      ?I h tau = integral\<^sup>L lborel (\<lambda>y. h y * ?root tau y)"
    if h_integrable: "integrable lborel h" for h tau
    using slp_natural_mixed_unit_average_transpose[
      OF R_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp
        cutoff_bound M_nonnegative Q_integrable Q_support cutoff_support q_support qt_support
        h_integrable, where n=n and m=m and tau=tau]
    by (auto simp only: Let_def)
  have averaged_integrable: "integrable ?MJ (?F h tau)"
    if "integrable lborel h" for h tau
    using transpose[OF that, of tau] by blast
  have l2_decay: "((\<lambda>tau. ?I h tau) \<longlongrightarrow> 0) at_top"
    if h_integrable: "integrable lborel h" and h_l2: "aim_complex_lp_on_plane 2 h" for h
    using slp_natural_mixed_unit_average_l2_decay[
      OF stationary density fourier_plancherel R_nonnegative p_lower p_upper
        cutoff_measurable q_lp qt_lp cutoff_bound M_nonnegative Q_integrable
        Q_support cutoff_support q_support qt_support h_integrable h_l2,
      where n=n and m=m]
    by (auto simp only: Let_def)
  obtain C :: real where C_positive: "0 < C"
    and C_all: "\<forall>tau y q0 qt0 Q0.
      2 \<le> tau \<and> aim_complex_lp_on_plane p q0 \<and>
        aim_complex_lp_on_plane p qt0 \<and> aim_complex_lp_on_plane p Q0 \<and>
        (\<forall>x. cutoff x * q0 x = q0 x) \<and>
        (\<forall>x. cutoff x * qt0 x = qt0 x) \<and>
        (\<forall>x. Q0 x \<noteq> 0 \<longrightarrow> x \<in> Y) \<longrightarrow>
      integrable lborel (\<lambda>x. Q0 x * slp_center_kernel (-tau) y x *
        slp_left_recursive_branch n tau y cutoff q0 ?one x *
        slp_right_recursive_branch m tau y cutoff qt0 ?one x) \<and>
      norm (of_real (tau / pi) * integral\<^sup>L lborel
        (\<lambda>x. Q0 x * slp_center_kernel (-tau) y x *
          slp_left_recursive_branch n tau y cutoff q0 ?one x *
          slp_right_recursive_branch m tau y cutoff qt0 ?one x))
        \<le> C * aim_complex_lp_norm p Q0 *
          (aim_complex_lp_norm p q0)^n * (aim_complex_lp_norm p qt0)^m"
    using slp_mixed_recursive_root_uniform_bound[
      OF p_lower p_upper Y_bounded Y_measurable cutoff_test, where j=n and k=m]
    by (elim exE conjE) (rule that; assumption)
  have Q_all: "\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y"
    by (intro allI impI) (erule Q_in)
  have root_bound: "norm (?root tau y) \<le> C * aim_complex_lp_norm p Q *
      (aim_complex_lp_norm p q)^n * (aim_complex_lp_norm p qt)^m"
    if tau: "2 \<le> tau" for tau y
  proof -
    have hypotheses: "2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      aim_complex_lp_on_plane p qt \<and> aim_complex_lp_on_plane p Q \<and>
      (\<forall>x. cutoff x * q x = q x) \<and>
      (\<forall>x. cutoff x * qt x = qt x) \<and>
      (\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y)"
      by (intro conjI tau q_lp qt_lp Q_lp cutoff_q cutoff_qt Q_all)
    note at_tau = C_all[THEN spec, of tau]
    note at_y = at_tau[THEN spec, of y]
    note at_q = at_y[THEN spec, of q]
    note at_qt = at_q[THEN spec, of qt]
    note at_Q = at_qt[THEN spec, of Q]
    note pair = at_Q[THEN mp, OF hypotheses]
    show ?thesis by (rule conjunct2[OF pair])
  qed
  let ?K = "C * aim_complex_lp_norm p Q *
    (aim_complex_lp_norm p q)^n * (aim_complex_lp_norm p qt)^m"
  have K_nonnegative: "0 \<le> ?K"
    using C_positive by (intro mult_nonneg_nonneg zero_le_power; simp add: aim_complex_lp_norm_def)
  have l1_norm: "aim_complex_lp_norm 1 h = integral\<^sup>L lborel (\<lambda>y. norm (h y))"
    for h :: slp_scalar_field
  proof -
    have nonnegative: "0 \<le> integral\<^sup>L lborel (\<lambda>y. norm (h y))"
      by (rule Bochner_Integration.integral_nonneg) simp
    show ?thesis using nonnegative by (simp add: aim_complex_lp_norm_def)
  qed
  have average_bound: "norm (?I h tau) \<le> ?K * aim_complex_lp_norm 1 h"
    if h_integrable: "integrable lborel h" and tau: "2 \<le> tau" for h tau
  proof -
    have pair_integrable: "integrable lborel (\<lambda>y. h y * ?root tau y)"
      using transpose[OF h_integrable, of tau] by blast
    have majorant_integrable: "integrable lborel (\<lambda>y. ?K * norm (h y))"
      by (intro Bochner_Integration.integrable_mult_right integrable_norm h_integrable)
    have pointwise: "norm (h y * ?root tau y) \<le> ?K * norm (h y)" for y
    proof -
      have "norm (h y * ?root tau y) = norm (h y) * norm (?root tau y)"
        by (simp only: norm_mult)
      also have "... \<le> norm (h y) * ?K"
        by (rule mult_left_mono[OF root_bound[OF tau] norm_ge_zero])
      also have "... = ?K * norm (h y)" by (rule mult.commute)
      finally show ?thesis .
    qed
    have norm_bound:
      "norm (integral\<^sup>L lborel (\<lambda>y. h y * ?root tau y)) \<le>
        integral\<^sup>L lborel (\<lambda>y. ?K * norm (h y))"
      by (rule Bochner_Integration.integral_norm_bound_integral[
            OF pair_integrable majorant_integrable]) (rule pointwise)
    have transpose_identity: "?I h tau = integral\<^sup>L lborel (\<lambda>y. h y * ?root tau y)"
      using transpose[OF h_integrable, of tau] by blast
    show ?thesis
      using norm_bound
      by (simp only: transpose_identity Bochner_Integration.integral_mult_right_zero l1_norm)
  qed
  have all_integrable: "\<forall>h tau. integrable lborel h \<longrightarrow> integrable ?MJ (?F h tau)"
    using averaged_integrable by blast
  have all_decay: "\<forall>h. integrable lborel h \<and> aim_complex_lp_on_plane 2 h \<longrightarrow>
    ((\<lambda>tau. ?I h tau) \<longlongrightarrow> 0) at_top"
    using l2_decay by blast
  have uniform: "\<exists>K::real. 0 \<le> K \<and> (\<forall>h tau. integrable lborel h \<and> 2 \<le> tau \<longrightarrow>
    norm (?I h tau) \<le> K * aim_complex_lp_norm 1 h)"
    by (rule exI[of _ ?K]) (use K_nonnegative average_bound in blast)
  show ?thesis using all_integrable all_decay uniform by (simp only: Let_def)
qed

end

end
