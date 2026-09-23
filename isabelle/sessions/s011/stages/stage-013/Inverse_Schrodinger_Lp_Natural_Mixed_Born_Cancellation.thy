theory Inverse_Schrodinger_Lp_Natural_Mixed_Born_Cancellation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Born_Identity"
begin

hide_const (open) Commutative_Ring.norm

section \<open>All-natural mixed Born cancellation\<close>

theorem slp_natural_mixed_bracket_integrand_decomposition:
  fixes n m :: nat and tau :: real and Q cutoff q qt phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
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
             W = (\<lambda>T U H. slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H);
             E = (\<lambda>h c. slp_center_average tau h c - h c);
             P = (\<lambda>z. W (\<lambda>s. A s - A (center z))
               (\<lambda>t. B t - B (center z)) phi z);
             e = (\<lambda>z. exp (\<i> * of_real (tau * phase z)))
    in e z * a z * slp_mixed_center_average_bracket tau phi A B
         (center z) (snd (fst (fst z))) (snd (snd (fst z))) =
       e z * P z + e z * W A B (E phi) z -
       e z * W A (\<lambda>_. 1) (E (\<lambda>c. phi c * B c)) z -
       e z * W (\<lambda>_. 1) B (E (\<lambda>c. phi c * A c)) z +
       e z * W (\<lambda>_. 1) (\<lambda>_. 1) (E (\<lambda>c. phi c * (A c * B c))) z"
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
  let ?E = "\<lambda>h c. slp_center_average tau h c - h c"
  have factor: "?W T U H z = ?a z * T (?s z) * U (?t z) * H (?center z)"
    for T U H z
    using slp_natural_mixed_amplitude_terminal_factor[
      where n=n and m=m and Q=Q and cutoff=cutoff and q=q and qt=qt
        and T=T and U=U and H=H and z=z]
    by (simp only: Let_def)
  note principal = factor[of "\<lambda>s. ?A s - ?A (?center z)"
    "\<lambda>t. ?B t - ?B (?center z)" phi z]
  note smooth = factor[of ?A ?B "?E phi" z]
  note cross_left = factor[of ?A ?one "?E (\<lambda>c. phi c * ?B c)" z]
  note cross_right = factor[of ?one ?B "?E (\<lambda>c. phi c * ?A c)" z]
  note product = factor[of ?one ?one "?E (\<lambda>c. phi c * (?A c * ?B c))" z]
  show ?thesis unfolding Let_def
    by (simp only: principal smooth cross_left cross_right product
        slp_mixed_center_average_bracket_decomposition;
        simp add: algebra_simps)
qed

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_mixed_born_functional_natural_cancellation:
  fixes n m :: nat and p :: real and Y :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
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
  shows "((\<lambda>tau. slp_mixed_born_functional n m tau phi Q cutoff q qt lo ro)
    \<longlongrightarrow> 0) at_top"
proof -
  interpret mixed_hls: aim_planar_riesz_hls_cauchy by unfold_locales
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
  let ?e = "\<lambda>tau z. exp (\<i> * of_real (tau * ?phase z))"
  let ?E = "\<lambda>tau h c. slp_center_average tau h c - h c"
  let ?P = "\<lambda>z. ?W (\<lambda>s. ?A s - ?A (?center z))
    (\<lambda>t. ?B t - ?B (?center z)) phi z"
  let ?F0 = "\<lambda>tau z. ?e tau z * ?P z"
  let ?F1 = "\<lambda>tau z. ?e tau z * ?W ?A ?B (?E tau phi) z"
  let ?F2 = "\<lambda>tau z. ?e tau z * ?W ?A ?one (?E tau (\<lambda>c. phi c * ?B c)) z"
  let ?F3 = "\<lambda>tau z. ?e tau z * ?W ?one ?B (?E tau (\<lambda>c. phi c * ?A c)) z"
  let ?F4 = "\<lambda>tau z. ?e tau z * ?W ?one ?one (?E tau (\<lambda>c. phi c * (?A c * ?B c))) z"
  let ?I = "\<lambda>tau z. ?e tau z * ?a z *
    slp_mixed_center_average_bracket tau phi ?A ?B (?center z) (?s z) (?t z)"
  let ?J0 = "\<lambda>tau. integral\<^sup>L ?MJ (?F0 tau)"
  let ?J1 = "\<lambda>tau. integral\<^sup>L ?MJ (?F1 tau)"
  let ?J2 = "\<lambda>tau. integral\<^sup>L ?MJ (?F2 tau)"
  let ?J3 = "\<lambda>tau. integral\<^sup>L ?MJ (?F3 tau)"
  let ?J4 = "\<lambda>tau. integral\<^sup>L ?MJ (?F4 tau)"
  let ?full = "\<lambda>tau. integral\<^sup>L ?MJ (?I tau)"
  obtain R C where R_nonnegative: "0 \<le> (R::real)"
    and C_nonnegative: "0 \<le> (C::real)"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
  proof (rule slp_test_cutoff_bounded_geometry[
      where Y=Y and cutoff=cutoff and q=q and qt=qt and Q=Q,
      OF Y_bounded cutoff_test cutoff_q cutoff_qt Q_in])
    fix R C :: real
    assume R: "0 \<le> R" and C: "0 \<le> C"
      and measurable: "cutoff \<in> borel_measurable lborel"
      and bound: "\<And>x. norm (cutoff x) \<le> C"
      and Q: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and cutoff: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and q: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and qt: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    show thesis by (rule that[OF R C measurable bound Q cutoff q qt])
  qed
  have Q_outside: "Q x = 0" if "x \<notin> Y" for x using Q_in that by blast
  note principal = mixed_hls.slp_natural_mixed_principal_integrable_decay[
    OF stationary density R_nonnegative C_nonnegative p_lower p_upper
      Y_measurable Y_bounded cutoff_measurable q_lp qt_lp Q_lp Q_outside
      cutoff_bound Q_support cutoff_support q_support qt_support phi_test,
    where n=n and m=m and lo=lo and ro=ro]
  have P_integrable: "integrable ?MJ ?P" using principal by (auto simp only: Let_def)
  have principal_limit: "(?J0 \<longlongrightarrow> 0) at_top"
    using principal by (auto simp only: Let_def)
  have F0_integrable: "integrable ?MJ (?F0 tau)" for tau
    using slp_natural_mixed_residual_integrable_decay[
      where n=n and m=m, OF stationary density P_integrable]
    by (auto simp only: Let_def)
  note errors = mixed_hls.slp_natural_mixed_smooth_cross_error_decay[
    OF fourier_plancherel R_nonnegative C_nonnegative p_lower p_upper
      Y_measurable Y_bounded cutoff_measurable q_lp qt_lp Q_lp Q_outside
      cutoff_bound cutoff_support q_support qt_support phi_test Q_support,
    where n=n and m=m and lo=lo and ro=ro]
  have error_integrability:
    "eventually (\<lambda>tau. integrable ?MJ (?F1 tau) \<and>
      integrable ?MJ (?F2 tau) \<and> integrable ?MJ (?F3 tau)) at_top"
    using errors by (auto simp only: Let_def)
  have smooth_limit: "(?J1 \<longlongrightarrow> 0) at_top"
    using errors by (auto simp only: Let_def)
  have left_limit: "(?J2 \<longlongrightarrow> 0) at_top"
    using errors by (auto simp only: Let_def)
  have right_limit: "(?J3 \<longlongrightarrow> 0) at_top"
    using errors by (auto simp only: Let_def)
  note product = slp_natural_mixed_product_error_decay[
    OF stationary density fourier_plancherel p_lower p_upper Y_bounded
      Y_measurable cutoff_test q_lp qt_lp Q_lp cutoff_q cutoff_qt Q_in phi_test,
    where n=n and m=m and lo=lo and ro=ro]
  have F4_integrable: "integrable ?MJ (?F4 tau)" for tau
    using product by (auto simp only: Let_def)
  have product_limit: "(?J4 \<longlongrightarrow> 0) at_top"
    using product by (auto simp only: Let_def)
  have pointwise:
    "?I tau z = ?F0 tau z + ?F1 tau z - ?F2 tau z - ?F3 tau z + ?F4 tau z"
    for tau z
    using slp_natural_mixed_bracket_integrand_decomposition[
      where n=n and m=m and Q=Q and cutoff=cutoff and q=q and qt=qt
        and phi=phi and lo=lo and ro=ro and tau=tau and z=z]
    by (simp only: Let_def)
  have integral_expansion:
    "?full tau = ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau + ?J4 tau"
    if i1: "integrable ?MJ (?F1 tau)" and i2: "integrable ?MJ (?F2 tau)"
      and i3: "integrable ?MJ (?F3 tau)" for tau
  proof -
    have s01: "integrable ?MJ (\<lambda>z. ?F0 tau z + ?F1 tau z)"
      by (rule Bochner_Integration.integrable_add[OF F0_integrable i1])
    have s012: "integrable ?MJ (\<lambda>z. ?F0 tau z + ?F1 tau z - ?F2 tau z)"
      by (rule Bochner_Integration.integrable_diff[OF s01 i2])
    have s0123: "integrable ?MJ (\<lambda>z. ?F0 tau z + ?F1 tau z - ?F2 tau z - ?F3 tau z)"
      by (rule Bochner_Integration.integrable_diff[OF s012 i3])
    show ?thesis
      by (simp only: pointwise Bochner_Integration.integral_add[OF s0123 F4_integrable]
          Bochner_Integration.integral_diff[OF s012 i3]
          Bochner_Integration.integral_diff[OF s01 i2]
          Bochner_Integration.integral_add[OF F0_integrable i1])
  qed
  have eventual_expansion:
    "\<forall>\<^sub>F tau in at_top. ?full tau = ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau + ?J4 tau"
    using error_integrability
  proof eventually_elim
    fix tau :: real
    assume all: "integrable ?MJ (?F1 tau) \<and>
      integrable ?MJ (?F2 tau) \<and> integrable ?MJ (?F3 tau)"
    have i1: "integrable ?MJ (?F1 tau)" using all by blast
    have i2: "integrable ?MJ (?F2 tau)" using all by blast
    have i3: "integrable ?MJ (?F3 tau)" using all by blast
    show "?full tau = ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau + ?J4 tau"
      by (rule integral_expansion[OF i1 i2 i3])
  qed
  have first_sum: "((\<lambda>tau. ?J0 tau + ?J1 tau) \<longlongrightarrow> 0 + 0) at_top"
    by (rule tendsto_add[OF principal_limit smooth_limit])
  have second_sum: "((\<lambda>tau. ?J0 tau + ?J1 tau - ?J2 tau) \<longlongrightarrow> 0 + 0 - 0) at_top"
    by (rule tendsto_diff[OF first_sum left_limit])
  have third_sum: "((\<lambda>tau. ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau)
    \<longlongrightarrow> 0 + 0 - 0 - 0) at_top"
    by (rule tendsto_diff[OF second_sum right_limit])
  have last_sum: "((\<lambda>tau. ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau + ?J4 tau)
    \<longlongrightarrow> 0 + 0 - 0 - 0 + 0) at_top"
    by (rule tendsto_add[OF third_sum product_limit])
  have sum_limit: "((\<lambda>tau. ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau + ?J4 tau)
    \<longlongrightarrow> 0) at_top" using last_sum by simp
  have full_limit: "(?full \<longlongrightarrow> 0) at_top"
    by (rule tendsto_cong[OF eventual_expansion, THEN iffD2, OF sum_limit])
  have born_identity:
    "slp_mixed_born_functional n m tau phi Q cutoff q qt lo ro = ?full tau" for tau
    using mixed_hls.slp_natural_mixed_born_bracket_identity[
      OF R_nonnegative C_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
        cutoff_support q_support qt_support phi_test,
      where n=n and m=m and lo=lo and ro=ro and tau=tau]
    by (auto simp only: Let_def)
  show ?thesis using full_limit by (simp only: born_identity)
qed

end

end
