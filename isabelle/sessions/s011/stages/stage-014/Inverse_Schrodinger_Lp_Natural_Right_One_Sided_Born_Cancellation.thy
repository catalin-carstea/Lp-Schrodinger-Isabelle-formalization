theory Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Born_Cancellation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Born_Identity"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Principal_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Error_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>All-natural right one-sided Born cancellation\<close>

theorem slp_natural_right_one_sided_amplitude_terminal_factor:
  fixes n :: nat and Q cutoff q T H :: slp_scalar_field
  shows "slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T H z =
    (let ps = map (\<lambda>k. (fst (fst (fst z)) k,
                            snd (fst (fst z)) k)) [0..<n];
         s = snd (fst z);
         output = slp_right_branch_output ps s
     in slp_natural_right_one_sided_weighted_amplitude n Q cutoff q
          (\<lambda>_. 1) (\<lambda>_. 1) z * T s * H output)"
proof -
  let ?ps = "map (\<lambda>k. (fst (fst (fst z)) k,
    snd (fst (fst z)) k)) [0..<n]"
  let ?s = "snd (fst z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  have terminal_factor:
      "slp_left_branch_complex_kernel_list
          (\<lambda>y. cnj (cutoff y)) (\<lambda>y. cnj (q y))
          (\<lambda>y. cnj (T y)) ?ps (snd z) ?s =
        cnj (T ?s) * slp_left_branch_complex_kernel_list
          (\<lambda>y. cnj (cutoff y)) (\<lambda>y. cnj (q y)) ?one
          ?ps (snd z) ?s"
    by (rule slp_left_branch_list_terminal_factor)
  show ?thesis
    unfolding slp_natural_right_one_sided_weighted_amplitude_def Let_def
    by (simp add: terminal_factor algebra_simps)
qed

theorem slp_natural_right_one_sided_bracket_integrand_decomposition:
  fixes n :: nat and tau :: real and Q cutoff q phi :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  shows "let P = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((P \<Otimes>\<^sub>M P) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel;
             ps = (\<lambda>z. map (\<lambda>k. (fst (fst (fst z)) k,
               snd (fst (fst z)) k)) [0..<n]);
             s = (\<lambda>z. snd (fst z));
             output = (\<lambda>z. slp_right_branch_output (ps z) (s z));
             phase = (\<lambda>z. slp_right_branch_residual (ps z) (s z));
             A = slp_cauchy_transform orientation q;
             a = slp_natural_right_one_sided_weighted_amplitude n Q cutoff q
               (\<lambda>_. 1) (\<lambda>_. 1);
             W = (\<lambda>T H. slp_natural_right_one_sided_weighted_amplitude
               n Q cutoff q T H);
             E = (\<lambda>h c. slp_center_average tau h c - h c);
             e = (\<lambda>z. exp (\<i> * of_real (tau * phase z)))
    in e z * a z * slp_one_sided_center_average_bracket tau phi A
         (output z) (s z) =
       e z * (W A phi z - W (\<lambda>_. 1) (\<lambda>c. phi c * A c) z) +
       e z * W A (E phi) z -
       e z * W (\<lambda>_. 1) (E (\<lambda>c. phi c * A c)) z"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MJ = "((?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure))
    \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  let ?s = "\<lambda>z. snd (fst z)"
  let ?output = "\<lambda>z. slp_right_branch_output (?ps z) (?s z)"
  let ?phase = "\<lambda>z. slp_right_branch_residual (?ps z) (?s z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?W = "\<lambda>T H. slp_natural_right_one_sided_weighted_amplitude
    n Q cutoff q T H"
  let ?a = "?W ?one ?one"
  let ?e = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z))"
  let ?E = "\<lambda>h c. slp_center_average tau h c - h c"
  have factor: "?W T H z = ?a z * T (?s z) * H (?output z)" for T H z
    using slp_natural_right_one_sided_amplitude_terminal_factor[
      where n=n and Q=Q and cutoff=cutoff and q=q and T=T and H=H and z=z]
    by (simp only: Let_def)
  note principal_terminal = factor[of ?A phi z]
  note principal_output = factor[of ?one "\<lambda>c. phi c * ?A c" z]
  note smooth = factor[of ?A "?E phi" z]
  note cauchy = factor[of ?one "?E (\<lambda>c. phi c * ?A c)" z]
  show ?thesis unfolding Let_def slp_one_sided_center_average_bracket_def
    by (simp only: principal_terminal principal_output smooth cauchy;
        simp add: algebra_simps)
qed

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_right_born_functional_natural_cancellation:
  fixes n :: nat and p :: real and Y :: "slp_point set"
    and cutoff q Q phi :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes stationary:
      "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and fourier_plancherel:
      "hormander_euclidean_l2_fourier_plancherel_claim"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and Y_bounded: "bounded Y"
    and Y_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "((\<lambda>tau. slp_right_born_functional n tau phi Q cutoff q orientation)
    \<longlongrightarrow> 0) at_top"
proof -
  interpret one_hls: aim_planar_riesz_hls_cauchy by unfold_locales
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  let ?s = "\<lambda>z. snd (fst z)"
  let ?output = "\<lambda>z. slp_right_branch_output (?ps z) (?s z)"
  let ?residual = "\<lambda>z. slp_right_branch_residual (?ps z) (?s z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?W = "\<lambda>T H. slp_natural_right_one_sided_weighted_amplitude
    n Q cutoff q T H"
  let ?a = "?W ?one ?one"
  let ?e = "\<lambda>tau z. exp (\<i> * of_real (tau * ?residual z))"
  let ?E = "\<lambda>tau h c. slp_center_average tau h c - h c"
  let ?F0 = "\<lambda>tau z. ?e tau z *
    (?W ?A phi z - ?W ?one (\<lambda>c. phi c * ?A c) z)"
  let ?F1 = "\<lambda>tau z. ?e tau z * ?W ?A (?E tau phi) z"
  let ?F2 = "\<lambda>tau z. ?e tau z *
    ?W ?one (?E tau (\<lambda>c. phi c * ?A c)) z"
  let ?I = "\<lambda>tau z. ?e tau z * ?a z *
    slp_one_sided_center_average_bracket tau phi ?A (?output z) (?s z)"
  let ?J0 = "\<lambda>tau. integral\<^sup>L ?MJ (?F0 tau)"
  let ?J1 = "\<lambda>tau. integral\<^sup>L ?MJ (?F1 tau)"
  let ?J2 = "\<lambda>tau. integral\<^sup>L ?MJ (?F2 tau)"
  let ?full = "\<lambda>tau. integral\<^sup>L ?MJ (?I tau)"
  obtain R C where R_nonnegative: "0 \<le> (R::real)"
    and C_nonnegative: "0 \<le> (C::real)"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
  proof (rule slp_test_cutoff_bounded_geometry[
      where Y=Y and cutoff=cutoff and q=q and qt=q and Q=Q,
      OF Y_bounded cutoff_test cutoff_q cutoff_q Q_in])
    fix R C :: real
    assume R: "0 \<le> R" and C: "0 \<le> C"
      and measurable: "cutoff \<in> borel_measurable lborel"
      and bound: "\<And>x. norm (cutoff x) \<le> C"
      and Q: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and cutoff: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and q: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and q_again: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    show thesis by (rule that[OF R C measurable bound Q cutoff q])
  qed
  have Q_outside: "Q x = 0" if "x \<notin> Y" for x
    using Q_in that by blast
  have left_residual_measurable:
      "(\<lambda>z. slp_left_branch_residual (?ps z) (?s z))
        \<in> borel_measurable ?MJ"
    by (rule slp_natural_branch_residual_param_measurable; measurable)
  have residual_measurable[measurable]:
      "?residual \<in> borel_measurable ?MJ"
    using left_residual_measurable
    by (simp only: slp_left_branch_residual_def slp_right_branch_residual_def)
  have phase_measurable:
    "(\<lambda>z. tau * ?residual z) \<in> borel_measurable ?MJ" for tau
    by measurable
  note principal = one_hls.slp_natural_right_one_sided_principal_decay[
    OF stationary density R_nonnegative p_lower p_upper Y_measurable
      Y_bounded cutoff_measurable q_lp Q_lp Q_outside cutoff_bound
      C_nonnegative Q_support cutoff_support q_support phi_test,
    where n=n and orientation=orientation]
  have principal_limit: "(?J0 \<longlongrightarrow> 0) at_top"
    using principal by (auto simp only: Let_def)
  note smooth = one_hls.slp_natural_right_one_sided_smooth_error_decay[
    where n=n and R=R and C=C and p=p and X=Y and cutoff=cutoff and q=q
      and Q=Q and phi=phi and orientation=orientation
      and psi="\<lambda>tau z. tau * ?residual z",
    OF R_nonnegative p_lower p_upper Y_measurable Y_bounded
      cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
      fourier_plancherel phi_test Q_support cutoff_support q_support
      phase_measurable]
  have smooth_integrability:
    "eventually (\<lambda>tau. integrable ?MJ (?F1 tau)) at_top"
    using smooth by (auto simp only: Let_def)
  have smooth_limit: "(?J1 \<longlongrightarrow> 0) at_top"
    using smooth by (auto simp only: Let_def)
  note cauchy = one_hls.slp_natural_right_one_sided_cauchy_error_decay[
    where n=n and R=R and C=C and p=p and X=Y and cutoff=cutoff and q=q
      and Q=Q and phi=phi and orientation=orientation
      and psi="\<lambda>tau z. tau * ?residual z",
    OF R_nonnegative p_lower p_upper Y_measurable Y_bounded
      cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
      fourier_plancherel phi_test Q_support cutoff_support q_support
      phase_measurable]
  have cauchy_integrability:
    "eventually (\<lambda>tau. integrable ?MJ (?F2 tau)) at_top"
    using cauchy by (auto simp only: Let_def)
  have cauchy_limit: "(?J2 \<longlongrightarrow> 0) at_top"
    using cauchy by (auto simp only: Let_def)
  have error_integrability:
    "eventually (\<lambda>tau. integrable ?MJ (?F1 tau) \<and>
      integrable ?MJ (?F2 tau)) at_top"
    using smooth_integrability cauchy_integrability
    by (rule eventually_conj)
  have pointwise:
    "?I tau z = ?F0 tau z + ?F1 tau z - ?F2 tau z" for tau z
    using slp_natural_right_one_sided_bracket_integrand_decomposition[
      where n=n and Q=Q and cutoff=cutoff and q=q and phi=phi
        and orientation=orientation and tau=tau and z=z]
    by (simp only: Let_def)
  have full_integrable: "integrable ?MJ (?I tau)" for tau
    using one_hls.slp_natural_right_one_sided_born_bracket_identity[
      OF R_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        Q_support cutoff_support q_support phi_test,
      where n=n and orientation=orientation and tau=tau]
    by (auto simp only: Let_def)
  have F0_integrable:
      "integrable ?MJ (?F0 tau)"
    if i1: "integrable ?MJ (?F1 tau)" and i2: "integrable ?MJ (?F2 tau)"
    for tau
  proof -
    have F0_eq:
        "?F0 tau = (\<lambda>z. ?I tau z - ?F1 tau z + ?F2 tau z)"
      by (rule ext) (simp only: pointwise; simp add: algebra_simps)
    have difference_integrable:
        "integrable ?MJ (\<lambda>z. ?I tau z - ?F1 tau z)"
      by (rule Bochner_Integration.integrable_diff[OF full_integrable i1])
    show ?thesis unfolding F0_eq
      by (rule Bochner_Integration.integrable_add[OF difference_integrable i2])
  qed
  have integral_expansion:
    "?full tau = ?J0 tau + ?J1 tau - ?J2 tau"
    if i1: "integrable ?MJ (?F1 tau)" and i2: "integrable ?MJ (?F2 tau)"
    for tau
  proof -
    have i0: "integrable ?MJ (?F0 tau)"
      by (rule F0_integrable[OF i1 i2])
    have s01: "integrable ?MJ (\<lambda>z. ?F0 tau z + ?F1 tau z)"
      by (rule Bochner_Integration.integrable_add[OF i0 i1])
    show ?thesis
      by (simp only: pointwise Bochner_Integration.integral_diff[OF s01 i2]
          Bochner_Integration.integral_add[OF i0 i1])
  qed
  have eventual_expansion:
    "\<forall>\<^sub>F tau in at_top. ?full tau = ?J0 tau + ?J1 tau - ?J2 tau"
    using error_integrability
  proof eventually_elim
    fix tau :: real
    assume all: "integrable ?MJ (?F1 tau) \<and> integrable ?MJ (?F2 tau)"
    show "?full tau = ?J0 tau + ?J1 tau - ?J2 tau"
      by (rule integral_expansion[OF conjunct1[OF all] conjunct2[OF all]])
  qed
  have first_sum:
    "((\<lambda>tau. ?J0 tau + ?J1 tau) \<longlongrightarrow> 0 + 0) at_top"
    by (rule tendsto_add[OF principal_limit smooth_limit])
  have last_sum:
    "((\<lambda>tau. ?J0 tau + ?J1 tau - ?J2 tau)
      \<longlongrightarrow> 0 + 0 - 0) at_top"
    by (rule tendsto_diff[OF first_sum cauchy_limit])
  have sum_limit:
    "((\<lambda>tau. ?J0 tau + ?J1 tau - ?J2 tau) \<longlongrightarrow> 0) at_top"
    using last_sum by simp
  have full_limit: "(?full \<longlongrightarrow> 0) at_top"
    by (rule tendsto_cong[OF eventual_expansion, THEN iffD2, OF sum_limit])
  have born_identity:
    "slp_right_born_functional n tau phi Q cutoff q orientation = ?full tau"
    for tau
    using one_hls.slp_natural_right_one_sided_born_bracket_identity[
      OF R_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        Q_support cutoff_support q_support phi_test,
      where n=n and orientation=orientation and tau=tau]
    by (auto simp only: Let_def)
  show ?thesis using full_limit by (simp only: born_identity)
qed

end

end
