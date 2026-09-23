theory Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Principal_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Negative_Residual_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Amplitude"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Principal_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Conjugation"
begin

hide_const (open) Commutative_Ring.norm

section \<open>All-natural right one-sided principal decay\<close>

lemma slp_natural_right_one_sided_zero_principal_amplitudes_equal:
  "slp_natural_right_one_sided_weighted_amplitude 0 Q cutoff q T H z =
    slp_natural_right_one_sided_weighted_amplitude 0 Q cutoff q (\<lambda>_. 1)
      (\<lambda>u. H u * T u) z"
  unfolding slp_natural_right_one_sided_weighted_amplitude_def Let_def
  by (simp add: slp_left_branch_complex_terminal_def algebra_simps)

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_right_one_sided_principal_decay:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q Q phi :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes stationary:
      "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "let A = slp_cauchy_transform orientation q;
             P = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((P \<Otimes>\<^sub>M P) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel;
             ps = (\<lambda>z. map (\<lambda>k.
               (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]);
             residual = (\<lambda>z. slp_right_branch_residual (ps z) (snd (fst z)))
    in ((\<lambda>omega::real. integral\<^sup>L MJ
      (\<lambda>z. exp (\<i> * of_real (omega * residual z)) *
        (slp_natural_right_one_sided_weighted_amplitude n Q cutoff q A phi z -
         slp_natural_right_one_sided_weighted_amplitude n Q cutoff q (\<lambda>_. 1)
           (\<lambda>u. phi u * A u) z))) \<longlongrightarrow> 0) at_top"
proof (cases n)
  case 0
  have bracket_zero:
    "slp_natural_right_one_sided_weighted_amplitude 0 Q cutoff q
        (slp_cauchy_transform orientation q) phi z -
      slp_natural_right_one_sided_weighted_amplitude 0 Q cutoff q (\<lambda>_. 1)
        (\<lambda>u. phi u * slp_cauchy_transform orientation q u) z = 0"
    for z
  proof -
    have amplitudes_equal:
      "slp_natural_right_one_sided_weighted_amplitude 0 Q cutoff q
          (slp_cauchy_transform orientation q) phi z =
        slp_natural_right_one_sided_weighted_amplitude 0 Q cutoff q (\<lambda>_. 1)
          (\<lambda>u. phi u * slp_cauchy_transform orientation q u) z"
      unfolding slp_natural_right_one_sided_weighted_amplitude_def Let_def
      by (simp add: slp_left_branch_complex_terminal_def algebra_simps)
    show ?thesis using amplitudes_equal by simp
  qed
  show ?thesis
    using 0
    unfolding Let_def
    by (simp add: bracket_zero)
next
  case (Suc k)
  let ?Qc = "\<lambda>x. cnj (Q x)"
  let ?cutoffc = "\<lambda>x. cnj (cutoff x)"
  let ?qc = "\<lambda>x. cnj (q x)"
  let ?phic = "\<lambda>x. cnj (phi x)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?Ac = "slp_cauchy_transform
    (slp_opposite_cauchy_orientation orientation) ?qc"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?P = "PiM {..<Suc k} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MJ = "((?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M
    (lborel :: slp_point measure)) \<Otimes>\<^sub>M lborel"
  let ?ps = "\<lambda>z. map (\<lambda>j.
    (fst (fst (fst z)) j, snd (fst (fst z)) j)) [0..<Suc k]"
  let ?left_residual = "\<lambda>z.
    slp_left_branch_residual (?ps z) (snd (fst z))"
  let ?right_residual = "\<lambda>z.
    slp_right_branch_residual (?ps z) (snd (fst z))"
  let ?left = "\<lambda>z.
    slp_natural_one_sided_weighted_amplitude (Suc k)
        ?Qc ?cutoffc ?qc ?Ac ?phic z -
      slp_natural_one_sided_weighted_amplitude (Suc k)
        ?Qc ?cutoffc ?qc ?one (\<lambda>u. ?phic u * ?Ac u) z"
  let ?right = "\<lambda>z.
    slp_natural_right_one_sided_weighted_amplitude (Suc k)
        Q cutoff q ?A phi z -
      slp_natural_right_one_sided_weighted_amplitude (Suc k)
        Q cutoff q ?one (\<lambda>u. phi u * ?A u) z"
  have A_conjugate: "(\<lambda>u. cnj (?A u)) = ?Ac"
    by (rule ext) simp
  have cnj_borel: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          continuous_on_cnj[OF continuous_on_id]])
  have cutoffc_measurable[measurable]: "?cutoffc \<in> borel_measurable lborel"
    using measurable_comp[OF cutoff_measurable cnj_borel]
    by (simp only: comp_def)
  have qc_lp: "aim_complex_lp_on_plane p ?qc"
    using q_lp by simp
  have Qc_lp: "aim_complex_lp_on_plane p ?Qc"
    using Q_lp by simp
  have Qc_outside: "?Qc x = 0" if "x \<notin> X" for x
    using Q_outside[OF that] by simp
  have cutoffc_bound: "norm (?cutoffc x) \<le> C" for x
    using cutoff_bound[of x] by simp
  have Qc_support: "norm x \<le> R" if "?Qc x \<noteq> 0" for x
    by (rule Q_support) (use that in simp)
  have cutoffc_support: "norm x \<le> R" if "?cutoffc x \<noteq> 0" for x
    by (rule cutoff_support) (use that in simp)
  have qc_support: "norm x \<le> R" if "?qc x \<noteq> 0" for x
    by (rule q_support) (use that in simp)
  have phic_test: "slp_test_function_on UNIV ?phic"
    using phi_test by simp
  have left_integrable: "integrable ?MJ ?left"
  proof -
    have raw:
      "let A = slp_cauchy_transform
                    (slp_opposite_cauchy_orientation orientation) ?qc;
           P = PiM {..<Suc k} (\<lambda>_::nat. (lborel :: slp_point measure));
           MJ = ((P \<Otimes>\<^sub>M P) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel;
           ps = (\<lambda>z. map (\<lambda>j.
             (fst (fst (fst z)) j, snd (fst (fst z)) j)) [0..<Suc k]);
           residual = (\<lambda>z.
             slp_left_branch_residual (ps z) (snd (fst z)))
       in integrable MJ (\<lambda>z. exp (\<i> * of_real (0 * residual z)) *
         (slp_natural_one_sided_weighted_amplitude (Suc k)
              ?Qc ?cutoffc ?qc A ?phic z -
          slp_natural_one_sided_weighted_amplitude (Suc k)
              ?Qc ?cutoffc ?qc (\<lambda>_. 1) (\<lambda>u. ?phic u * A u) z))"
      by (rule slp_natural_one_sided_principal_components_integrable[
        OF R_nonnegative p_lower p_upper X_measurable X_bounded
          cutoffc_measurable qc_lp Qc_lp Qc_outside cutoffc_bound
          C_nonnegative Qc_support cutoffc_support qc_support phic_test])
    show ?thesis using raw by (simp add: Let_def)
  qed
  have negative_decay:
    "((\<lambda>omega::real. integral\<^sup>L ?MJ
      (\<lambda>z. exp (\<i> * of_real ((- omega) * ?left_residual z)) *
        ?left z)) \<longlongrightarrow> 0) at_top"
  proof -
    note raw = slp_natural_one_sided_negative_residual_decay[
      OF stationary density left_integrable]
    show ?thesis using raw by (simp only: Let_def)
  qed
  have right_left: "?right z = cnj (?left z)" for z
    by (simp add: slp_natural_right_one_sided_weighted_amplitude_conjugate
        A_conjugate algebra_simps)
  let ?negative = "\<lambda>omega::real. integral\<^sup>L ?MJ
    (\<lambda>z. exp (\<i> * of_real ((- omega) * ?left_residual z)) *
      ?left z)"
  let ?positive = "\<lambda>omega::real. integral\<^sup>L ?MJ
    (\<lambda>z. exp (\<i> * of_real (omega * ?right_residual z)) *
      ?right z)"
  have phase_conjugate:
    "exp (\<i> * of_real (omega * ?right_residual z)) =
      cnj (exp (\<i> * of_real ((- omega) * ?left_residual z)))" for omega z
    by (simp add: exp_cnj algebra_simps slp_left_branch_residual_def
        slp_right_branch_residual_def)
  have pointwise:
    "exp (\<i> * of_real (omega * ?right_residual z)) * ?right z =
      cnj (exp (\<i> * of_real ((- omega) * ?left_residual z)) *
        ?left z)" for omega z
    by (simp only: right_left[of z] phase_conjugate[of omega z]
        complex_cnj_mult)
  have integrand_eq:
    "(\<lambda>z. exp (\<i> * of_real (omega * ?right_residual z)) *
        ?right z) =
      (\<lambda>z. cnj (exp (\<i> * of_real ((- omega) * ?left_residual z)) *
        ?left z))" for omega
    by (rule ext) (rule pointwise)
  have positive_eq:
    "?positive omega = integral\<^sup>L ?MJ
      (\<lambda>z. cnj (exp (\<i> * of_real ((- omega) * ?left_residual z)) *
        ?left z))" for omega
    by (simp only: integrand_eq)
  have move_conjugate:
    "integral\<^sup>L ?MJ
        (\<lambda>z. cnj (exp (\<i> * of_real ((- omega) * ?left_residual z)) *
          ?left z)) = cnj (?negative omega)" for omega
    by (rule Bochner_Integration.integral_cnj)
  have integral_conjugate: "?positive omega = cnj (?negative omega)" for omega
    using positive_eq[of omega] move_conjugate[of omega] by simp
  have conjugate_decay:
    "((\<lambda>omega. cnj (?negative omega)) \<longlongrightarrow> cnj 0) at_top"
    by (rule tendsto_cnj[OF negative_decay])
  have positive_decay: "(?positive \<longlongrightarrow> 0) at_top"
    using conjugate_decay
    by (simp only: integral_conjugate; simp)
  show ?thesis
    using Suc positive_decay by (simp only: Let_def)
qed

end

end
