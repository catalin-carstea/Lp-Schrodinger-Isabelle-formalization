theory Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Born_Identity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Born_Identity"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Amplitude"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Born_Functional"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Conjugation"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The original natural right one-sided Born functional\<close>

lemma slp_center_average_neg_conjugate:
  "cnj (slp_center_average (- tau) (\<lambda>x. cnj (f x)) c) =
    - slp_center_average tau f c"
proof -
  let ?negative = "\<lambda>x.
    slp_center_kernel (- tau) c x * cnj (f x)"
  let ?positive = "\<lambda>x. slp_center_kernel tau c x * f x"
  have pointwise: "cnj (?negative x) = ?positive x" for x
    unfolding slp_center_kernel_def
    by (simp add: exp_cnj algebra_simps)
  have move_conjugate:
      "cnj (integral\<^sup>L lborel ?negative) =
        integral\<^sup>L lborel (\<lambda>x. cnj (?negative x))"
    by (rule sym) (rule Bochner_Integration.integral_cnj)
  have integral_conjugate:
      "cnj (integral\<^sup>L lborel ?negative) =
        integral\<^sup>L lborel ?positive"
    using move_conjugate by (simp only: pointwise)
  show ?thesis
    unfolding slp_center_average_def
    using integral_conjugate
    by (simp add: algebra_simps)
qed


lemma slp_one_sided_center_average_bracket_neg_conjugate:
  "cnj (slp_one_sided_center_average_bracket (- tau)
      (\<lambda>x. cnj (phi x)) (\<lambda>x. cnj (A x)) target terminal) =
    - slp_one_sided_center_average_bracket tau phi A target terminal"
proof -
  have phi_average:
      "cnj (slp_center_average (- tau) (\<lambda>x. cnj (phi x)) target) =
        - slp_center_average tau phi target"
    by (rule slp_center_average_neg_conjugate)
  have product_average:
      "cnj (slp_center_average (- tau)
          (\<lambda>x. cnj (phi x) * cnj (A x)) target) =
        - slp_center_average tau (\<lambda>x. phi x * A x) target"
    using slp_center_average_neg_conjugate[
      where tau=tau and f="\<lambda>x. phi x * A x" and c=target]
    by (simp add: algebra_simps)
  show ?thesis
    unfolding slp_one_sided_center_average_bracket_def
    using phi_average product_average
    by (simp add: algebra_simps)
qed


context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_right_one_sided_born_bracket_identity:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
    and tau :: real and phi :: slp_scalar_field
    and cutoff q Q :: slp_scalar_field
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
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
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
             I = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_one_sided_center_average_bracket tau phi A
                 (output z) (s z))
    in integrable MJ I \<and>
       slp_right_born_functional n tau phi Q cutoff q orientation =
         integral\<^sup>L MJ I"
proof -
  let ?Qc = "\<lambda>x. cnj (Q x)"
  let ?cutoffc = "\<lambda>x. cnj (cutoff x)"
  let ?qc = "\<lambda>x. cnj (q x)"
  let ?phic = "\<lambda>x. cnj (phi x)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?Ac = "slp_cauchy_transform
    (slp_opposite_cauchy_orientation orientation) ?qc"
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MJ = "((?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M
    (lborel :: slp_point measure)) \<Otimes>\<^sub>M lborel"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  let ?s = "\<lambda>z. snd (fst z)"
  let ?output = "\<lambda>z. slp_left_branch_output (?ps z) (?s z)"
  let ?left_residual = "\<lambda>z.
    slp_left_branch_residual (?ps z) (?s z)"
  let ?right_residual = "\<lambda>z.
    slp_right_branch_residual (?ps z) (?s z)"
  let ?left_a = "slp_natural_one_sided_weighted_amplitude
    n ?Qc ?cutoffc ?qc ?one ?one"
  let ?right_a = "slp_natural_right_one_sided_weighted_amplitude
    n Q cutoff q ?one ?one"
  let ?left_I = "\<lambda>z.
    exp (\<i> * of_real ((- tau) * ?left_residual z)) * ?left_a z *
      slp_one_sided_center_average_bracket (- tau) ?phic ?Ac
        (?output z) (?s z)"
  let ?right_I = "\<lambda>z.
    exp (\<i> * of_real (tau * ?right_residual z)) * ?right_a z *
      slp_one_sided_center_average_bracket tau phi ?A
        (?output z) (?s z)"
  have A_conjugate: "(\<lambda>u. cnj (?A u)) = ?Ac"
    by (rule ext) simp
  have cnj_borel: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          continuous_on_cnj[OF continuous_on_id]])
  have cutoffc_measurable[measurable]:
      "?cutoffc \<in> borel_measurable lborel"
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
  note left_identity = slp_natural_one_sided_born_bracket_identity[
    OF R_nonnegative p_lower p_upper X_measurable X_bounded
      cutoffc_measurable qc_lp Qc_lp Qc_outside cutoffc_bound
      C_nonnegative Qc_support cutoffc_support qc_support phic_test,
    where n=n and orientation="slp_opposite_cauchy_orientation orientation"
      and tau="- tau"]
  have left_integrable: "integrable ?MJ ?left_I"
    using left_identity by (auto simp only: Let_def)
  have left_exact:
      "slp_left_born_functional n (- tau) ?phic ?Qc ?cutoffc ?qc
          (slp_opposite_cauchy_orientation orientation) =
        integral\<^sup>L ?MJ ?left_I"
    using left_identity by (auto simp only: Let_def)
  have right_amplitude: "?right_a z = cnj (?left_a z)" for z
    by (simp add:
        slp_natural_right_one_sided_weighted_amplitude_conjugate)
  have phase_conjugate:
      "exp (\<i> * of_real (tau * ?right_residual z)) =
        cnj (exp (\<i> * of_real ((- tau) * ?left_residual z)))" for z
    by (simp add: exp_cnj algebra_simps slp_left_branch_residual_def
        slp_right_branch_residual_def)
  have bracket_conjugate:
      "cnj (slp_one_sided_center_average_bracket (- tau) ?phic ?Ac
          (?output z) (?s z)) =
        - slp_one_sided_center_average_bracket tau phi ?A
          (?output z) (?s z)" for z
    using slp_one_sided_center_average_bracket_neg_conjugate[
      where tau=tau and phi=phi and A="?A" and target="?output z"
        and terminal="?s z"]
    by (simp only: A_conjugate)
  have pointwise: "?right_I z = - cnj (?left_I z)" for z
    by (simp only: phase_conjugate[of z] right_amplitude[of z]
        bracket_conjugate[of z] complex_cnj_mult;
        simp add: algebra_simps)
  have right_I_eq: "?right_I = (\<lambda>z. - cnj (?left_I z))"
    by (rule ext) (rule pointwise)
  have conjugate_integrable: "integrable ?MJ (\<lambda>z. cnj (?left_I z))"
    by (rule integrable_cnj[OF left_integrable])
  have right_integrable: "integrable ?MJ ?right_I"
    unfolding right_I_eq
    by (rule Bochner_Integration.integrable_minus[OF conjugate_integrable])
  have integral_right:
      "integral\<^sup>L ?MJ ?right_I =
        - cnj (integral\<^sup>L ?MJ ?left_I)"
  proof -
    have rewrite:
        "integral\<^sup>L ?MJ ?right_I =
          integral\<^sup>L ?MJ (\<lambda>z. - cnj (?left_I z))"
      by (simp only: right_I_eq)
    have minus:
        "integral\<^sup>L ?MJ (\<lambda>z. - cnj (?left_I z)) =
          - integral\<^sup>L ?MJ (\<lambda>z. cnj (?left_I z))"
      by (rule Bochner_Integration.integral_minus)
    have move:
        "integral\<^sup>L ?MJ (\<lambda>z. cnj (?left_I z)) =
          cnj (integral\<^sup>L ?MJ ?left_I)"
      by (rule Bochner_Integration.integral_cnj)
    show ?thesis using rewrite minus move by simp
  qed
  have right_exact:
      "slp_right_born_functional n tau phi Q cutoff q orientation =
        integral\<^sup>L ?MJ ?right_I"
    using slp_right_born_functional_eq_neg_conjugate_left[
      where n=n and tau=tau and phi=phi and root_weight=Q and cutoff=cutoff
        and potential=q and orientation=orientation]
      left_exact integral_right
    by simp
  show ?thesis
    unfolding Let_def
    using right_integrable right_exact slp_left_branch_output_eq_right
    by simp
qed

end

end
