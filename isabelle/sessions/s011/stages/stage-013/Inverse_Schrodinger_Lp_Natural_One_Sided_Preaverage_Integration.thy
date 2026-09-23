theory Inverse_Schrodinger_Lp_Natural_One_Sided_Preaverage_Integration
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Raw_Amplitudes"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Natural one-sided preaverage integration\<close>

definition slp_one_sided_center_average_bracket ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_one_sided_center_average_bracket tau phi A output terminal =
    A terminal * slp_center_average tau phi output -
      slp_center_average tau (\<lambda>u. phi u * A u) output"

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_one_sided_fixed_preaverage_integrable:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
    and tau :: real and y :: slp_point
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
  shows "let P = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((P \<Otimes>\<^sub>M P) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel;
             ps = (\<lambda>z. map (\<lambda>k. (fst (fst (fst z)) k,
               snd (fst (fst z)) k)) [0..<n]);
             s = (\<lambda>z. snd (fst z));
             output = (\<lambda>z. slp_left_branch_output (ps z) (s z));
             phase = (\<lambda>z. slp_left_branch_residual (ps z) (s z));
             A = slp_cauchy_transform orientation q;
             a = slp_natural_one_sided_weighted_amplitude n Q cutoff q
               (\<lambda>_. 1) (\<lambda>_. 1);
             F = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_center_kernel tau (output z) y * (A (s z) - A y))
    in integrable MJ F"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  let ?s = "\<lambda>z. snd (fst z)"
  let ?output = "\<lambda>z. slp_left_branch_output (?ps z) (?s z)"
  let ?phase = "\<lambda>z. slp_left_branch_residual (?ps z) (?s z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?W = "\<lambda>T. slp_natural_one_sided_weighted_amplitude n Q cutoff q T ?one"
  let ?a = "?W ?one"
  let ?e = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z))"
  let ?F = "\<lambda>z. ?e z * ?a z * slp_center_kernel tau (?output z) y *
    (?A (?s z) - ?A y)"
  let ?D = "\<lambda>z. ?W ?A z - ?A y * ?a z"
  note raw = slp_natural_one_sided_raw_amplitudes_integrable[
    OF R_nonnegative p_lower p_upper X_measurable X_bounded cutoff_measurable
      q_lp Q_lp Q_outside cutoff_bound C_nonnegative Q_support cutoff_support
      q_support, where n=n and orientation=orientation]
  have rawA: "integrable ?MJ (?W ?A)"
    using raw by (auto simp only: Let_def)
  have raw1: "integrable ?MJ ?a"
    using raw by (auto simp only: Let_def)
  have raw_factor: "?W T z = ?a z * T (?s z)" for T z
    using slp_natural_one_sided_amplitude_terminal_factor[
      where n=n and Q=Q and cutoff=cutoff and q=q and T=T and H="?one" and z=z]
    by (simp only: Let_def mult_1_right)
  have D_integrable: "integrable ?MJ ?D"
    by (intro Bochner_Integration.integrable_diff rawA
      Bochner_Integration.integrable_mult_right raw1)
  have D_borel[measurable]: "?D \<in> borel_measurable ?MJ"
    using D_integrable by measurable
  have output_map: "?output \<in> measurable ?MJ lborel"
    by (rule slp_natural_branch_output_param_measurable; measurable)
  have output_borel[measurable]: "?output \<in> borel_measurable ?MJ"
    using output_map by (simp only: measurable_lborel1)
  have phase_borel[measurable]: "?phase \<in> borel_measurable ?MJ"
    by (rule slp_natural_branch_residual_param_measurable; measurable)
  have output_nth[measurable]:
    "(\<lambda>z. ?output z $ i) \<in> borel_measurable ?MJ" for i :: 2
    using measurable_comp[OF output_borel borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have kernel_borel[measurable]:
    "(\<lambda>z. slp_center_kernel tau (?output z) y) \<in> borel_measurable ?MJ"
    unfolding slp_center_kernel_def slp_center_phase_def by measurable
  have phased:
      "integrable ?MJ (\<lambda>z. ?e z * slp_center_kernel tau (?output z) y * ?D z)"
  proof (rule Bochner_Integration.integrable_bound[OF D_integrable])
    show "(\<lambda>z. ?e z * slp_center_kernel tau (?output z) y * ?D z)
        \<in> borel_measurable ?MJ"
      by measurable
    show "AE z in ?MJ. norm (?e z * slp_center_kernel tau (?output z) y * ?D z)
        \<le> norm (?D z)"
      by (simp add: norm_mult norm_exp_i_times)
  qed
  have expansion:
      "?F z = ?e z * slp_center_kernel tau (?output z) y * ?D z" for z
    using raw_factor[of ?A z]
    by (simp add: algebra_simps)
  show ?thesis unfolding Let_def using phased by (simp only: expansion)
qed

theorem slp_natural_one_sided_preaverage_fubini:
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
             output = (\<lambda>z. slp_left_branch_output (ps z) (s z));
             phase = (\<lambda>z. slp_left_branch_residual (ps z) (s z));
             A = slp_cauchy_transform orientation q;
             a = slp_natural_one_sided_weighted_amplitude n Q cutoff q
               (\<lambda>_. 1) (\<lambda>_. 1);
             F = (\<lambda>z y. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_center_kernel tau (output z) y * (A (s z) - A y));
             G = (\<lambda>z y. F z y * phi y);
             I = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_one_sided_center_average_bracket tau phi A (output z) (s z))
    in (\<forall>y. integrable MJ (\<lambda>z. F z y)) \<and>
       integrable (MJ \<Otimes>\<^sub>M lborel) (case_prod G) \<and>
       integrable MJ I \<and>
       integrable lborel (\<lambda>y. integral\<^sup>L MJ (\<lambda>z. G z y)) \<and>
       of_real (tau / pi) * integral\<^sup>L lborel
         (\<lambda>y. integral\<^sup>L MJ (\<lambda>z. G z y)) = integral\<^sup>L MJ I"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MY = "?MJ \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  let ?s = "\<lambda>z. snd (fst z)"
  let ?output = "\<lambda>z. slp_left_branch_output (?ps z) (?s z)"
  let ?phase = "\<lambda>z. slp_left_branch_residual (?ps z) (?s z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?W = "\<lambda>T. slp_natural_one_sided_weighted_amplitude n Q cutoff q T ?one"
  let ?a = "?W ?one"
  let ?e = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z))"
  let ?F = "\<lambda>z y. ?e z * ?a z * slp_center_kernel tau (?output z) y *
    (?A (?s z) - ?A y)"
  let ?G = "\<lambda>z y. ?F z y * phi y"
  let ?I = "\<lambda>z. ?e z * ?a z *
    slp_one_sided_center_average_bracket tau phi ?A (?output z) (?s z)"
  let ?scale = "of_real (tau / pi) :: complex"
  let ?Tensor = "\<lambda>w h z y. ?e z * w z *
    slp_center_kernel tau (?output z) y * h y"
  note raw = slp_natural_one_sided_raw_amplitudes_integrable[
    OF R_nonnegative p_lower p_upper X_measurable X_bounded cutoff_measurable
      q_lp Q_lp Q_outside cutoff_bound C_nonnegative Q_support cutoff_support
      q_support, where n=n and orientation=orientation]
  have rawA: "integrable ?MJ (?W ?A)"
    using raw by (auto simp only: Let_def)
  have raw1: "integrable ?MJ ?a"
    using raw by (auto simp only: Let_def)
  have raw_factor: "?W T z = ?a z * T (?s z)" for T z
    using slp_natural_one_sided_amplitude_terminal_factor[
      where n=n and Q=Q and cutoff=cutoff and q=q and T=T and H="?one" and z=z]
    by (simp only: Let_def mult_1_right)
  have output_map: "?output \<in> measurable ?MJ lborel"
    by (rule slp_natural_branch_output_param_measurable; measurable)
  have output_borel[measurable]: "?output \<in> borel_measurable ?MJ"
    using output_map by (simp only: measurable_lborel1)
  have phase_borel[measurable]: "?phase \<in> borel_measurable ?MJ"
    by (rule slp_natural_branch_residual_param_measurable; measurable)
  have phi0: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi1: "integrable lborel (\<lambda>y. phi y * ?A y)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have center_lift: "(\<lambda>zy. ?output (fst zy)) \<in> borel_measurable ?MY"
    by measurable
  have target_lift: "snd \<in> borel_measurable ?MY" by measurable
  have center_nth[measurable]:
    "(\<lambda>zy. ?output (fst zy) $ i) \<in> borel_measurable ?MY" for i :: 2
    using measurable_comp[OF center_lift borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have target_nth[measurable]:
    "(\<lambda>zy. snd zy $ i) \<in> borel_measurable ?MY" for i :: 2
    using measurable_comp[OF target_lift borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have kernel_joint_borel[measurable]:
    "(\<lambda>zy. slp_center_kernel tau (?output (fst zy)) (snd zy))
      \<in> borel_measurable ?MY"
    unfolding slp_center_kernel_def slp_center_phase_def by measurable
  interpret natural_product: product_sigma_finite
    "(\<lambda>_::nat. (lborel :: slp_point measure))" by standard
  interpret family: sigma_finite_measure ?P
    by (rule natural_product.sigma_finite) simp
  interpret arrays: pair_sigma_finite ?P ?P ..
  interpret array_measure: sigma_finite_measure "(?P \<Otimes>\<^sub>M ?P)" by standard
  interpret coordinates: pair_sigma_finite
    "(?P \<Otimes>\<^sub>M ?P)" "(lborel :: slp_point measure)" ..
  interpret branch_measure: sigma_finite_measure ?B by standard
  interpret joint: pair_sigma_finite ?B "(lborel :: slp_point measure)" ..
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
  let ?P0 = "?Tensor (?W ?A) phi"
  let ?P1 = "?Tensor ?a (\<lambda>y. phi y * ?A y)"
  have P0: "integrable ?MY (case_prod ?P0)"
    by (rule product_integrable[OF rawA phi0])
  have P1: "integrable ?MY (case_prod ?P1)"
    by (rule product_integrable[OF raw1 phi1])
  have combined:
      "integrable ?MY (\<lambda>zy. ?P0 (fst zy) (snd zy) -
        ?P1 (fst zy) (snd zy))"
    using P0 P1 unfolding case_prod_unfold
    by (intro Bochner_Integration.integrable_diff)
  have expansion: "?G z y = ?P0 z y - ?P1 z y" for z y
    using raw_factor[of ?A z]
    by (simp add: algebra_simps)
  have G_integrable: "integrable ?MY (case_prod ?G)"
    using combined by (simp only: case_prod_unfold expansion)
  have fixed_integrable: "integrable ?MJ (\<lambda>z. ?F z y)" for y
    using slp_natural_one_sided_fixed_preaverage_integrable[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        Q_support cutoff_support q_support,
      where n=n and orientation=orientation and tau=tau and y=y]
    by (auto simp only: Let_def)
  have inner_identity: "?I z = ?scale * integral\<^sup>L lborel (?G z)" for z
  proof -
    let ?K0 = "\<lambda>y. slp_center_kernel tau (?output z) y * phi y"
    let ?K1 = "\<lambda>y. slp_center_kernel tau (?output z) y * (phi y * ?A y)"
    have K0: "integrable lborel ?K0"
      by (rule slp_center_kernel_integrable_mult[OF phi0])
    have K1: "integrable lborel ?K1"
      by (rule slp_center_kernel_integrable_mult[OF phi1])
    have difference: "integrable lborel (\<lambda>y. ?A (?s z) * ?K0 y - ?K1 y)"
      by (intro Bochner_Integration.integrable_diff
        Bochner_Integration.integrable_mult_right K0 K1)
    have pointwise:
        "slp_center_kernel tau (?output z) y * phi y * (?A (?s z) - ?A y) =
          ?A (?s z) * ?K0 y - ?K1 y" for y
      by (simp add: algebra_simps)
    have scalar:
        "slp_one_sided_center_average_bracket tau phi ?A (?output z) (?s z) =
          ?scale * integral\<^sup>L lborel
            (\<lambda>y. slp_center_kernel tau (?output z) y * phi y *
              (?A (?s z) - ?A y))"
      unfolding slp_one_sided_center_average_bracket_def slp_center_average_def
      by (simp only: pointwise Bochner_Integration.integral_diff[OF
            Bochner_Integration.integrable_mult_right[OF K0] K1]
          Bochner_Integration.integral_mult_right_zero; simp add: algebra_simps)
    have factor:
        "?G z y = (?e z * ?a z) *
          (slp_center_kernel tau (?output z) y * phi y *
            (?A (?s z) - ?A y))" for y
      by (simp add: algebra_simps)
    show ?thesis
      by (simp only: factor scalar Bochner_Integration.integral_mult_right_zero;
        simp only: mult_ac)
  qed
  have I_integrable: "integrable ?MJ ?I"
    unfolding inner_identity
    by (intro Bochner_Integration.integrable_mult_right
      averaging.integrable_fst[OF G_integrable])
  have outer_integrable:
      "integrable lborel (\<lambda>y. integral\<^sup>L ?MJ (\<lambda>z. ?G z y))"
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
