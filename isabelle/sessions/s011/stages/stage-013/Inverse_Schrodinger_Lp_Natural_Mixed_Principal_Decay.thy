theory Inverse_Schrodinger_Lp_Natural_Mixed_Principal_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Principal_Integrability"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Mixed_Root_Quadratic_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Bracket_Integrand"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Natural residuals and the principal mixed oscillation\<close>

lemma slp_natural_branch_residual_param_measurable:
  fixes M :: "'a measure"
    and pos neg :: "'a \<Rightarrow> nat \<Rightarrow> slp_point"
    and terminal :: "'a \<Rightarrow> slp_point"
  assumes pos_measurable:
      "pos \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and neg_measurable:
      "neg \<in> measurable M (PiM {..<n} (\<lambda>_::nat. lborel))"
    and terminal_measurable: "terminal \<in> measurable M lborel"
  shows "(\<lambda>x. slp_left_branch_residual
      (map (\<lambda>j. (pos x j, neg x j)) [0..<n]) (terminal x))
    \<in> borel_measurable M"
proof -
  let ?MP = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?pairs = "\<lambda>x. map (\<lambda>j. (pos x j, neg x j)) [0..<n]"
  let ?out = "\<lambda>x. slp_left_branch_output (?pairs x) (terminal x)"
  have quadratic_compose:
    "(\<lambda>x. slp_point_quadratic_value (f x)) \<in> borel_measurable M"
    if f_borel: "f \<in> borel_measurable M" for f :: "'a \<Rightarrow> slp_point"
  proof -
    have nth[measurable]: "(\<lambda>x. f x $ i) \<in> borel_measurable M" for i :: 2
      using measurable_comp[OF f_borel borel_measurable_nth[of i]]
      by (simp only: comp_def)
    show ?thesis unfolding slp_point_quadratic_value_def by measurable
  qed
  have component: "(\<lambda>x. family x j) \<in> borel_measurable M"
    if family_measurable: "family \<in> measurable M ?MP" and j_in: "j \<in> {..<n}"
    for family j
  proof -
    have evaluation: "(\<lambda>f::nat \<Rightarrow> slp_point. f j) \<in> measurable ?MP lborel"
      by (rule measurable_component_singleton[OF j_in])
    show ?thesis using measurable_compose[OF family_measurable evaluation]
      by (simp only: measurable_lborel1)
  qed
  have sum_measurable[measurable]:
    "(\<lambda>x. \<Sum>j\<in>{..<n}.
      slp_point_quadratic_value (pos x j) - slp_point_quadratic_value (neg x j))
      \<in> borel_measurable M"
  proof (rule borel_measurable_sum)
    fix j assume j_in: "j \<in> {..<n}"
    show "(\<lambda>x. slp_point_quadratic_value (pos x j) -
      slp_point_quadratic_value (neg x j)) \<in> borel_measurable M"
      using quadratic_compose[OF component[OF pos_measurable j_in]]
        quadratic_compose[OF component[OF neg_measurable j_in]]
      by measurable
  qed
  have terminal_borel: "terminal \<in> borel_measurable M"
    using terminal_measurable by (simp only: measurable_lborel1)
  have out_map: "?out \<in> measurable M lborel"
    by (rule slp_natural_branch_output_param_measurable[
          OF pos_measurable neg_measurable terminal_measurable])
  have out_borel: "?out \<in> borel_measurable M"
    using out_map by (simp only: measurable_lborel1)
  have terminal_quadratic[measurable]:
    "(\<lambda>x. slp_point_quadratic_value (terminal x)) \<in> borel_measurable M"
    by (rule quadratic_compose[OF terminal_borel])
  have out_quadratic[measurable]:
    "(\<lambda>x. slp_point_quadratic_value (?out x)) \<in> borel_measurable M"
    by (rule quadratic_compose[OF out_borel])
  have residual_eq:
    "slp_left_branch_residual (?pairs x) (terminal x) =
      (\<Sum>j\<in>{..<n}. slp_point_quadratic_value (pos x j) -
        slp_point_quadratic_value (neg x j)) +
      slp_point_quadratic_value (terminal x) - slp_point_quadratic_value (?out x)"
    for x
    by (simp add: slp_left_branch_residual_def slp_branch_residual_def
        map_map comp_def sum_list_distinct_conv_sum_set atLeast0LessThan)
  show ?thesis by (simp only: residual_eq; measurable)
qed

theorem slp_natural_mixed_residual_integrable_decay:
  fixes n m :: nat
    and F :: "(((((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times> slp_point) \<times>
      (((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times> slp_point)) \<times>
      slp_point) \<Rightarrow> complex"
  assumes stationary: "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and F_integrable:
      "integrable (((((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel)
        \<Otimes>\<^sub>M
        (((PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M lborel))
        \<Otimes>\<^sub>M lborel) F"
  shows "let PL = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             PR = PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((((PL \<Otimes>\<^sub>M PL) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
               ((PR \<Otimes>\<^sub>M PR) \<Otimes>\<^sub>M lborel)) \<Otimes>\<^sub>M lborel);
             lp = (\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]);
             rp = (\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]);
             phase = (\<lambda>z. slp_mixed_branch_residual (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))))
    in (\<forall>omega::real. integrable MJ
         (\<lambda>z. exp (\<i> * of_real (omega * phase z)) * F z)) \<and>
       ((\<lambda>omega::real. integral\<^sup>L MJ
         (\<lambda>z. exp (\<i> * of_real (omega * phase z)) * F z)) \<longlongrightarrow> 0) at_top"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?N = "?BL \<Otimes>\<^sub>M ?BR"
  let ?MJ = "?N \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?s = "\<lambda>c. snd (fst c)"
  let ?t = "\<lambda>c. snd (snd c)"
  let ?u = "\<lambda>c. slp_left_branch_output (?lp c) (?s c)"
  let ?v = "\<lambda>c. slp_right_branch_output (?rp c) (?t c)"
  let ?phase = "\<lambda>z. slp_mixed_branch_residual (snd z)
    (?lp (fst z)) (?s (fst z)) (?rp (fst z)) (?t (fst z))"
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
  have N_sigma: "sigma_finite_measure ?N" by standard
  have left_output_map: "?u \<in> measurable ?N lborel"
    by (rule slp_natural_branch_output_param_measurable; measurable)
  have left_output_borel[measurable]: "?u \<in> borel_measurable ?N"
    using left_output_map by (simp only: measurable_lborel1)
  have right_output_map:
    "(\<lambda>c. slp_left_branch_output (?rp c) (?t c)) \<in> measurable ?N lborel"
    by (rule slp_natural_branch_output_param_measurable; measurable)
  have right_output_borel[measurable]: "?v \<in> borel_measurable ?N"
    using right_output_map
    by (simp only: measurable_lborel1 slp_left_branch_output_eq_right)
  have left_residual_borel[measurable]:
    "(\<lambda>c. slp_left_branch_residual (?lp c) (?s c)) \<in> borel_measurable ?N"
    by (rule slp_natural_branch_residual_param_measurable; measurable)
  have right_left_residual_borel:
    "(\<lambda>c. slp_left_branch_residual (?rp c) (?t c)) \<in> borel_measurable ?N"
    by (rule slp_natural_branch_residual_param_measurable; measurable)
  have right_residual_borel[measurable]:
    "(\<lambda>c. slp_right_branch_residual (?rp c) (?t c)) \<in> borel_measurable ?N"
    using right_left_residual_borel
    by (simp only: slp_left_branch_residual_def slp_right_branch_residual_def)
  have quadratic_compose:
    "(\<lambda>z. slp_point_quadratic_value (f z)) \<in> borel_measurable ?MJ"
    if f_borel: "f \<in> borel_measurable ?MJ" for f
  proof -
    have nth[measurable]: "(\<lambda>z. f z $ i) \<in> borel_measurable ?MJ" for i :: 2
      using measurable_comp[OF f_borel borel_measurable_nth[of i]]
      by (simp only: comp_def)
    show ?thesis unfolding slp_point_quadratic_value_def by measurable
  qed
  have root_quadratic[measurable]:
    "(\<lambda>z. slp_point_quadratic_value (snd z)) \<in> borel_measurable ?MJ"
    by (rule quadratic_compose; measurable)
  have left_quadratic[measurable]:
    "(\<lambda>z. slp_point_quadratic_value (?u (fst z))) \<in> borel_measurable ?MJ"
    by (rule quadratic_compose; measurable)
  have right_quadratic[measurable]:
    "(\<lambda>z. slp_point_quadratic_value (?v (fst z))) \<in> borel_measurable ?MJ"
    by (rule quadratic_compose; measurable)
  have center_quadratic[measurable]:
    "(\<lambda>z. slp_point_quadratic_value (-snd z + ?u (fst z) + ?v (fst z)))
      \<in> borel_measurable ?MJ"
    by (rule quadratic_compose; measurable)
  have phase_borel[measurable]: "?phase \<in> borel_measurable ?MJ"
    unfolding slp_mixed_branch_residual_def slp_mixed_core_residual_def by measurable
  have F_borel[measurable]: "F \<in> borel_measurable ?MJ"
    using F_integrable by measurable
  have oscillatory_integrable:
    "integrable ?MJ (\<lambda>z. exp (\<i> * of_real (omega * ?phase z)) * F z)"
    for omega :: real
  proof (rule Bochner_Integration.integrable_bound[OF F_integrable])
    show "(\<lambda>z. exp (\<i> * of_real (omega * ?phase z)) * F z)
      \<in> borel_measurable ?MJ" by measurable
    show "AE z in ?MJ. norm (exp (\<i> * of_real (omega * ?phase z)) * F z) \<le> norm (F z)"
      by (simp add: norm_mult norm_exp_i_times)
  qed
  have curried_integrable: "integrable ?MJ (case_prod (\<lambda>c x. F (c,x)))"
    using F_integrable by (simp add: case_prod_unfold)
  have curried_decay:
    "((\<lambda>omega::real. integral\<^sup>L ?MJ
      (\<lambda>(c,x). exp (\<i> * of_real (omega *
        slp_mixed_branch_residual x (?lp c) (?s c) (?rp c) (?t c))) * F (c,x)))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_mixed_branch_residual_root_decay_measure[
          OF stationary density N_sigma left_output_borel right_output_borel
            left_residual_borel right_residual_borel curried_integrable])
  have decay:
    "((\<lambda>omega::real. integral\<^sup>L ?MJ
      (\<lambda>z. exp (\<i> * of_real (omega * ?phase z)) * F z)) \<longlongrightarrow> 0) at_top"
    using curried_decay by (simp add: case_prod_unfold)
  show ?thesis unfolding Let_def using oscillatory_integrable decay by blast
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_mixed_principal_integrable_decay:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes stationary: "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
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
             PL = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             PR = PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((((PL \<Otimes>\<^sub>M PL) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
               ((PR \<Otimes>\<^sub>M PR) \<Otimes>\<^sub>M lborel)) \<Otimes>\<^sub>M lborel);
             lp = (\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]);
             rp = (\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]);
             center = (\<lambda>z. slp_mixed_branch_center (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             phase = (\<lambda>z. slp_mixed_branch_residual (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             W = (\<lambda>T U H. slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H);
             F = (\<lambda>z. W (\<lambda>s. A s - A (center z)) (\<lambda>t. B t - B (center z)) phi z)
    in integrable MJ F \<and>
       ((\<lambda>omega::real. integral\<^sup>L MJ
         (\<lambda>z. exp (\<i> * of_real (omega * phase z)) * F z)) \<longlongrightarrow> 0) at_top"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?s = "\<lambda>z. snd (fst (fst z))"
  let ?t = "\<lambda>z. snd (snd (fst z))"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?phase = "\<lambda>z. slp_mixed_branch_residual (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?W = "\<lambda>T U H. slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H"
  let ?F = "\<lambda>z. ?W (\<lambda>s. ?A s - ?A (?center z))
    (\<lambda>t. ?B t - ?B (?center z)) phi z"
  have weighted_factor:
    "?W T U H z = ?W ?one ?one ?one z * T (?s z) * U (?t z) * H (?center z)"
    for T U H z
  proof -
    have left_factor:
      "slp_left_branch_complex_kernel_list cutoff q T (?lp (fst z)) (snd z) (?s z) =
        T (?s z) * slp_left_branch_complex_kernel_list cutoff q ?one
          (?lp (fst z)) (snd z) (?s z)"
      by (rule slp_left_branch_list_terminal_factor)
    have right_factor:
      "slp_left_branch_complex_kernel_list (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (qt x)) (\<lambda>x. cnj (U x)) (?rp (fst z)) (snd z) (?t z) =
        cnj (U (?t z)) * slp_left_branch_complex_kernel_list (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (qt x)) ?one (?rp (fst z)) (snd z) (?t z)"
      by (rule slp_left_branch_list_terminal_factor)
    show ?thesis
      unfolding slp_natural_mixed_weighted_amplitude_def Let_def
      by (simp add: left_factor right_factor algebra_simps)
  qed
  have principal_expansion:
    "?F z = ?W ?A ?B phi z -
      ?W ?A ?one (\<lambda>c. phi c * ?B c) z -
      ?W ?one ?B (\<lambda>c. phi c * ?A c) z +
      ?W ?one ?one (\<lambda>c. phi c * (?A c * ?B c)) z" for z
  proof -
    note tt = weighted_factor[of ?A ?B phi z]
    note lc = weighted_factor[of ?A ?one "\<lambda>c. phi c * ?B c" z]
    note rc = weighted_factor[of ?one ?B "\<lambda>c. phi c * ?A c" z]
    note uu = weighted_factor[of ?one ?one "\<lambda>c. phi c * (?A c * ?B c)" z]
    note principal = weighted_factor[of "\<lambda>s. ?A s - ?A (?center z)"
      "\<lambda>t. ?B t - ?B (?center z)" phi z]
    show ?thesis by (simp only: tt lc rc uu principal; simp add: algebra_simps)
  qed
  note components = slp_natural_mixed_principal_components_integrable[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
      cutoff_support q_support qt_support phi_test, where n=n and m=m and lo=lo and ro=ro]
  have tt: "integrable ?MJ (?W ?A ?B phi)"
    using components by (auto simp only: Let_def)
  have lc: "integrable ?MJ (?W ?A ?one (\<lambda>c. phi c * ?B c))"
    using components by (auto simp only: Let_def)
  have rc: "integrable ?MJ (?W ?one ?B (\<lambda>c. phi c * ?A c))"
    using components by (auto simp only: Let_def)
  have uu: "integrable ?MJ (?W ?one ?one (\<lambda>c. phi c * (?A c * ?B c)))"
    using components by (auto simp only: Let_def)
  have F_integrable: "integrable ?MJ ?F"
    unfolding principal_expansion
    by (rule Bochner_Integration.integrable_add[
          OF Bochner_Integration.integrable_diff[
            OF Bochner_Integration.integrable_diff[OF tt lc] rc] uu])
  have decay:
    "((\<lambda>omega::real. integral\<^sup>L ?MJ
      (\<lambda>z. exp (\<i> * of_real (omega * ?phase z)) * ?F z)) \<longlongrightarrow> 0) at_top"
    using slp_natural_mixed_residual_integrable_decay[
      OF stationary density F_integrable]
    by (auto simp only: Let_def)
  show ?thesis unfolding Let_def using F_integrable decay by blast
qed

end

end
