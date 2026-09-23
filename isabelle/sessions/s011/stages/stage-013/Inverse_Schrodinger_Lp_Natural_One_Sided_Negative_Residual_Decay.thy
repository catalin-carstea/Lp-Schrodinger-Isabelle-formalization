theory Inverse_Schrodinger_Lp_Natural_One_Sided_Negative_Residual_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Positive_Principal_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Active_Phase_Sign"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Negative-frequency decay on the original natural carrier\<close>

theorem slp_natural_one_sided_negative_residual_decay:
  fixes n :: nat
    and F :: "((((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
      slp_point) \<times> slp_point) \<Rightarrow> complex"
  assumes stationary:
      "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and F_integrable:
      "integrable
        ((((PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
          (PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))))
            \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel) F"
  shows "let P = PiM {..<Suc n}
                  (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((P \<Otimes>\<^sub>M P) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel;
             ps = (\<lambda>z. map (\<lambda>k.
               (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<Suc n]);
             residual = (\<lambda>z.
               slp_left_branch_residual (ps z) (snd (fst z)))
    in ((\<lambda>omega::real. integral\<^sup>L MJ
      (\<lambda>z. exp (\<i> * of_real ((- omega) * residual z)) * F z))
        \<longlongrightarrow> 0) at_top"
proof -
  let ?L = "lborel :: slp_point measure"
  let ?Tail = "PiM {1..<Suc n} (\<lambda>_::nat. ?L)"
  let ?Full = "PiM {..<Suc n} (\<lambda>_::nat. ?L)"
  let ?Rcarrier = "?L \<Otimes>\<^sub>M ?L"
  let ?Source = "?L \<Otimes>\<^sub>M ?Tail"
  let ?M = "?Tail \<Otimes>\<^sub>M (?Rcarrier \<Otimes>\<^sub>M ?Source)"
  let ?Original = "((?Full \<Otimes>\<^sub>M ?Full) \<Otimes>\<^sub>M ?L) \<Otimes>\<^sub>M ?L"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<Suc n]"
  let ?residual = "\<lambda>z. slp_left_branch_residual (?ps z) (snd (fst z))"
  let ?neg_tail = "\<lambda>c. fst c"
  let ?terminal = "\<lambda>c. fst (fst (snd c))"
  let ?root = "\<lambda>c. snd (fst (snd c))"
  let ?lam = "\<lambda>c. fst (snd (snd c))"
  let ?pos_tail = "\<lambda>c. snd (snd (snd c))"
  let ?pack = "\<lambda>c eta.
    ((((?pos_tail c)(0 := ?lam c), (?neg_tail c)(0 := eta)), ?terminal c), ?root c)"
  let ?pairs = "\<lambda>c. map (\<lambda>k.
    (?pos_tail c (Suc k), ?neg_tail c (Suc k))) [0..<n]"
  let ?G = "\<lambda>c eta. F (?pack c eta)"
  have L_sigma: "sigma_finite_measure ?L" by standard
  interpret L: sigma_finite_measure ?L by (rule L_sigma)
  interpret natural: product_sigma_finite
    "(\<lambda>_::nat. (lborel :: slp_point measure))" by standard
  have Tail_sigma: "sigma_finite_measure ?Tail"
    by (rule natural.sigma_finite) simp
  have R_sigma: "sigma_finite_measure ?Rcarrier"
    by (rule sigma_finite_pair_measure[OF L_sigma L_sigma])
  have Source_sigma: "sigma_finite_measure ?Source"
    by (rule sigma_finite_pair_measure[OF L_sigma Tail_sigma])
  have R_Source_sigma: "sigma_finite_measure (?Rcarrier \<Otimes>\<^sub>M ?Source)"
    by (rule sigma_finite_pair_measure[OF R_sigma Source_sigma])
  have M_sigma: "sigma_finite_measure ?M"
    by (rule sigma_finite_pair_measure[OF Tail_sigma R_Source_sigma])
  have neg_tail_measurable: "?neg_tail \<in> measurable ?M ?Tail"
    by measurable
  have pos_tail_measurable: "?pos_tail \<in> measurable ?M ?Tail"
    by measurable
  have lam_measurable: "?lam \<in> borel_measurable ?M"
    by measurable
  have terminal_map: "?terminal \<in> measurable ?M ?L"
    by measurable
  have terminal_measurable: "?terminal \<in> borel_measurable ?M"
    using terminal_map by (simp only: measurable_lborel1)
  have pos_component:
    "(\<lambda>c. ?pos_tail c k) \<in> borel_measurable ?M"
    if k_in: "k \<in> {1..<Suc n}" for k
  proof -
    have evaluation:
      "(\<lambda>f::nat \<Rightarrow> slp_point. f k) \<in> measurable ?Tail ?L"
      by (rule measurable_component_singleton[OF k_in])
    show ?thesis
      using measurable_compose[OF pos_tail_measurable evaluation]
      by (simp only: measurable_lborel1 comp_def)
  qed
  have neg_component:
    "(\<lambda>c. ?neg_tail c k) \<in> borel_measurable ?M"
    if k_in: "k \<in> {1..<Suc n}" for k
  proof -
    have evaluation:
      "(\<lambda>f::nat \<Rightarrow> slp_point. f k) \<in> measurable ?Tail ?L"
      by (rule measurable_component_singleton[OF k_in])
    show ?thesis
      using measurable_compose[OF neg_tail_measurable evaluation]
      by (simp only: measurable_lborel1 comp_def)
  qed
  have output_tail_eq:
    "slp_left_branch_output (?pairs c) (?terminal c) =
      ?terminal c + (\<Sum>k\<in>{..<n}.
        ?pos_tail c (Suc k) - ?neg_tail c (Suc k))" for c
    by (simp add: slp_left_branch_output_def slp_branch_increment_def
        map_map comp_def sum_list_distinct_conv_sum_set atLeast0LessThan)
  have increment_measurable[measurable]:
    "(\<lambda>c. \<Sum>k\<in>{..<n}.
      ?pos_tail c (Suc k) - ?neg_tail c (Suc k))
      \<in> borel_measurable ?M"
  proof (rule borel_measurable_sum)
    fix k assume k_in: "k \<in> {..<n}"
    have shifted_in: "Suc k \<in> {1..<Suc n}" using k_in by auto
    show "(\<lambda>c. ?pos_tail c (Suc k) - ?neg_tail c (Suc k))
      \<in> borel_measurable ?M"
      using pos_component[OF shifted_in] neg_component[OF shifted_in] by measurable
  qed
  have output_measurable:
    "(\<lambda>c. slp_left_branch_output (?pairs c) (?terminal c))
      \<in> borel_measurable ?M"
    by (simp only: output_tail_eq; measurable)
  have quadratic_compose:
    "(\<lambda>c. slp_point_quadratic_value (f c)) \<in> borel_measurable ?M"
    if f_measurable: "f \<in> borel_measurable ?M"
    for f :: "_ \<Rightarrow> slp_point"
  proof -
    have nth[measurable]: "(\<lambda>c. f c $ i) \<in> borel_measurable ?M" for i :: 2
      using measurable_comp[OF f_measurable borel_measurable_nth[of i]]
      by (simp only: comp_def)
    show ?thesis unfolding slp_point_quadratic_value_def by measurable
  qed
  have quadratic_sum_measurable[measurable]:
    "(\<lambda>c. \<Sum>k\<in>{..<n}.
      slp_point_quadratic_value (?pos_tail c (Suc k)) -
      slp_point_quadratic_value (?neg_tail c (Suc k))) \<in> borel_measurable ?M"
  proof (rule borel_measurable_sum)
    fix k assume k_in: "k \<in> {..<n}"
    have shifted_in: "Suc k \<in> {1..<Suc n}" using k_in by auto
    show "(\<lambda>c. slp_point_quadratic_value (?pos_tail c (Suc k)) -
      slp_point_quadratic_value (?neg_tail c (Suc k))) \<in> borel_measurable ?M"
      using quadratic_compose[OF pos_component[OF shifted_in]]
        quadratic_compose[OF neg_component[OF shifted_in]] by measurable
  qed
  have residual_tail_eq:
    "slp_left_branch_residual (?pairs c) (?terminal c) =
      (\<Sum>k\<in>{..<n}.
        slp_point_quadratic_value (?pos_tail c (Suc k)) -
        slp_point_quadratic_value (?neg_tail c (Suc k))) +
      slp_point_quadratic_value (?terminal c) -
      slp_point_quadratic_value
        (slp_left_branch_output (?pairs c) (?terminal c))" for c
    by (simp add: slp_left_branch_residual_def slp_branch_residual_def
        map_map comp_def sum_list_distinct_conv_sum_set atLeast0LessThan)
  have terminal_quadratic_measurable[measurable]:
    "(\<lambda>c. slp_point_quadratic_value (?terminal c))
      \<in> borel_measurable ?M"
    by (rule quadratic_compose[OF terminal_measurable])
  have output_quadratic_measurable[measurable]:
    "(\<lambda>c. slp_point_quadratic_value
      (slp_left_branch_output (?pairs c) (?terminal c)))
      \<in> borel_measurable ?M"
    by (rule quadratic_compose[OF output_measurable])
  have residual_measurable:
    "(\<lambda>c. slp_left_branch_residual (?pairs c) (?terminal c))
      \<in> borel_measurable ?M"
    by (simp only: residual_tail_eq; measurable)
  have interval_list: "0 # map Suc [0..<n] = [0..<Suc n]"
    by (induction n) simp_all
  have pack_pairs:
    "?ps (?pack c eta) = (?lam c, eta) # ?pairs c" for c eta
  proof -
    show ?thesis
      by (subst interval_list[symmetric]) simp
  qed
  have residual_pack:
    "?residual (?pack c eta) =
      slp_left_branch_residual ((?lam c, eta) # ?pairs c) (?terminal c)"
    for c eta
    using pack_pairs[of c eta]
    by (simp only: prod.sel)
  have active_integrable:
    "integrable (?M \<Otimes>\<^sub>M ?L) (case_prod ?G)"
  proof -
    note transported = slp_natural_pair_heads_negative_active_transport[
      OF F_integrable]
    show ?thesis
      using transported by (simp only: Let_def split_beta' prod.sel)
  qed
  have active_decay:
    "((\<lambda>omega::real. integral\<^sup>L (?M \<Otimes>\<^sub>M ?L)
      (\<lambda>(c,eta). exp (\<i> * of_real ((- omega) *
        slp_left_branch_residual ((?lam c, eta) # ?pairs c) (?terminal c))) *
        ?G c eta)) \<longlongrightarrow> 0) at_top"
    by (rule slp_left_branch_residual_first_negative_decay_measure_sign[
      OF stationary density M_sigma lam_measurable output_measurable
        residual_measurable active_integrable])
  have original_residual_measurable:
    "?residual \<in> borel_measurable ?Original"
    by (rule slp_natural_branch_residual_param_measurable; measurable)
  have F_measurable: "F \<in> borel_measurable ?Original"
    using F_integrable by measurable
  have original_integrable:
    "integrable ?Original
      (\<lambda>z. exp (\<i> * of_real ((- omega) * ?residual z)) * F z)"
    for omega :: real
  proof (rule Bochner_Integration.integrable_bound[OF F_integrable])
    show "(\<lambda>z. exp (\<i> * of_real ((- omega) * ?residual z)) * F z)
      \<in> borel_measurable ?Original"
      using original_residual_measurable F_measurable by measurable
    show "AE z in ?Original.
      norm (exp (\<i> * of_real ((- omega) * ?residual z)) * F z)
        \<le> norm (F z)"
      by (simp add: norm_mult norm_exp_i_times)
  qed
  have integral_transport:
    "integral\<^sup>L ?Original
        (\<lambda>z. exp (\<i> * of_real ((- omega) * ?residual z)) * F z) =
      integral\<^sup>L (?M \<Otimes>\<^sub>M ?L)
        (\<lambda>(c,eta). exp (\<i> * of_real ((- omega) *
          slp_left_branch_residual ((?lam c, eta) # ?pairs c) (?terminal c))) *
          ?G c eta)" for omega
  proof -
    note transported = slp_natural_pair_heads_negative_active_transport[
      OF original_integrable[of omega]]
    have raw:
      "integral\<^sup>L ?Original
          (\<lambda>z. exp (\<i> * of_real ((- omega) * ?residual z)) * F z) =
        integral\<^sup>L (?M \<Otimes>\<^sub>M ?L)
          (\<lambda>(c,eta). exp (\<i> * of_real ((- omega) *
            ?residual (?pack c eta))) * F (?pack c eta))"
      using transported by (simp only: Let_def split_beta' prod.sel)
    show ?thesis
      using raw by (simp only: residual_pack)
  qed
  have function_eq:
    "(\<lambda>omega::real. integral\<^sup>L ?Original
      (\<lambda>z. exp (\<i> * of_real ((- omega) * ?residual z)) * F z)) =
     (\<lambda>omega::real. integral\<^sup>L (?M \<Otimes>\<^sub>M ?L)
      (\<lambda>(c,eta). exp (\<i> * of_real ((- omega) *
        slp_left_branch_residual ((?lam c, eta) # ?pairs c) (?terminal c))) *
        ?G c eta))"
    by (rule ext) (rule integral_transport)
  show ?thesis
    unfolding Let_def
    using active_decay function_eq by simp
qed

end
