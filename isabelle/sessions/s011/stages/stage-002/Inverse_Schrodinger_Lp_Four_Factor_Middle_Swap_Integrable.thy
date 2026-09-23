theory Inverse_Schrodinger_Lp_Four_Factor_Middle_Swap_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Complex_Integral_Insert_Rev"
begin

section \<open>Integrability under a four-factor middle swap\<close>

theorem slp_integrable_four_factor_middle_swap:
  fixes M1 :: "'a measure" and M2 :: "'b measure"
    and M3 :: "'c measure" and M4 :: "'d measure"
    and f :: "(('a \<times> 'b) \<times> ('c \<times> 'd)) \<Rightarrow>
      'e::{banach, second_countable_topology}"
  assumes sigma1: "sigma_finite_measure M1"
    and sigma2: "sigma_finite_measure M2"
    and sigma3: "sigma_finite_measure M3"
    and sigma4: "sigma_finite_measure M4"
    and f_integrable:
      "integrable ((M1 \<Otimes>\<^sub>M M2) \<Otimes>\<^sub>M (M3 \<Otimes>\<^sub>M M4)) f"
  shows
    "integrable ((M1 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M (M2 \<Otimes>\<^sub>M M4))
      (\<lambda>((a, c), (b, d)). f ((a, b), (c, d)))"
proof -
  let ?S = "(M1 \<Otimes>\<^sub>M M2) \<Otimes>\<^sub>M (M3 \<Otimes>\<^sub>M M4)"
  let ?T = "(M1 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M (M2 \<Otimes>\<^sub>M M4)"
  let ?q = "\<lambda>((a, c), (b, d)). f ((a, b), (c, d))"
  let ?N = "\<lambda>a b c d. ennreal (norm (f ((a, b), (c, d))))"
  interpret M1: sigma_finite_measure M1 by (rule sigma1)
  interpret M2: sigma_finite_measure M2 by (rule sigma2)
  interpret M3: sigma_finite_measure M3 by (rule sigma3)
  interpret M4: sigma_finite_measure M4 by (rule sigma4)
  interpret M12: pair_sigma_finite M1 M2 ..
  interpret M13: pair_sigma_finite M1 M3 ..
  interpret M23: pair_sigma_finite M2 M3 ..
  interpret M24: pair_sigma_finite M2 M4 ..
  interpret M34: pair_sigma_finite M3 M4 ..
  interpret S: pair_sigma_finite "M1 \<Otimes>\<^sub>M M2" "M3 \<Otimes>\<^sub>M M4" ..
  interpret T: pair_sigma_finite "M1 \<Otimes>\<^sub>M M3" "M2 \<Otimes>\<^sub>M M4" ..
  have f_measurable: "f \<in> borel_measurable ?S"
    using f_integrable by simp
  have shuffle_measurable:
      "(\<lambda>((a, c), (b, d)). ((a, b), (c, d)))
        \<in> measurable ?T ?S"
  proof -
    have raw:
        "(\<lambda>x. ((fst (fst x), fst (snd x)),
          (snd (fst x), snd (snd x)))) \<in> measurable ?T ?S"
      by measurable
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have q_measurable: "?q \<in> borel_measurable ?T"
    using measurable_compose[OF shuffle_measurable f_measurable]
    by (simp only: comp_def split_beta')
  have q_norm_measurable:
      "(\<lambda>x. ennreal (norm (?q x))) \<in> borel_measurable ?T"
    using q_measurable by measurable
  have f_norm_measurable:
      "(\<lambda>x. ennreal (norm (f x))) \<in> borel_measurable ?S"
    using f_measurable by measurable
  have middle_swap:
      "(\<integral>\<^sup>+c. \<integral>\<^sup>+b. \<integral>\<^sup>+d. ?N a b c d
          \<partial>M4 \<partial>M2 \<partial>M3) =
        (\<integral>\<^sup>+b. \<integral>\<^sup>+c. \<integral>\<^sup>+d. ?N a b c d
          \<partial>M4 \<partial>M3 \<partial>M2)"
    if a_space: "a \<in> space M1" for a
  proof -
    have joint_measurable:
        "case_prod (\<lambda>b c. \<integral>\<^sup>+d. ?N a b c d \<partial>M4)
          \<in> borel_measurable (M2 \<Otimes>\<^sub>M M3)"
    proof -
      have raw:
          "(\<lambda>((b, c), d). ?N a b c d)
            \<in> borel_measurable ((M2 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M M4)"
      proof -
        have map_measurable:
            "(\<lambda>((b, c), d). ((a, b), (c, d)))
              \<in> measurable ((M2 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M M4) ?S"
        proof -
          have left:
              "(\<lambda>x. (a, fst (fst x)))
                \<in> measurable ((M2 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M M4)
                  (M1 \<Otimes>\<^sub>M M2)"
            using a_space by measurable
          have right:
              "(\<lambda>x. (snd (fst x), snd x))
                \<in> measurable ((M2 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M M4)
                  (M3 \<Otimes>\<^sub>M M4)"
            by measurable
          note raw = measurable_Pair[OF left right]
          show ?thesis
            using raw by (simp only: split_beta')
        qed
        have composed:
            "(\<lambda>x. ennreal (norm (f x))) \<circ>
                (\<lambda>((b, c), d). ((a, b), (c, d)))
              \<in> borel_measurable ((M2 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M M4)"
          by (rule measurable_comp[OF map_measurable f_norm_measurable])
        show ?thesis
          using composed by (simp only: comp_def split_beta')
      qed
      note integrated = M4.borel_measurable_nn_integral_fst[OF raw]
      have presentation:
          "(\<lambda>x. \<integral>\<^sup>+d.
              (\<lambda>((b, c), d). ?N a b c d) (x, d) \<partial>M4) =
            case_prod (\<lambda>b c. \<integral>\<^sup>+d. ?N a b c d \<partial>M4)"
        by (rule ext) (auto split: prod.split)
      show ?thesis
        using integrated unfolding presentation .
    qed
    show ?thesis
      using M23.Fubini'[OF joint_measurable]
      by simp
  qed
  have mass_equality:
      "integral\<^sup>N ?T (\<lambda>x. ennreal (norm (?q x))) =
        integral\<^sup>N ?S (\<lambda>x. ennreal (norm (f x)))"
  proof -
    let ?SO = "\<lambda>ab. integral\<^sup>N (M3 \<Otimes>\<^sub>M M4)
      (\<lambda>cd. ennreal (norm (f (ab, cd))))"
    let ?TO = "\<lambda>ac. integral\<^sup>N (M2 \<Otimes>\<^sub>M M4)
      (\<lambda>bd. ennreal (norm (?q (ac, bd))))"
    have SO_measurable:
        "?SO \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
      by (rule M34.borel_measurable_nn_integral_fst[OF
            f_norm_measurable])
    have TO_measurable:
        "?TO \<in> borel_measurable (M1 \<Otimes>\<^sub>M M3)"
      by (rule M24.borel_measurable_nn_integral_fst[OF
            q_norm_measurable])
    have source_section:
        "?SO (a, b) =
          (\<integral>\<^sup>+c. \<integral>\<^sup>+d. ?N a b c d \<partial>M4 \<partial>M3)"
      if a_space: "a \<in> space M1" and b_space: "b \<in> space M2"
      for a b
    proof -
      have ab_space: "(a, b) \<in> space (M1 \<Otimes>\<^sub>M M2)"
      proof -
        have pair_mem: "(a, b) \<in> space M1 \<times> space M2"
          using a_space b_space by blast
        show ?thesis
          by (subst space_pair_measure, rule pair_mem)
      qed
      have section_measurable:
          "(\<lambda>(c, d). ?N a b c d)
            \<in> borel_measurable (M3 \<Otimes>\<^sub>M M4)"
      proof -
        note raw = measurable_compose_Pair1[OF ab_space f_norm_measurable]
        have presentation:
            "(\<lambda>y. ennreal (norm (f ((a, b), y)))) =
              (\<lambda>(c, d). ?N a b c d)"
          by (rule ext) (auto split: prod.split)
        show ?thesis
          using raw unfolding presentation .
      qed
      note raw = M4.nn_integral_fst[OF section_measurable, symmetric]
      have left_presentation:
          "(\<lambda>(c, d). ?N a b c d) =
            (\<lambda>cd. ennreal (norm (f ((a, b), cd))))"
        by (rule ext) (auto split: prod.split)
      have right_presentation:
          "(\<lambda>x. \<integral>\<^sup>+y.
              (case (x, y) of (c, d) \<Rightarrow> ?N a b c d) \<partial>M4) =
            (\<lambda>c. \<integral>\<^sup>+d. ?N a b c d \<partial>M4)"
        by (rule ext) simp
      show ?thesis
        using raw unfolding left_presentation right_presentation .
    qed
    have target_section:
        "?TO (a, c) =
          (\<integral>\<^sup>+b. \<integral>\<^sup>+d. ?N a b c d \<partial>M4 \<partial>M2)"
      if a_space: "a \<in> space M1" and c_space: "c \<in> space M3"
      for a c
    proof -
      have ac_space: "(a, c) \<in> space (M1 \<Otimes>\<^sub>M M3)"
      proof -
        have pair_mem: "(a, c) \<in> space M1 \<times> space M3"
          using a_space c_space by blast
        show ?thesis
          by (subst space_pair_measure, rule pair_mem)
      qed
      have section_measurable:
          "(\<lambda>(b, d). ennreal (norm (?q ((a, c), (b, d)))))
            \<in> borel_measurable (M2 \<Otimes>\<^sub>M M4)"
      proof -
        note raw = measurable_compose_Pair1[OF ac_space q_norm_measurable]
        have presentation:
            "(\<lambda>y. ennreal (norm (?q ((a, c), y)))) =
              (\<lambda>(b, d). ennreal (norm (?q ((a, c), (b, d)))))"
          by (rule ext) (auto split: prod.split)
        show ?thesis
          using raw unfolding presentation .
      qed
      note raw = M4.nn_integral_fst[OF section_measurable, symmetric]
      have left_presentation:
          "(\<lambda>(b, d). ennreal (norm (?q ((a, c), (b, d))))) =
            (\<lambda>bd. ennreal (norm (?q ((a, c), bd))))"
        by (rule ext) (auto split: prod.split)
      have right_presentation:
          "(\<lambda>x. \<integral>\<^sup>+y.
              (case (x, y) of (b, d) \<Rightarrow>
                ennreal (norm (?q ((a, c), (b, d))))) \<partial>M4) =
            (\<lambda>b. \<integral>\<^sup>+d. ?N a b c d \<partial>M4)"
        by (rule ext) simp
      show ?thesis
        using raw by (simp only: split_beta' prod.sel)
    qed
    have source_expanded:
        "integral\<^sup>N ?S (\<lambda>x. ennreal (norm (f x))) =
          (\<integral>\<^sup>+a. \<integral>\<^sup>+b. \<integral>\<^sup>+c. \<integral>\<^sup>+d.
            ?N a b c d \<partial>M4 \<partial>M3 \<partial>M2 \<partial>M1)"
    proof -
      have grouped:
          "integral\<^sup>N ?S (\<lambda>x. ennreal (norm (f x))) =
            (\<integral>\<^sup>+ab. ?SO ab \<partial>(M1 \<Otimes>\<^sub>M M2))"
        using M34.nn_integral_fst[OF f_norm_measurable, symmetric]
        by simp
      have outer:
          "(\<integral>\<^sup>+ab. ?SO ab \<partial>(M1 \<Otimes>\<^sub>M M2)) =
            (\<integral>\<^sup>+a. \<integral>\<^sup>+b. ?SO (a, b) \<partial>M2 \<partial>M1)"
        using M2.nn_integral_fst[OF SO_measurable, symmetric]
        by simp
      have sections:
          "(\<integral>\<^sup>+a. \<integral>\<^sup>+b. ?SO (a, b) \<partial>M2 \<partial>M1) =
            (\<integral>\<^sup>+a. \<integral>\<^sup>+b. \<integral>\<^sup>+c. \<integral>\<^sup>+d.
              ?N a b c d \<partial>M4 \<partial>M3 \<partial>M2 \<partial>M1)"
      proof (rule nn_integral_cong_AE)
        show "AE a in M1.
          (\<integral>\<^sup>+b. ?SO (a, b) \<partial>M2) =
          (\<integral>\<^sup>+b. \<integral>\<^sup>+c. \<integral>\<^sup>+d.
            ?N a b c d \<partial>M4 \<partial>M3 \<partial>M2)"
        proof (rule AE_I2)
          fix a
          assume a_space: "a \<in> space M1"
          show "(\<integral>\<^sup>+b. ?SO (a, b) \<partial>M2) =
            (\<integral>\<^sup>+b. \<integral>\<^sup>+c. \<integral>\<^sup>+d.
              ?N a b c d \<partial>M4 \<partial>M3 \<partial>M2)"
          proof (rule nn_integral_cong_AE)
            show "AE b in M2. ?SO (a, b) =
              (\<integral>\<^sup>+c. \<integral>\<^sup>+d. ?N a b c d \<partial>M4 \<partial>M3)"
              by (rule AE_I2) (rule source_section[OF a_space])
          qed
        qed
      qed
      show ?thesis
        using grouped outer sections by simp
    qed
    have target_expanded:
        "integral\<^sup>N ?T (\<lambda>x. ennreal (norm (?q x))) =
          (\<integral>\<^sup>+a. \<integral>\<^sup>+c. \<integral>\<^sup>+b. \<integral>\<^sup>+d.
            ?N a b c d \<partial>M4 \<partial>M2 \<partial>M3 \<partial>M1)"
    proof -
      have grouped:
          "integral\<^sup>N ?T (\<lambda>x. ennreal (norm (?q x))) =
            (\<integral>\<^sup>+ac. ?TO ac \<partial>(M1 \<Otimes>\<^sub>M M3))"
        using M24.nn_integral_fst[OF q_norm_measurable, symmetric]
        by simp
      have outer:
          "(\<integral>\<^sup>+ac. ?TO ac \<partial>(M1 \<Otimes>\<^sub>M M3)) =
            (\<integral>\<^sup>+a. \<integral>\<^sup>+c. ?TO (a, c) \<partial>M3 \<partial>M1)"
        using M3.nn_integral_fst[OF TO_measurable, symmetric]
        by simp
      have sections:
          "(\<integral>\<^sup>+a. \<integral>\<^sup>+c. ?TO (a, c) \<partial>M3 \<partial>M1) =
            (\<integral>\<^sup>+a. \<integral>\<^sup>+c. \<integral>\<^sup>+b. \<integral>\<^sup>+d.
              ?N a b c d \<partial>M4 \<partial>M2 \<partial>M3 \<partial>M1)"
      proof (rule nn_integral_cong_AE)
        show "AE a in M1.
          (\<integral>\<^sup>+c. ?TO (a, c) \<partial>M3) =
          (\<integral>\<^sup>+c. \<integral>\<^sup>+b. \<integral>\<^sup>+d.
            ?N a b c d \<partial>M4 \<partial>M2 \<partial>M3)"
        proof (rule AE_I2)
          fix a
          assume a_space: "a \<in> space M1"
          show "(\<integral>\<^sup>+c. ?TO (a, c) \<partial>M3) =
            (\<integral>\<^sup>+c. \<integral>\<^sup>+b. \<integral>\<^sup>+d.
              ?N a b c d \<partial>M4 \<partial>M2 \<partial>M3)"
          proof (rule nn_integral_cong_AE)
            show "AE c in M3. ?TO (a, c) =
              (\<integral>\<^sup>+b. \<integral>\<^sup>+d. ?N a b c d \<partial>M4 \<partial>M2)"
              by (rule AE_I2) (rule target_section[OF a_space])
          qed
        qed
      qed
      show ?thesis
        using grouped outer sections by simp
    qed
    have swap_expanded:
        "(\<integral>\<^sup>+a. \<integral>\<^sup>+c. \<integral>\<^sup>+b. \<integral>\<^sup>+d.
            ?N a b c d \<partial>M4 \<partial>M2 \<partial>M3 \<partial>M1) =
          (\<integral>\<^sup>+a. \<integral>\<^sup>+b. \<integral>\<^sup>+c. \<integral>\<^sup>+d.
            ?N a b c d \<partial>M4 \<partial>M3 \<partial>M2 \<partial>M1)"
      by (rule nn_integral_cong_AE, rule AE_I2, rule middle_swap)
    show ?thesis
      using target_expanded swap_expanded source_expanded by simp
  qed
  show ?thesis
    unfolding integrable_iff_bounded
  proof (intro conjI)
    show "?q \<in> borel_measurable ?T"
      by (rule q_measurable)
    show "integral\<^sup>N ?T (\<lambda>x. ennreal (norm (?q x))) < \<infinity>"
      using f_integrable mass_equality
      unfolding integrable_iff_bounded by simp
  qed
qed

end
