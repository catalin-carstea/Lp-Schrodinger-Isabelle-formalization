theory Inverse_Schrodinger_Lp_Four_Factor_Middle_Swap_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Four_Factor_Middle_Swap_Integrable"
begin

section \<open>The four-factor middle swap preserves the Bochner integral\<close>

theorem slp_distr_four_factor_middle_swap:
  fixes M1 :: "'a measure" and M2 :: "'b measure"
    and M3 :: "'c measure" and M4 :: "'d measure"
  assumes sigma1: "sigma_finite_measure M1"
    and sigma2: "sigma_finite_measure M2"
    and sigma3: "sigma_finite_measure M3"
    and sigma4: "sigma_finite_measure M4"
  shows
    "distr
      ((M1 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M (M2 \<Otimes>\<^sub>M M4))
      ((M1 \<Otimes>\<^sub>M M2) \<Otimes>\<^sub>M (M3 \<Otimes>\<^sub>M M4))
      (\<lambda>((a, c), (b, d)). ((a, b), (c, d))) =
      ((M1 \<Otimes>\<^sub>M M2) \<Otimes>\<^sub>M (M3 \<Otimes>\<^sub>M M4))"
proof -
  let ?S = "(M1 \<Otimes>\<^sub>M M2) \<Otimes>\<^sub>M (M3 \<Otimes>\<^sub>M M4)"
  let ?T = "(M1 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M (M2 \<Otimes>\<^sub>M M4)"
  let ?r = "\<lambda>((a, c), (b, d)). ((a, b), (c, d))"
  interpret M1: sigma_finite_measure M1 by (rule sigma1)
  interpret M2: sigma_finite_measure M2 by (rule sigma2)
  interpret M3: sigma_finite_measure M3 by (rule sigma3)
  interpret M4: sigma_finite_measure M4 by (rule sigma4)
  interpret M12: pair_sigma_finite M1 M2 ..
  interpret M13: pair_sigma_finite M1 M3 ..
  interpret M24: pair_sigma_finite M2 M4 ..
  interpret M34: pair_sigma_finite M3 M4 ..
  interpret M24_product: sigma_finite_measure "M2 \<Otimes>\<^sub>M M4"
    by standard
  interpret S: pair_sigma_finite "M1 \<Otimes>\<^sub>M M2" "M3 \<Otimes>\<^sub>M M4" ..
  interpret T: pair_sigma_finite "M1 \<Otimes>\<^sub>M M3" "M2 \<Otimes>\<^sub>M M4" ..
  have r_measurable: "?r \<in> measurable ?T ?S"
  proof -
    have raw:
        "(\<lambda>x. ((fst (fst x), fst (snd x)),
          (snd (fst x), snd (snd x)))) \<in> measurable ?T ?S"
      by measurable
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have source_eq: "?S = distr ?T ?S ?r"
  proof (rule pair_measure_eqI)
    show "sigma_finite_measure (M1 \<Otimes>\<^sub>M M2)"
      by standard
    show "sigma_finite_measure (M3 \<Otimes>\<^sub>M M4)"
      by standard
    show "sets ?S = sets (distr ?T ?S ?r)"
      using r_measurable by simp
    fix A B
    assume A: "A \<in> sets (M1 \<Otimes>\<^sub>M M2)"
      and B: "B \<in> sets (M3 \<Otimes>\<^sub>M M4)"
    show "emeasure (M1 \<Otimes>\<^sub>M M2) A *
        emeasure (M3 \<Otimes>\<^sub>M M4) B =
      emeasure (distr ?T ?S ?r) (A \<times> B)"
    proof -
      have AB_sets: "A \<times> B \<in> sets ?S"
        using A B by measurable
      let ?E = "?r -` (A \<times> B) \<inter> space ?T"
      have E_sets: "?E \<in> sets ?T"
        by (rule measurable_sets[OF r_measurable AB_sets])
      have sections:
          "AE ac in (M1 \<Otimes>\<^sub>M M3).
            emeasure (M2 \<Otimes>\<^sub>M M4) (Pair ac -` ?E) =
            emeasure M2 (Pair (fst ac) -` A) *
              emeasure M4 (Pair (snd ac) -` B)"
      proof (rule AE_I2)
        fix ac
        assume ac_space: "ac \<in> space (M1 \<Otimes>\<^sub>M M3)"
        have section_eq:
            "Pair ac -` ?E =
              (Pair (fst ac) -` A) \<times> (Pair (snd ac) -` B)"
          using ac_space sets.sets_into_space[OF A]
            sets.sets_into_space[OF B]
          by (auto simp: space_pair_measure)
        show "emeasure (M2 \<Otimes>\<^sub>M M4) (Pair ac -` ?E) =
            emeasure M2 (Pair (fst ac) -` A) *
              emeasure M4 (Pair (snd ac) -` B)"
          unfolding section_eq
          by (rule M4.emeasure_pair_measure_Times)
             (rule sets_Pair1[OF A], rule sets_Pair1[OF B])
      qed
      have target_mass:
          "emeasure ?T ?E =
            (\<integral>\<^sup>+ac.
              emeasure M2 (Pair (fst ac) -` A) *
                emeasure M4 (Pair (snd ac) -` B)
              \<partial>(M1 \<Otimes>\<^sub>M M3))"
        using M24.P.emeasure_pair_measure_alt[OF E_sets] sections
        by (rule trans[OF _ nn_integral_cong_AE])
      have factor_mass:
          "(\<integral>\<^sup>+ac.
              emeasure M2 (Pair (fst ac) -` A) *
                emeasure M4 (Pair (snd ac) -` B)
              \<partial>(M1 \<Otimes>\<^sub>M M3)) =
            emeasure (M1 \<Otimes>\<^sub>M M2) A *
              emeasure (M3 \<Otimes>\<^sub>M M4) B"
      proof -
        have A_section_measurable:
            "(\<lambda>a. emeasure M2 (Pair a -` A))
              \<in> borel_measurable M1"
          by (rule M12.measurable_emeasure_Pair1[OF A])
        have B_section_measurable:
            "(\<lambda>c. emeasure M4 (Pair c -` B))
              \<in> borel_measurable M3"
          by (rule M34.measurable_emeasure_Pair1[OF B])
        have fst_measurable:
            "(fst :: ('a \<times> 'c) \<Rightarrow> 'a)
              \<in> measurable (M1 \<Otimes>\<^sub>M M3) M1"
          by measurable
        have snd_measurable:
            "(snd :: ('a \<times> 'c) \<Rightarrow> 'c)
              \<in> measurable (M1 \<Otimes>\<^sub>M M3) M3"
          by measurable
        have A_lift_measurable:
            "(\<lambda>ac. emeasure M2 (Pair (fst ac) -` A))
              \<in> borel_measurable (M1 \<Otimes>\<^sub>M M3)"
          using measurable_compose[OF fst_measurable A_section_measurable]
          by (simp only: comp_def)
        have B_lift_measurable:
            "(\<lambda>ac. emeasure M4 (Pair (snd ac) -` B))
              \<in> borel_measurable (M1 \<Otimes>\<^sub>M M3)"
          using measurable_compose[OF snd_measurable B_section_measurable]
          by (simp only: comp_def)
        have measurable_product:
            "(\<lambda>(a, c). emeasure M2 (Pair a -` A) *
              emeasure M4 (Pair c -` B))
              \<in> borel_measurable (M1 \<Otimes>\<^sub>M M3)"
        proof -
          note raw = borel_measurable_times_ennreal[OF
            A_lift_measurable B_lift_measurable]
          show ?thesis
            using raw by (simp only: split_beta')
        qed
        have expand:
            "(\<integral>\<^sup>+ac.
                emeasure M2 (Pair (fst ac) -` A) *
                  emeasure M4 (Pair (snd ac) -` B)
                \<partial>(M1 \<Otimes>\<^sub>M M3)) =
              (\<integral>\<^sup>+a. \<integral>\<^sup>+c.
                emeasure M2 (Pair a -` A) *
                  emeasure M4 (Pair c -` B) \<partial>M3 \<partial>M1)"
          using M3.nn_integral_fst[OF measurable_product, symmetric]
          by (simp only: split_beta' prod.sel)
        have inner:
            "\<And>a. (\<integral>\<^sup>+c.
              emeasure M2 (Pair a -` A) *
                emeasure M4 (Pair c -` B) \<partial>M3) =
              emeasure M2 (Pair a -` A) *
                (\<integral>\<^sup>+c. emeasure M4 (Pair c -` B) \<partial>M3)"
          by (rule nn_integral_cmult[OF B_section_measurable])
        have outer:
            "(\<integral>\<^sup>+a. emeasure M2 (Pair a -` A) *
                (\<integral>\<^sup>+c. emeasure M4 (Pair c -` B) \<partial>M3)
              \<partial>M1) =
              (\<integral>\<^sup>+a. emeasure M2 (Pair a -` A) \<partial>M1) *
                (\<integral>\<^sup>+c. emeasure M4 (Pair c -` B) \<partial>M3)"
        proof -
          note raw = nn_integral_cmult[OF A_section_measurable,
            of "(\<integral>\<^sup>+c. emeasure M4 (Pair c -` B) \<partial>M3)"]
          show ?thesis
            using raw by (simp only: mult.commute)
        qed
        show ?thesis
          unfolding expand
          apply (subst nn_integral_cong[OF inner])
          using outer M2.emeasure_pair_measure_alt[OF A]
            M4.emeasure_pair_measure_alt[OF B]
          by simp
      qed
      show ?thesis
        using emeasure_distr[OF r_measurable AB_sets]
          target_mass factor_mass
        by simp
    qed
  qed
  show ?thesis
    using source_eq by simp
qed

theorem slp_integral_four_factor_middle_swap:
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
    "integral\<^sup>L
        ((M1 \<Otimes>\<^sub>M M2) \<Otimes>\<^sub>M (M3 \<Otimes>\<^sub>M M4)) f =
      integral\<^sup>L
        ((M1 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M (M2 \<Otimes>\<^sub>M M4))
        (\<lambda>((a, c), (b, d)). f ((a, b), (c, d)))"
proof -
  let ?S = "(M1 \<Otimes>\<^sub>M M2) \<Otimes>\<^sub>M (M3 \<Otimes>\<^sub>M M4)"
  let ?T = "(M1 \<Otimes>\<^sub>M M3) \<Otimes>\<^sub>M (M2 \<Otimes>\<^sub>M M4)"
  let ?r = "\<lambda>((a, c), (b, d)). ((a, b), (c, d))"
  have f_measurable: "f \<in> borel_measurable ?S"
    using f_integrable by simp
  have r_measurable: "?r \<in> measurable ?T ?S"
  proof -
    have raw:
        "(\<lambda>x. ((fst (fst x), fst (snd x)),
          (snd (fst x), snd (snd x)))) \<in> measurable ?T ?S"
      by measurable
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have distribution:
      "distr ?T ?S ?r = ?S"
    by (rule slp_distr_four_factor_middle_swap[OF
      sigma1 sigma2 sigma3 sigma4])
  note transported = integral_distr[OF r_measurable f_measurable]
  show ?thesis
    using transported distribution
    by (simp only: split_beta' comp_def)
qed

end
