theory Inverse_Schrodinger_Lp_Left_Branch_Natural_Finite_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Branch_Natural_Finite_Transport"
begin

section \<open>Bochner integration after full branch-coordinate transport\<close>

theorem slp_left_branch_natural_to_finite_coordinates_measurable:
  "(\<lambda>coordinates.
      (((\<chi> i. fst (fst coordinates) (to_nat_on UNIV i)),
        (\<chi> i. snd (fst coordinates) (to_nat_on UNIV i))),
        snd coordinates)) \<in>
    measurable
      (((PiM {..<CARD('i::finite)}
          (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<CARD('i)}
          (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
      (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
        slp_point) measure)"
proof -
  let ?PN = "PiM {..<CARD('i)}
    (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?V = "lborel :: (slp_point^'i) measure"
  let ?T = "\<lambda>natural_coordinates.
    \<chi> i. natural_coordinates (to_nat_on UNIV i)"
  have reindex_measurable:
      "(\<lambda>natural_coordinates.
          \<lambda>i\<in>(UNIV::'i set).
            natural_coordinates (to_nat_on UNIV i)) \<in>
        measurable ?PN
          (PiM UNIV (\<lambda>_::'i. (lborel :: slp_point measure)))"
    by (rule slp_PiM_uniform_finite_nat_reindex_measurable)
  have vector_borel_measurable:
      "(\<lambda>f::'i \<Rightarrow> slp_point. \<chi> i. f i) \<in>
        measurable
          (PiM UNIV (\<lambda>_::'i. (lborel :: slp_point measure)))
          (borel :: (slp_point^'i) measure)"
  proof -
    have coordinates_measurable:
        "(id :: ('i \<Rightarrow> slp_point) \<Rightarrow>
            ('i \<Rightarrow> slp_point)) \<in>
          borel_measurable
            (PiM UNIV
              (\<lambda>_::'i. (lborel :: slp_point measure)))"
    proof (rule measurable_coordinatewise_then_product)
      fix i :: 'i
      show "(\<lambda>x. id x i) \<in>
        borel_measurable
          (PiM UNIV (\<lambda>_::'i. (lborel :: slp_point measure)))"
        by (simp add: measurable_component_singleton
            cong: measurable_cong_sets)
    qed
    have vec_measurable:
        "vec_lambda \<in> borel_measurable
          (borel :: ('i \<Rightarrow> slp_point) measure)"
      by (rule borel_measurable_continuous_onI)
        (intro continuous_on_vec_lambda, simp)
    show ?thesis
      using measurable_compose[OF coordinates_measurable vec_measurable]
      by (simp only: comp_def id_apply)
  qed
  have vector_measurable:
      "(\<lambda>f::'i \<Rightarrow> slp_point. \<chi> i. f i) \<in>
        measurable
          (PiM UNIV (\<lambda>_::'i. (lborel :: slp_point measure))) ?V"
    using vector_borel_measurable
    by (simp only: measurable_cong_sets[OF refl sets_lborel[symmetric]])
  have T_measurable: "?T \<in> measurable ?PN ?V"
    using measurable_compose[OF reindex_measurable vector_measurable]
    by (simp only: comp_def restrict_UNIV)
  have pair_measurable:
      "(\<lambda>(positive, negative). (?T positive, ?T negative)) \<in>
        measurable (?PN \<Otimes>\<^sub>M ?PN) (?V \<Otimes>\<^sub>M ?V)"
    using T_measurable by measurable
  have full_measurable:
      "(\<lambda>(families, terminal).
          ((\<lambda>(positive, negative). (?T positive, ?T negative))
            families, terminal)) \<in>
        measurable
          ((?PN \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
          ((?V \<Otimes>\<^sub>M ?V) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    using pair_measurable by measurable
  show ?thesis
    using full_measurable
    by (simp only: lborel_prod fst_conv snd_conv case_prod_unfold)
qed

theorem slp_integrable_left_branch_natural_to_finite_coordinates:
  fixes F :: "(((slp_point^'i::finite) \<times> (slp_point^'i)) \<times>
    slp_point) \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes F_measurable:
    "F \<in> borel_measurable
      (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
        slp_point) measure)"
  shows
    "integrable
        (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
          slp_point) measure) F \<longleftrightarrow>
      integrable
        (((PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))
        (\<lambda>coordinates.
          F (((\<chi> i. fst (fst coordinates) (to_nat_on UNIV i)),
            (\<chi> i. snd (fst coordinates) (to_nat_on UNIV i))),
            snd coordinates))"
proof -
  let ?M = "((PiM {..<CARD('i)}
      (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
    (PiM {..<CARD('i)}
      (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
    (lborel :: slp_point measure)"
  let ?N = "lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
    slp_point) measure"
  let ?T = "\<lambda>coordinates.
    (((\<chi> i. fst (fst coordinates) (to_nat_on UNIV i)),
      (\<chi> i. snd (fst coordinates) (to_nat_on UNIV i))),
      snd coordinates)"
  have T_measurable: "?T \<in> measurable ?M ?N"
    by (rule slp_left_branch_natural_to_finite_coordinates_measurable)
  have source_measure: "distr ?M ?N ?T = ?N"
    by (rule slp_distr_left_branch_natural_to_finite_coordinates)
  show ?thesis
    using integrable_distr_eq[OF T_measurable F_measurable]
    by (simp only: source_measure)
qed

theorem slp_integral_left_branch_natural_to_finite_coordinates:
  fixes F :: "(((slp_point^'i::finite) \<times> (slp_point^'i)) \<times>
    slp_point) \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes F_measurable:
    "F \<in> borel_measurable
      (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
        slp_point) measure)"
  shows
    "integral\<^sup>L
        (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
          slp_point) measure) F =
      integral\<^sup>L
        (((PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))
        (\<lambda>coordinates.
          F (((\<chi> i. fst (fst coordinates) (to_nat_on UNIV i)),
            (\<chi> i. snd (fst coordinates) (to_nat_on UNIV i))),
            snd coordinates))"
proof -
  let ?M = "((PiM {..<CARD('i)}
      (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
    (PiM {..<CARD('i)}
      (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
    (lborel :: slp_point measure)"
  let ?N = "lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
    slp_point) measure"
  let ?T = "\<lambda>coordinates.
    (((\<chi> i. fst (fst coordinates) (to_nat_on UNIV i)),
      (\<chi> i. snd (fst coordinates) (to_nat_on UNIV i))),
      snd coordinates)"
  have T_measurable: "?T \<in> measurable ?M ?N"
    by (rule slp_left_branch_natural_to_finite_coordinates_measurable)
  have source_measure: "distr ?M ?N ?T = ?N"
    by (rule slp_distr_left_branch_natural_to_finite_coordinates)
  have transported:
      "integral\<^sup>L (distr ?M ?N ?T) F =
        integral\<^sup>L ?M (\<lambda>x. F (?T x))"
    by (rule integral_distr[OF T_measurable F_measurable])
  show ?thesis
    using transported by (simp only: source_measure)
qed

end
