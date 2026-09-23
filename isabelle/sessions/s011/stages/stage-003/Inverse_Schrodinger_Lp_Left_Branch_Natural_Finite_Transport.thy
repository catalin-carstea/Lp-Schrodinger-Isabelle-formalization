theory Inverse_Schrodinger_Lp_Left_Branch_Natural_Finite_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Finite_Product_Nat_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cartesian_Euclidean_Product"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Product_Map_Transport"
begin

section \<open>Natural branch families as finite Cartesian coordinates\<close>

theorem slp_PiM_uniform_finite_nat_reindex_measurable:
  "(\<lambda>natural_coordinates.
      \<lambda>i\<in>(UNIV::'i::finite set).
        natural_coordinates (to_nat_on UNIV i)) \<in>
    measurable
      (PiM {..<CARD('i)}
        (\<lambda>_::nat. (lborel :: 'a::euclidean_space measure)))
      (PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure)))"
proof (rule measurable_PiM_single')
  fix i :: 'i
  assume "i \<in> (UNIV::'i set)"
  have enumeration:
      "bij_betw (to_nat_on (UNIV :: 'i set)) UNIV {..<CARD('i)}"
    by (rule to_nat_on_finite) simp
  have index_in: "to_nat_on (UNIV :: 'i set) i \<in> {..<CARD('i)}"
    using enumeration by (auto simp: bij_betw_def)
  have component:
      "(\<lambda>natural_coordinates.
          natural_coordinates (to_nat_on (UNIV :: 'i set) i)) \<in>
        measurable
          (PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: 'a measure)))
          (lborel :: 'a measure)"
    by (rule measurable_component_singleton[OF index_in])
  show
    "(\<lambda>natural_coordinates.
        (\<lambda>i\<in>(UNIV::'i set).
          natural_coordinates (to_nat_on UNIV i)) i) \<in>
      measurable
        (PiM {..<CARD('i)}
          (\<lambda>_::nat. (lborel :: 'a measure)))
        (lborel :: 'a measure)"
    using component by simp
next
  show
    "(\<lambda>natural_coordinates i.
        (\<lambda>i\<in>(UNIV::'i set).
          natural_coordinates (to_nat_on UNIV i)) i) \<in>
      space
        (PiM {..<CARD('i)}
          (\<lambda>_::nat. (lborel :: 'a measure))) \<rightarrow>
      PiE (UNIV::'i set) (\<lambda>_. space (lborel :: 'a measure))"
    by simp
qed

theorem slp_distr_PiM_finite_nat_to_cartesian_lborel:
  "distr
      (PiM {..<CARD('i::finite)}
        (\<lambda>_::nat. (lborel :: 'a::euclidean_space measure)))
      (lborel :: ('a^'i) measure)
      (\<lambda>natural_coordinates.
        \<chi> i. natural_coordinates (to_nat_on UNIV i)) =
    (lborel :: ('a^'i) measure)"
proof -
  let ?PN = "PiM {..<CARD('i)}
    (\<lambda>_::nat. (lborel :: 'a measure))"
  let ?PI = "PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))"
  let ?T = "\<lambda>natural_coordinates.
    \<lambda>i\<in>(UNIV::'i set).
      natural_coordinates (to_nat_on UNIV i)"
  let ?V = "\<lambda>f::'i \<Rightarrow> 'a. \<chi> i. f i"
  have T_measurable: "?T \<in> measurable ?PN ?PI"
    by (rule slp_PiM_uniform_finite_nat_reindex_measurable)
  have V_borel_measurable:
      "?V \<in> measurable ?PI (borel :: ('a^'i) measure)"
  proof -
    have coordinates_measurable:
        "(id :: ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a)) \<in>
          borel_measurable ?PI"
    proof (rule measurable_coordinatewise_then_product)
      fix i :: 'i
      show "(\<lambda>x. id x i) \<in> borel_measurable ?PI"
        by (simp add: measurable_component_singleton
            cong: measurable_cong_sets)
    qed
    have vec_measurable:
        "vec_lambda \<in> borel_measurable
          (borel :: ('i \<Rightarrow> 'a) measure)"
      by (rule borel_measurable_continuous_onI)
        (intro continuous_on_vec_lambda, simp)
    show ?thesis
      using measurable_compose[OF coordinates_measurable vec_measurable]
      by (simp only: comp_def id_apply)
  qed
  have V_measurable:
      "?V \<in> measurable ?PI (lborel :: ('a^'i) measure)"
    using V_borel_measurable
    by (simp only: measurable_cong_sets[OF refl sets_lborel[symmetric]])
  have natural_transport: "distr ?PN ?PI ?T = ?PI"
    by (rule slp_distr_PiM_uniform_finite_nat_reindex)
  have vector_transport:
      "distr ?PI (lborel :: ('a^'i) measure) ?V = lborel"
  proof -
    have target_change:
        "distr ?PI (lborel :: ('a^'i) measure) ?V =
          distr ?PI borel ?V"
    proof (rule distr_cong)
      show "?PI = ?PI"
        by (rule refl)
      show "sets (lborel :: ('a^'i) measure) = sets borel"
        by (rule sets_lborel)
      show "?V x = ?V x" for x
        by (rule refl)
    qed
    show ?thesis
      using target_change
        slp_lborel_cartesian_euclidean_vector_product[
          where 'a = 'a and 'n = 'i, symmetric]
      by simp
  qed
  have composed_transport:
      "distr (distr ?PN ?PI ?T) (lborel :: ('a^'i) measure) ?V =
        distr ?PN (lborel :: ('a^'i) measure) (?V \<circ> ?T)"
    by (rule distr_distr[OF V_measurable T_measurable])
  have direct_transport:
      "distr ?PN (lborel :: ('a^'i) measure) (?V \<circ> ?T) = lborel"
  proof -
    have
      "distr ?PN (lborel :: ('a^'i) measure) (?V \<circ> ?T) =
        distr (distr ?PN ?PI ?T) (lborel :: ('a^'i) measure) ?V"
      by (rule composed_transport[symmetric])
    also have "... = distr ?PI (lborel :: ('a^'i) measure) ?V"
      by (simp only: natural_transport)
    also have "... = lborel"
      by (rule vector_transport)
    finally show ?thesis .
  qed
  show ?thesis
    using direct_transport
    by (simp only: comp_def restrict_UNIV)
qed

theorem slp_distr_left_branch_natural_to_finite_coordinates:
  "distr
      (((PiM {..<CARD('i::finite)}
          (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
        (PiM {..<CARD('i)}
          (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
      (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
        slp_point) measure)
      (\<lambda>coordinates.
        (((\<chi> i. fst (fst coordinates) (to_nat_on UNIV i)),
          (\<chi> i. snd (fst coordinates) (to_nat_on UNIV i))),
          snd coordinates)) =
    (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
      slp_point) measure)"
proof -
  let ?PN = "PiM {..<CARD('i)}
    (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?V = "lborel :: (slp_point^'i) measure"
  let ?T = "\<lambda>natural_coordinates.
    \<chi> i. natural_coordinates (to_nat_on UNIV i)"
  have T_measurable: "?T \<in> measurable ?PN ?V"
  proof -
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
    show ?thesis
      using measurable_compose[OF reindex_measurable vector_measurable]
      by (simp only: comp_def restrict_UNIV)
  qed
  have T_transport: "distr ?PN ?V ?T = ?V"
    by (rule slp_distr_PiM_finite_nat_to_cartesian_lborel)
  have pair_transport:
      "distr (?PN \<Otimes>\<^sub>M ?PN) (?V \<Otimes>\<^sub>M ?V)
          (\<lambda>(positive, negative). (?T positive, ?T negative)) =
        ?V \<Otimes>\<^sub>M ?V"
    by (rule slp_distr_pair_map_eq[OF T_measurable T_measurable
          T_transport T_transport]) standard
  have pair_measurable:
      "(\<lambda>(positive, negative). (?T positive, ?T negative)) \<in>
        measurable (?PN \<Otimes>\<^sub>M ?PN) (?V \<Otimes>\<^sub>M ?V)"
    using T_measurable by measurable
  have terminal_measurable:
      "(id :: slp_point \<Rightarrow> slp_point) \<in>
        measurable lborel lborel"
    by measurable
  have terminal_transport:
      "distr (lborel :: slp_point measure) lborel id = lborel"
    unfolding id_def
    by (rule distr_id2) (rule refl)
  have full_transport:
      "distr
          ((?PN \<Otimes>\<^sub>M ?PN) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
          ((?V \<Otimes>\<^sub>M ?V) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
          (\<lambda>(families, terminal).
            ((\<lambda>(positive, negative). (?T positive, ?T negative))
              families, id terminal)) =
        (?V \<Otimes>\<^sub>M ?V) \<Otimes>\<^sub>M
          (lborel :: slp_point measure)"
    by (rule slp_distr_pair_map_eq[OF pair_measurable terminal_measurable
          pair_transport terminal_transport]) standard
  show ?thesis
    using full_transport
    by (simp only: lborel_prod fst_conv snd_conv id_apply case_prod_unfold)
qed

end
