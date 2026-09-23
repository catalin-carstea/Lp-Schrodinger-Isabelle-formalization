theory Inverse_Schrodinger_Lp_Finite_Product_Nat_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Finite_Product_Nat_Reindex"
begin

section \<open>Bochner integration after finite natural reindexing\<close>

theorem slp_integrable_uniform_finite_nat_reindex:
  fixes F :: "('i::finite \<Rightarrow> 'a::euclidean_space) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes F_measurable:
    "F \<in> borel_measurable
      (PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure)))"
  shows
    "integrable
        (PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))) F \<longleftrightarrow>
      integrable
        (PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: 'a measure)))
        (\<lambda>natural_coordinates.
          F (\<lambda>i\<in>UNIV.
            natural_coordinates (to_nat_on UNIV i)))"
proof -
  let ?PI = "PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))"
  let ?PN = "PiM {..<CARD('i)}
    (\<lambda>_::nat. (lborel :: 'a measure))"
  let ?t = "to_nat_on (UNIV :: 'i set)"
  let ?T = "\<lambda>omega. \<lambda>i\<in>(UNIV::'i set). omega (?t i)"
  have t_bij: "bij_betw ?t (UNIV::'i set) {..<CARD('i)}"
    by (rule to_nat_on_finite) simp
  have t_into: "\<And>i. ?t i \<in> {..<CARD('i)}"
    using t_bij by (auto simp: bij_betw_def)
  have T_measurable: "?T \<in> measurable ?PN ?PI"
  proof (rule measurable_PiM_single')
    fix i
    assume "i \<in> (UNIV::'i set)"
    have component:
        "(\<lambda>omega. omega (?t i)) \<in>
          measurable ?PN (lborel :: 'a measure)"
      by (rule measurable_component_singleton[OF t_into])
    show "(\<lambda>omega. ?T omega i) \<in>
        measurable ?PN (lborel :: 'a measure)"
      using component by simp
  next
    show "?T \<in> space ?PN \<rightarrow>
        PiE (UNIV::'i set) (\<lambda>_. space (lborel :: 'a measure))"
      by simp
  qed
  have source_measure: "distr ?PN ?PI ?T = ?PI"
    by (rule slp_distr_PiM_uniform_finite_nat_reindex)
  show ?thesis
    using integrable_distr_eq[OF T_measurable F_measurable]
    by (simp only: source_measure)
qed

theorem slp_integral_uniform_finite_nat_reindex:
  fixes F :: "('i::finite \<Rightarrow> 'a::euclidean_space) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes F_measurable:
    "F \<in> borel_measurable
      (PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure)))"
  shows
    "integral\<^sup>L
        (PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))) F =
      integral\<^sup>L
        (PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: 'a measure)))
        (\<lambda>natural_coordinates.
          F (\<lambda>i\<in>UNIV.
            natural_coordinates (to_nat_on UNIV i)))"
proof -
  let ?PI = "PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))"
  let ?PN = "PiM {..<CARD('i)}
    (\<lambda>_::nat. (lborel :: 'a measure))"
  let ?t = "to_nat_on (UNIV :: 'i set)"
  let ?T = "\<lambda>omega. \<lambda>i\<in>(UNIV::'i set). omega (?t i)"
  have t_bij: "bij_betw ?t (UNIV::'i set) {..<CARD('i)}"
    by (rule to_nat_on_finite) simp
  have t_into: "\<And>i. ?t i \<in> {..<CARD('i)}"
    using t_bij by (auto simp: bij_betw_def)
  have T_measurable: "?T \<in> measurable ?PN ?PI"
  proof (rule measurable_PiM_single')
    fix i
    assume "i \<in> (UNIV::'i set)"
    have component:
        "(\<lambda>omega. omega (?t i)) \<in>
          measurable ?PN (lborel :: 'a measure)"
      by (rule measurable_component_singleton[OF t_into])
    show "(\<lambda>omega. ?T omega i) \<in>
        measurable ?PN (lborel :: 'a measure)"
      using component by simp
  next
    show "?T \<in> space ?PN \<rightarrow>
        PiE (UNIV::'i set) (\<lambda>_. space (lborel :: 'a measure))"
      by simp
  qed
  have source_measure: "distr ?PN ?PI ?T = ?PI"
    by (rule slp_distr_PiM_uniform_finite_nat_reindex)
  have transported:
      "integral\<^sup>L (distr ?PN ?PI ?T) F =
        integral\<^sup>L ?PN (\<lambda>x. F (?T x))"
    by (rule integral_distr[OF T_measurable F_measurable])
  show ?thesis
    using transported by (simp only: source_measure)
qed

end
