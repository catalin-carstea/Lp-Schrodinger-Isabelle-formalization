theory Inverse_Schrodinger_Lp_Nested_Boolean_Family_Lebesgue_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Nested_Boolean_Family_Product"
begin

section \<open>Lebesgue transport under nested Boolean flattening\<close>

theorem slp_nested_boolean_family_flatten_distr_lborel:
  "distr
      (lborel :: ((real^bool)^'i::finite) measure)
      (lborel :: (real^('i \<times> bool)) measure)
      slp_nested_boolean_family_flatten =
    (lborel :: (real^('i \<times> bool)) measure)"
proof -
  let ?Pbool =
    "PiM (UNIV::bool set) (\<lambda>_. (lborel :: real measure))"
  let ?Pnested =
    "PiM (UNIV::'i set) (\<lambda>_. ?Pbool)"
  let ?Pvector =
    "PiM (UNIV::'i set) (\<lambda>_. (lborel :: (real^bool) measure))"
  let ?Pflat =
    "PiM (UNIV::('i \<times> bool) set)
      (\<lambda>_. (lborel :: real measure))"
  let ?Vbool = "\<lambda>f::bool \<Rightarrow> real. \<chi> b. f b"
  let ?T =
    "\<lambda>omega::'i \<Rightarrow> (bool \<Rightarrow> real).
      \<lambda>i\<in>(UNIV::'i set). ?Vbool (omega i)"
  let ?Vouter =
    "\<lambda>f::'i \<Rightarrow> (real^bool). \<chi> i. f i"
  let ?Vnested =
    "\<lambda>omega::'i \<Rightarrow> (bool \<Rightarrow> real).
      \<chi> i. \<chi> b. omega i b"
  let ?F =
    "\<lambda>omega::'i \<Rightarrow> (bool \<Rightarrow> real).
      \<lambda>ib. omega (fst ib) (snd ib)"
  let ?Vflat =
    "\<lambda>f::('i \<times> bool) \<Rightarrow> real. \<chi> ib. f ib"

  have Vbool_measurable:
    "?Vbool \<in> measurable ?Pbool (lborel :: (real^bool) measure)"
  proof -
    have raw: "?Vbool \<in> measurable ?Pbool borel"
      by (rule slp_cartesian_vector_constructor_measurable)
    have target_sets:
      "measurable ?Pbool borel =
        measurable ?Pbool (lborel :: (real^bool) measure)"
      by (rule measurable_cong_sets)
        (rule refl, rule sets_lborel[symmetric])
    show ?thesis
      using raw by (simp only: target_sets)
  qed
  have T_measurable: "?T \<in> measurable ?Pnested ?Pvector"
  proof (rule measurable_PiM_single')
    fix i
    assume i_in: "i \<in> (UNIV::'i set)"
    have component:
      "(\<lambda>omega. omega i) \<in> measurable ?Pnested ?Pbool"
      by (rule measurable_component_singleton[OF i_in])
    have composed:
      "(\<lambda>omega. ?Vbool (omega i)) \<in>
        measurable ?Pnested (lborel :: (real^bool) measure)"
      using measurable_compose[OF component Vbool_measurable]
      by (simp only: comp_def)
    show "(\<lambda>omega. ?T omega i) \<in>
      measurable ?Pnested (lborel :: (real^bool) measure)"
      using composed i_in by simp
  next
    show "?T \<in> space ?Pnested \<rightarrow>
      PiE (UNIV::'i set)
        (\<lambda>_. space (lborel :: (real^bool) measure))"
      using Vbool_measurable
      by (auto simp: space_PiM PiE_iff intro: measurable_space)
  qed
  have Vouter_measurable: "?Vouter \<in> measurable ?Pvector borel"
    by (rule slp_euclidean_vector_constructor_measurable)
  have nested_composition: "?Vouter \<circ> ?T = ?Vnested"
  proof (rule ext)
    fix omega
    show "(?Vouter \<circ> ?T) omega = ?Vnested omega"
      unfolding comp_apply vec_eq_iff
      by (intro allI) (simp only: vec_lambda_beta restrict_apply UNIV_I if_True)
  qed
  have Vnested_measurable: "?Vnested \<in> measurable ?Pnested borel"
  proof -
    have "?Vouter \<circ> ?T \<in> measurable ?Pnested borel"
      using measurable_compose[OF T_measurable Vouter_measurable]
      by (simp only: comp_def)
    then show ?thesis
      by (simp only: nested_composition)
  qed
  have F_measurable: "?F \<in> measurable ?Pnested ?Pflat"
  proof (rule measurable_PiM_single')
    fix ib
    assume ib_in: "ib \<in> (UNIV::('i \<times> bool) set)"
    have outer_component:
      "(\<lambda>omega. omega (fst ib)) \<in>
        measurable ?Pnested ?Pbool"
      by (rule measurable_component_singleton) simp
    have inner_component:
      "(\<lambda>eta. eta (snd ib)) \<in>
        measurable ?Pbool (lborel :: real measure)"
      by (rule measurable_component_singleton) simp
    show "(\<lambda>omega. ?F omega ib) \<in>
      measurable ?Pnested (lborel :: real measure)"
      using measurable_compose[OF outer_component inner_component]
      by (simp only: comp_def)
  next
    show "?F \<in> space ?Pnested \<rightarrow>
      PiE (UNIV::('i \<times> bool) set)
        (\<lambda>_. space (lborel :: real measure))"
      by simp
  qed
  have Vflat_measurable: "?Vflat \<in> measurable ?Pflat borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have flatten_borel:
    "(slp_nested_boolean_family_flatten ::
      ((real^bool)^'i) \<Rightarrow> real^('i \<times> bool))
      \<in> measurable borel borel"
    using slp_nested_boolean_family_flatten_measurable[where 'i='i]
    by (simp only: measurable_lborel1 measurable_lborel2)
  have F_transport: "distr ?Pnested ?Pflat ?F = ?Pflat"
  proof -
    have restricted_raw:
      "distr ?Pnested
          (PiM ((UNIV::'i set) \<times> (UNIV::bool set))
            (\<lambda>_. (lborel :: real measure)))
          (\<lambda>omega. \<lambda>ib\<in>
            (UNIV::'i set) \<times> (UNIV::bool set).
              omega (fst ib) (snd ib)) =
        PiM ((UNIV::'i set) \<times> (UNIV::bool set))
          (\<lambda>_. (lborel :: real measure))"
    proof (rule slp_distr_PiM_nested_flatten)
      show "sigma_finite_measure (lborel :: real measure)"
        by standard
      show "finite (UNIV::'i set)"
        by simp
      show "finite (UNIV::bool set)"
        by simp
    qed
    have restricted:
      "distr ?Pnested ?Pflat
          (\<lambda>omega. \<lambda>ib\<in>
            (UNIV::'i set) \<times> (UNIV::bool set).
              omega (fst ib) (snd ib)) =
        ?Pflat"
      using restricted_raw by simp
    have map_eq:
      "(\<lambda>omega. \<lambda>ib\<in>
          (UNIV::'i set) \<times> (UNIV::bool set).
            omega (fst ib) (snd ib)) = ?F"
      by (rule ext)+ simp
    show ?thesis
      using restricted by (simp only: map_eq)
  qed
  have flatten_composition:
    "(slp_nested_boolean_family_flatten ::
        ((real^bool)^'i) \<Rightarrow> real^('i \<times> bool)) \<circ> ?Vnested =
      ?Vflat \<circ> ?F"
  proof (rule ext)
    fix omega
    show "(slp_nested_boolean_family_flatten \<circ> ?Vnested) omega =
        (?Vflat \<circ> ?F) omega"
      unfolding comp_apply slp_nested_boolean_family_flatten_def vec_eq_iff
      by (intro allI) (simp only: vec_lambda_beta)
  qed

  have borel_transport:
    "distr
        (lborel :: ((real^bool)^'i) measure)
        borel
        slp_nested_boolean_family_flatten =
      (lborel :: (real^('i \<times> bool)) measure)"
  proof -
    have
      "distr
          (lborel :: ((real^bool)^'i) measure)
          borel
          slp_nested_boolean_family_flatten =
        distr (distr ?Pnested borel ?Vnested) borel
          slp_nested_boolean_family_flatten"
      by (simp only: slp_lborel_nested_boolean_family_scalar_product)
    also have "... =
        distr ?Pnested borel
          (slp_nested_boolean_family_flatten \<circ> ?Vnested)"
      by (rule distr_distr[OF flatten_borel Vnested_measurable])
    also have "... = distr ?Pnested borel (?Vflat \<circ> ?F)"
      by (simp only: flatten_composition)
    also have "... = distr (distr ?Pnested ?Pflat ?F) borel ?Vflat"
      by (rule distr_distr[OF Vflat_measurable F_measurable, symmetric])
    also have "... = distr ?Pflat borel ?Vflat"
      by (simp only: F_transport)
    also have "... = (lborel :: (real^('i \<times> bool)) measure)"
      by (rule slp_lborel_cartesian_vector_product[symmetric])
    finally show ?thesis .
  qed
  have target_change:
    "distr
        (lborel :: ((real^bool)^'i) measure)
        (lborel :: (real^('i \<times> bool)) measure)
        slp_nested_boolean_family_flatten =
      distr (lborel :: ((real^bool)^'i) measure) borel
        slp_nested_boolean_family_flatten"
  proof (rule distr_cong)
    show "(lborel :: ((real^bool)^'i) measure) = lborel"
      by (rule refl)
    show "sets (lborel :: (real^('i \<times> bool)) measure) = sets borel"
      by (rule sets_lborel)
    show "slp_nested_boolean_family_flatten x =
        slp_nested_boolean_family_flatten x"
      for x :: "(real^bool)^'i"
      by (rule refl)
  qed
  show ?thesis
    using target_change borel_transport by simp
qed

end
