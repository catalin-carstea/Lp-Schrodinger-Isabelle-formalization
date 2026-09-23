theory Inverse_Schrodinger_Lp_Nested_Boolean_Family_Product
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Nested_Boolean_Family_Flatten"
begin

section \<open>Nested Boolean Cartesian Lebesgue measure as scalar products\<close>

lemma slp_lborel_nested_boolean_family_scalar_product:
  "(lborel :: ((real^bool)^'i::finite) measure) =
    distr
      (PiM UNIV
        (\<lambda>_::'i. PiM UNIV
          (\<lambda>_::bool. (lborel :: real measure))))
      borel
      (\<lambda>omega. \<chi> i. \<chi> b. omega i b)"
proof -
  let ?Pbool =
    "PiM (UNIV::bool set) (\<lambda>_. (lborel :: real measure))"
  let ?Pnested =
    "PiM (UNIV::'i set) (\<lambda>_. ?Pbool)"
  let ?Pvector =
    "PiM (UNIV::'i set) (\<lambda>_. (lborel :: (real^bool) measure))"
  let ?Vbool = "\<lambda>f::bool \<Rightarrow> real. \<chi> b. f b"
  let ?T =
    "\<lambda>omega::'i \<Rightarrow> (bool \<Rightarrow> real).
      \<lambda>i\<in>(UNIV::'i set). ?Vbool (omega i)"
  let ?Vouter =
    "\<lambda>f::'i \<Rightarrow> (real^bool). \<chi> i. f i"
  let ?Vnested =
    "\<lambda>omega::'i \<Rightarrow> (bool \<Rightarrow> real).
      \<chi> i. \<chi> b. omega i b"

  interpret bool_product:
    finite_product_sigma_finite
      "\<lambda>_::bool. (lborel :: real measure)" UNIV
    by standard simp
  have Pbool_sigma: "sigma_finite_measure ?Pbool"
    by standard
  interpret nested_scalar:
    product_sigma_finite "\<lambda>_::'i. ?Pbool"
    by standard

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
  have Vbool_transport:
    "distr ?Pbool (lborel :: (real^bool) measure) ?Vbool = lborel"
  proof -
    have target_change:
      "distr ?Pbool (lborel :: (real^bool) measure) ?Vbool =
        distr ?Pbool borel ?Vbool"
    proof (rule distr_cong)
      show "?Pbool = ?Pbool"
        by (rule refl)
      show "sets (lborel :: (real^bool) measure) = sets borel"
        by (rule sets_lborel)
      show "?Vbool x = ?Vbool x" for x
        by (rule refl)
    qed
    show ?thesis
      using target_change
        slp_lborel_cartesian_vector_product[where 'n=bool, symmetric]
      by simp
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
  have product_transport: "distr ?Pnested ?Pvector ?T = ?Pvector"
  proof (rule nested_scalar.slp_distr_PiM_componentwise)
    show "finite (UNIV::'i set)"
      by simp
    show "sigma_finite_measure (lborel :: (real^bool) measure)"
      for i :: 'i
      by standard
    show "?Vbool \<in> measurable ?Pbool (lborel :: (real^bool) measure)"
      for i :: 'i
      by (rule Vbool_measurable)
    show "distr ?Pbool (lborel :: (real^bool) measure) ?Vbool =
        (lborel :: (real^bool) measure)"
      for i :: 'i
      by (rule Vbool_transport)
  qed
  have composition: "?Vouter \<circ> ?T = ?Vnested"
  proof (rule ext)
    fix omega
    show "(?Vouter \<circ> ?T) omega = ?Vnested omega"
      unfolding comp_apply vec_eq_iff
      by (intro allI) (simp only: vec_lambda_beta restrict_apply UNIV_I if_True)
  qed

  have
    "(lborel :: ((real^bool)^'i) measure) =
      distr ?Pvector borel ?Vouter"
    by (rule slp_lborel_cartesian_euclidean_vector_product)
  also have "... =
      distr (distr ?Pnested ?Pvector ?T) borel ?Vouter"
    by (simp only: product_transport)
  also have "... = distr ?Pnested borel (?Vouter \<circ> ?T)"
    by (rule distr_distr[OF Vouter_measurable T_measurable])
  also have "... = distr ?Pnested borel ?Vnested"
    by (simp only: composition)
  finally show ?thesis .
qed

end
