theory Inverse_Schrodinger_Lp_Point_Family_Boolean_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Finite_Product_Componentwise_Transport"
begin

section \<open>Finite planar families in nested Boolean coordinates\<close>

definition slp_point_family_boolean_nested_pack ::
    "(slp_point^'i::finite) \<Rightarrow> ((real^bool)^'i)"
where
  "slp_point_family_boolean_nested_pack x =
    (\<chi> i. slp_complex_coordinate_pack (slp_point_as_complex (x $ i)))"

lemma slp_euclidean_vector_constructor_measurable:
  "(\<lambda>f. \<chi> i. f i) \<in>
    measurable
      (PiM UNIV (\<lambda>_::'i::finite. (lborel :: 'a::euclidean_space measure)))
      borel"
proof -
  have coordinates_measurable:
    "(id :: ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a)) \<in>
      borel_measurable
        (PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure)))"
  proof (rule measurable_coordinatewise_then_product)
    fix i
    show "(\<lambda>x. id x i) \<in>
      borel_measurable (PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure)))"
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
    by (simp add: comp_def)
qed

lemma slp_point_boolean_map_measurable:
  "(\<lambda>x::slp_point.
      slp_complex_coordinate_pack (slp_point_as_complex x)) \<in>
    measurable lborel (lborel :: (real^bool) measure)"
proof -
  have
    "(\<lambda>x::slp_point. \<chi> b. x $ slp_bool_to_point_index b) \<in>
      measurable borel borel"
    by (rule slp_cartesian_coordinate_reindex_measurable)
  then show ?thesis
    by (simp only: slp_point_boolean_coordinate_reindex
        measurable_lborel1 measurable_lborel2)
qed

lemma slp_point_family_boolean_nested_pack_measurable:
  "slp_point_family_boolean_nested_pack \<in>
    measurable borel borel"
proof -
  let ?P = "\<lambda>x::slp_point.
    slp_complex_coordinate_pack (slp_point_as_complex x)"
  have point_linear:
    "linear (\<lambda>x::slp_point.
      \<chi> b. x $ slp_bool_to_point_index b)"
    by (rule slp_cartesian_coordinate_reindex_linear)
  have point_bounded:
    "bounded_linear (\<lambda>x::slp_point.
      \<chi> b. x $ slp_bool_to_point_index b)"
    using point_linear by (simp add: linear_conv_bounded_linear)
  have point_continuous: "continuous_on UNIV ?P"
    using linear_continuous_on[OF point_bounded]
    by (simp only: slp_point_boolean_coordinate_reindex)
  have continuous:
    "continuous_on UNIV (slp_point_family_boolean_nested_pack ::
      (slp_point^'i::finite) \<Rightarrow> ((real^bool)^'i))"
    unfolding slp_point_family_boolean_nested_pack_def
  proof (rule continuous_on_vec_lambda)
    fix i
    have component_continuous:
      "continuous_on UNIV (\<lambda>x::slp_point^'i. x $ i)"
      by (rule linear_continuous_on)
        (rule bounded_linear_vec_nth)
    show "continuous_on UNIV (\<lambda>x::slp_point^'i. ?P (x $ i))"
      by (rule continuous_on_compose2[
            OF point_continuous component_continuous])
        simp
  qed
  show ?thesis
    by (rule borel_measurable_continuous_onI[OF continuous])
qed

theorem slp_point_family_boolean_nested_distr_borel:
  "distr (lborel :: (slp_point^'i::finite) measure) borel
      slp_point_family_boolean_nested_pack =
    (lborel :: ((real^bool)^'i) measure)"
proof -
  let ?Ms = "PiM (UNIV::'i set)
    (\<lambda>_. (lborel :: slp_point measure))"
  let ?Mt = "PiM (UNIV::'i set)
    (\<lambda>_. (lborel :: (real^bool) measure))"
  let ?Vs = "\<lambda>f::'i \<Rightarrow> slp_point. \<chi> i. f i"
  let ?Vt = "\<lambda>f::'i \<Rightarrow> (real^bool). \<chi> i. f i"
  let ?P = "\<lambda>x::slp_point.
    slp_complex_coordinate_pack (slp_point_as_complex x)"
  let ?T = "\<lambda>omega::'i \<Rightarrow> slp_point. \<lambda>i. ?P (omega i)"

  interpret source:
    product_sigma_finite "\<lambda>_::'i. (lborel :: slp_point measure)"
    by standard

  have Vs_measurable: "?Vs \<in> measurable ?Ms borel"
    by (rule slp_euclidean_vector_constructor_measurable)
  have Vt_measurable: "?Vt \<in> measurable ?Mt borel"
    by (rule slp_euclidean_vector_constructor_measurable)
  have P_measurable:
    "?P \<in> measurable lborel (lborel :: (real^bool) measure)"
    by (rule slp_point_boolean_map_measurable)
  have T_measurable: "?T \<in> measurable ?Ms ?Mt"
  proof (rule measurable_PiM_single')
    fix i
    assume "i \<in> (UNIV::'i set)"
    have component:
      "(\<lambda>omega. omega i) \<in>
        measurable ?Ms (lborel :: slp_point measure)"
      by (rule measurable_component_singleton) simp
    show "(\<lambda>omega. ?T omega i) \<in>
      measurable ?Ms (lborel :: (real^bool) measure)"
      using measurable_compose[OF component P_measurable]
      by (simp only: comp_def)
  next
    show "?T \<in> space ?Ms \<rightarrow>
      PiE (UNIV::'i set) (\<lambda>_. space (lborel :: (real^bool) measure))"
    proof
      fix omega
      assume omega_space: "omega \<in> space ?Ms"
      show "?T omega \<in>
        PiE (UNIV::'i set) (\<lambda>_. space (lborel :: (real^bool) measure))"
      proof (simp only: PiE_iff, intro conjI)
        show "?T omega \<in> extensional (UNIV::'i set)"
          by (simp only: extensional_UNIV UNIV_I)
        show "\<forall>i\<in>(UNIV::'i set).
            ?T omega i \<in> space (lborel :: (real^bool) measure)"
        proof (intro ballI)
          fix i
          assume "i \<in> (UNIV::'i set)"
          have component_space:
            "omega i \<in> space (lborel :: slp_point measure)"
          proof -
            have omega_PiE:
              "omega \<in>
                PiE (UNIV::'i set)
                  (\<lambda>_. space (lborel :: slp_point measure))"
              using omega_space unfolding space_PiM .
            show ?thesis
              by (rule PiE_mem[OF omega_PiE UNIV_I])
          qed
          show "?T omega i \<in> space (lborel :: (real^bool) measure)"
            by (rule measurable_space[OF P_measurable component_space])
        qed
      qed
    qed
  qed
  have product_transport: "distr ?Ms ?Mt ?T = ?Mt"
  proof -
    have restricted:
      "distr ?Ms ?Mt
          (\<lambda>omega. \<lambda>i\<in>(UNIV::'i set). ?P (omega i)) = ?Mt"
    proof (rule source.slp_distr_PiM_componentwise)
      show "finite (UNIV::'i set)"
        by simp
      show "sigma_finite_measure (lborel :: (real^bool) measure)"
        for i :: 'i
        by standard
      show "?P \<in> measurable lborel (lborel :: (real^bool) measure)"
        for i :: 'i
        by (rule P_measurable)
      show "distr lborel (lborel :: (real^bool) measure) ?P =
          (lborel :: (real^bool) measure)"
        for i :: 'i
        by (rule slp_point_boolean_distr_lborel)
    qed
    have map_eq:
      "(\<lambda>omega. \<lambda>i\<in>(UNIV::'i set). ?P (omega i)) = ?T"
    proof (rule ext)
      fix omega
      show "(\<lambda>i\<in>(UNIV::'i set). ?P (omega i)) = ?T omega"
      proof (rule ext)
        fix i
        show "(\<lambda>i\<in>(UNIV::'i set). ?P (omega i)) i = ?T omega i"
          by (rule restrict_apply'[OF UNIV_I])
      qed
    qed
    show ?thesis
      using restricted by (simp only: map_eq)
  qed
  have composition:
    "slp_point_family_boolean_nested_pack \<circ> ?Vs = ?Vt \<circ> ?T"
  proof (rule ext)
    fix f
    show "(slp_point_family_boolean_nested_pack \<circ> ?Vs) f =
        (?Vt \<circ> ?T) f"
      unfolding comp_apply slp_point_family_boolean_nested_pack_def vec_eq_iff
      by (intro allI) (simp only: vec_lambda_beta)
  qed

  have
    "distr (lborel :: (slp_point^'i) measure) borel
        slp_point_family_boolean_nested_pack =
      distr (distr ?Ms borel ?Vs) borel
        slp_point_family_boolean_nested_pack"
    by (simp only: slp_lborel_cartesian_euclidean_vector_product)
  also have "... =
      distr ?Ms borel (slp_point_family_boolean_nested_pack \<circ> ?Vs)"
    by (rule distr_distr[
          OF slp_point_family_boolean_nested_pack_measurable Vs_measurable])
  also have "... = distr ?Ms borel (?Vt \<circ> ?T)"
    by (simp only: composition)
  also have "... = distr (distr ?Ms ?Mt ?T) borel ?Vt"
    by (rule distr_distr[OF Vt_measurable T_measurable, symmetric])
  also have "... = distr ?Mt borel ?Vt"
    by (simp only: product_transport)
  also have "... = (lborel :: ((real^bool)^'i) measure)"
    by (rule slp_lborel_cartesian_euclidean_vector_product[symmetric])
  finally show ?thesis .
qed

theorem slp_point_family_boolean_nested_distr_lborel:
  "distr (lborel :: (slp_point^'i::finite) measure)
      (lborel :: ((real^bool)^'i) measure)
      slp_point_family_boolean_nested_pack =
    (lborel :: ((real^bool)^'i) measure)"
proof -
  have target_change:
    "distr (lborel :: (slp_point^'i) measure)
        (lborel :: ((real^bool)^'i) measure)
        slp_point_family_boolean_nested_pack =
      distr (lborel :: (slp_point^'i) measure) borel
        slp_point_family_boolean_nested_pack"
  proof (rule distr_cong)
    show "(lborel :: (slp_point^'i) measure) = lborel"
      by (rule refl)
    show "sets (lborel :: ((real^bool)^'i) measure) = sets borel"
      by (rule sets_lborel)
    show "slp_point_family_boolean_nested_pack x =
        slp_point_family_boolean_nested_pack x"
      for x :: "slp_point^'i"
      by (rule refl)
  qed
  show ?thesis
    using target_change slp_point_family_boolean_nested_distr_borel
    by simp
qed

end
