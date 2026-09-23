theory Inverse_Schrodinger_Lp_Cartesian_Euclidean_Product
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Point_Boolean_Lebesgue_Transport"
begin

section \<open>Finite products of Euclidean-valued Cartesian coordinates\<close>

lemma slp_lborel_cartesian_euclidean_vector_product:
  "(lborel :: ('a::euclidean_space^'n::finite) measure) =
    distr (PiM UNIV (\<lambda>_::'n. (lborel :: 'a measure))) borel
      (\<lambda>f. \<chi> i. f i)"
proof (rule lborel_eqI)
  interpret coordinates:
    product_sigma_finite "\<lambda>_::'n. (lborel :: 'a measure)"
    by standard
  fix l u :: "'a^'n"
  assume basis_le:
    "\<And>b. b \<in> Basis \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b"
  have component_le:
    "l $ i \<bullet> b \<le> u $ i \<bullet> b"
    if "b \<in> Basis"
    for i and b :: 'a
  proof -
    have "axis i b \<in> (Basis :: ('a^'n) set)"
      using that by (rule axis_in_Basis_iff[THEN iffD2])
    from basis_le[OF this] show ?thesis
      by (simp only: inner_axis)
  qed
  have vector_measurable:
    "(\<lambda>f. \<chi> i. f i) \<in>
      measurable (PiM UNIV (\<lambda>_::'n. (lborel :: 'a measure))) borel"
  proof -
    have coordinates_measurable:
      "(id :: ('n \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> 'a)) \<in>
        borel_measurable (PiM UNIV (\<lambda>_::'n. (lborel :: 'a measure)))"
    proof (rule measurable_coordinatewise_then_product)
      fix i
      show "(\<lambda>x. id x i) \<in>
        borel_measurable (PiM UNIV (\<lambda>_::'n. (lborel :: 'a measure)))"
        by (simp add: measurable_component_singleton
            cong: measurable_cong_sets)
    qed
    have vec_measurable:
      "vec_lambda \<in> borel_measurable
        (borel :: ('n \<Rightarrow> 'a) measure)"
      by (rule borel_measurable_continuous_onI)
        (intro continuous_on_vec_lambda, simp)
    show ?thesis
      using measurable_compose[OF coordinates_measurable vec_measurable]
      by (simp add: comp_def)
  qed
  have preimage:
    "(\<lambda>f. \<chi> i. f i) -` box l u \<inter>
        space (PiM UNIV (\<lambda>_::'n. (lborel :: 'a measure))) =
      PiE UNIV (\<lambda>i. box (l $ i) (u $ i))"
    by (auto simp: box_def space_PiM PiE_iff Basis_vec_def inner_axis)
  show
    "emeasure
        (distr (PiM UNIV (\<lambda>_::'n. (lborel :: 'a measure))) borel
          (\<lambda>f. \<chi> i. f i))
        (box l u) =
      (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
  proof -
    have
      "emeasure
          (distr (PiM UNIV (\<lambda>_::'n. (lborel :: 'a measure))) borel
            (\<lambda>f. \<chi> i. f i))
          (box l u) =
        emeasure (PiM UNIV (\<lambda>_::'n. (lborel :: 'a measure)))
          (PiE UNIV (\<lambda>i. box (l $ i) (u $ i)))"
      by (subst emeasure_distr[OF vector_measurable])
        (simp_all add: preimage)
    also have "... =
        (\<Prod>i\<in>(UNIV :: 'n set).
          emeasure lborel (box (l $ i) (u $ i)))"
      by (rule coordinates.emeasure_PiM) auto
    also have "... =
        (\<Prod>i\<in>(UNIV :: 'n set).
          (\<Prod>b\<in>(Basis :: 'a set). (u $ i - l $ i) \<bullet> b))"
    proof -
      have each_measure:
        "emeasure lborel (box (l $ i) (u $ i)) =
          ennreal (\<Prod>b\<in>(Basis :: 'a set).
            (u $ i - l $ i) \<bullet> b)"
        for i
        by (rule emeasure_lborel_box)
          (rule component_le)
      show ?thesis
        apply (simp only: each_measure)
        apply (rule prod_ennreal)
        apply (rule prod_nonneg)
        apply (simp add: inner_diff_left component_le)
        done
    qed
    also have "... = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
    proof -
      have axis_inj:
        "inj_on (axis i) (Basis :: 'a set)"
        for i :: 'n
        by (rule inj_onI)
          (auto simp: axis_eq_axis)
      have axis_disjoint:
        "axis i ` (Basis :: 'a set) \<inter> axis j ` Basis = {}"
        if "i \<noteq> j"
        for i j :: 'n
        using that by (auto simp: axis_eq_axis)
      have axis_product:
        "(\<Prod>x\<in>axis i ` (Basis :: 'a set). (u - l) \<bullet> x) =
          (\<Prod>b\<in>Basis. (u $ i - l $ i) \<bullet> b)"
        for i :: 'n
      proof (rule prod.reindex_cong)
        show "inj_on (axis i) (Basis :: 'a set)"
          by (rule axis_inj)
        show "axis i ` (Basis :: 'a set) = axis i ` Basis"
          by (rule refl)
        show "(u - l) \<bullet> axis i b = (u $ i - l $ i) \<bullet> b"
          if "b \<in> (Basis :: 'a set)"
          for b
          by (simp only: inner_axis vector_minus_component)
      qed
      have union_product:
        "(\<Prod>x\<in>(\<Union>i::'n. axis i ` (Basis :: 'a set)).
            (u - l) \<bullet> x) =
          (\<Prod>i\<in>UNIV.
            (\<Prod>x\<in>axis i ` (Basis :: 'a set). (u - l) \<bullet> x))"
      proof (rule prod.UNION_disjoint)
        show "finite (UNIV :: 'n set)"
          by simp
        show "\<forall>i\<in>(UNIV :: 'n set).
            finite (axis i ` (Basis :: 'a set))"
          by simp
        show "\<forall>i\<in>(UNIV :: 'n set). \<forall>j\<in>UNIV.
            i \<noteq> j \<longrightarrow>
              axis i ` (Basis :: 'a set) \<inter> axis j ` Basis = {}"
          using axis_disjoint by blast
      qed
      have basis_as_union:
        "(Basis :: ('a^'n) set) =
          (\<Union>i::'n. axis i ` (Basis :: 'a set))"
        by (simp only: Basis_vec_def UNION_singleton_eq_range)
      have real_product:
        "(\<Prod>i\<in>(UNIV :: 'n set).
            (\<Prod>b\<in>(Basis :: 'a set). (u $ i - l $ i) \<bullet> b)) =
          (\<Prod>b\<in>(Basis :: ('a^'n) set). (u - l) \<bullet> b)"
        using union_product
        by (simp only: basis_as_union axis_product)
      show ?thesis
        by (simp only: real_product)
    qed
    finally show ?thesis .
  qed
qed simp

end
