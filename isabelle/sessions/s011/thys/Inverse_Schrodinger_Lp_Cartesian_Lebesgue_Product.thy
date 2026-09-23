theory Inverse_Schrodinger_Lp_Cartesian_Lebesgue_Product
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Finite_Product_Reindex"
begin

section \<open>Cartesian Lebesgue measure as a finite scalar product\<close>

lemma slp_lborel_cartesian_vector_product:
  "(lborel :: (real^'n::finite) measure) =
    distr (PiM UNIV (\<lambda>_::'n. (lborel :: real measure))) borel
      (\<lambda>f. \<chi> i. f i)"
proof (rule lborel_eqI)
  interpret coordinates:
    product_sigma_finite "\<lambda>_::'n. (lborel :: real measure)"
    by standard
  fix l u :: "real^'n"
  assume basis_le:
    "\<And>b. b \<in> Basis \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b"
  have component_le: "l $ i \<le> u $ i" for i
  proof -
    have "axis i 1 \<in> (Basis :: (real^'n) set)"
      by simp
    from basis_le[OF this] show ?thesis
      by (simp add: inner_axis)
  qed
  have vector_measurable:
    "(\<lambda>f. \<chi> i. f i) \<in>
      measurable (PiM UNIV (\<lambda>_::'n. (lborel :: real measure))) borel"
  proof -
    have coordinates_measurable:
      "(id :: ('n \<Rightarrow> real) \<Rightarrow> ('n \<Rightarrow> real)) \<in>
        borel_measurable (PiM UNIV (\<lambda>_::'n. (lborel :: real measure)))"
    proof (rule measurable_coordinatewise_then_product)
      fix i
      show "(\<lambda>x. id x i) \<in>
        borel_measurable (PiM UNIV (\<lambda>_::'n. (lborel :: real measure)))"
        by (simp add: measurable_component_singleton cong: measurable_cong_sets)
    qed
    have vec_measurable:
      "vec_lambda \<in> borel_measurable
        (borel :: ('n \<Rightarrow> real) measure)"
      by (rule borel_measurable_continuous_onI)
        (intro continuous_on_vec_lambda, simp)
    show ?thesis
      using measurable_compose[OF coordinates_measurable vec_measurable]
      by (simp add: comp_def)
  qed
  have preimage:
    "(\<lambda>f. \<chi> i. f i) -` box l u \<inter>
        space (PiM UNIV (\<lambda>_::'n. (lborel :: real measure))) =
      PiE UNIV (\<lambda>i. {l $ i<..<u $ i})"
    by (auto simp: box_def space_PiM PiE_iff Basis_vec_def
        Basis_real_def inner_axis axis_eq_axis)
  show
    "emeasure
        (distr (PiM UNIV (\<lambda>_::'n. (lborel :: real measure))) borel
          (\<lambda>f. \<chi> i. f i))
        (box l u) =
      (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
  proof -
    have
      "emeasure
          (distr (PiM UNIV (\<lambda>_::'n. (lborel :: real measure))) borel
            (\<lambda>f. \<chi> i. f i))
          (box l u) =
        emeasure (PiM UNIV (\<lambda>_::'n. (lborel :: real measure)))
          (PiE UNIV (\<lambda>i. {l $ i<..<u $ i}))"
      by (subst emeasure_distr[OF vector_measurable])
        (simp_all add: preimage)
    also have "... =
        (\<Prod>i\<in>(UNIV :: 'n set).
          emeasure lborel {l $ i<..<u $ i})"
      by (rule coordinates.emeasure_PiM) auto
    also have "... = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
      using component_le
      by (simp add: Basis_vec_def Basis_real_def inner_axis axis_eq_axis
          UNION_singleton_eq_range prod.reindex inj_on_def prod_ennreal)
    finally show ?thesis .
  qed
qed simp

end
