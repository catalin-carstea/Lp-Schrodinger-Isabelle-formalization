theory Inverse_Schrodinger_Lp_Cartesian_Lebesgue_Reindex
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cartesian_Lebesgue_Product"
begin

section \<open>Bijective reindexing of Cartesian Lebesgue coordinates\<close>

lemma slp_cartesian_vector_constructor_measurable:
  "(\<lambda>f. \<chi> i. f i) \<in>
    measurable (PiM UNIV (\<lambda>_::'n::finite. (lborel :: real measure))) borel"
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

lemma slp_cartesian_coordinate_reindex_linear:
  fixes t :: "'b::finite \<Rightarrow> 'a::finite"
  shows "linear (\<lambda>x::real^'a. \<chi> j. x $ t j)"
  by (rule linearI) (simp_all add: vec_eq_iff)

lemma slp_cartesian_coordinate_reindex_measurable:
  fixes t :: "'b::finite \<Rightarrow> 'a::finite"
  shows "(\<lambda>x::real^'a. \<chi> j. x $ t j) \<in>
    measurable borel borel"
proof -
  have bounded:
    "bounded_linear (\<lambda>x::real^'a. \<chi> j. x $ t j)"
    using slp_cartesian_coordinate_reindex_linear[of t]
    by (simp add: linear_conv_bounded_linear)
  have continuous:
    "continuous_on UNIV (\<lambda>x::real^'a. \<chi> j. x $ t j)"
    by (rule linear_continuous_on[OF bounded])
  show ?thesis
    by (rule borel_measurable_continuous_onI[OF continuous])
qed

lemma slp_lborel_cartesian_coordinate_reindex:
  fixes t :: "'b::finite \<Rightarrow> 'a::finite"
  assumes t_bij: "bij t"
  shows
    "distr (lborel :: (real^'a) measure) borel
        (\<lambda>x. \<chi> j. x $ t j) =
      (lborel :: (real^'b) measure)"
proof -
  let ?Pa = "PiM (UNIV::'a set) (\<lambda>_. (lborel :: real measure))"
  let ?Pb = "PiM (UNIV::'b set) (\<lambda>_. (lborel :: real measure))"
  let ?Va = "\<lambda>f::'a \<Rightarrow> real. \<chi> i. f i"
  let ?Vb = "\<lambda>f::'b \<Rightarrow> real. \<chi> j. f j"
  let ?R = "\<lambda>x::real^'a. \<chi> j. x $ t j"
  let ?T = "\<lambda>omega::'a \<Rightarrow> real. \<lambda>j. omega (t j)"

  interpret scalar:
    product_sigma_finite "\<lambda>_::'a. (lborel :: real measure)"
    by standard

  have Va_measurable: "?Va \<in> measurable ?Pa borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have Vb_measurable: "?Vb \<in> measurable ?Pb borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have R_measurable: "?R \<in> measurable borel borel"
    by (rule slp_cartesian_coordinate_reindex_measurable)
  have T_measurable: "?T \<in> measurable ?Pa ?Pb"
  proof (rule measurable_PiM_single')
    fix j
    assume "j \<in> (UNIV::'b set)"
    show "(\<lambda>omega. omega (t j)) \<in> measurable ?Pa lborel"
    proof (rule measurable_component_singleton)
      show "t j \<in> (UNIV::'a set)"
        by simp
    qed
  next
    show "(\<lambda>omega j. omega (t j)) \<in>
      space ?Pa \<rightarrow> PiE (UNIV::'b set) (\<lambda>_. space lborel)"
      by simp
  qed
  have product_reindex: "distr ?Pa ?Pb ?T = ?Pb"
  proof -
    have restricted:
      "distr ?Pa ?Pb (\<lambda>omega. \<lambda>j\<in>(UNIV::'b set). omega (t j)) =
        ?Pb"
      using scalar.slp_distr_PiM_reindex_bij_betw[
        of "UNIV::'b set" "UNIV::'a set" t] t_bij
      by simp
    have map_eq:
      "(\<lambda>omega. \<lambda>j\<in>(UNIV::'b set). omega (t j)) = ?T"
      by (rule ext)+ simp
    show ?thesis
      using restricted by (simp only: map_eq)
  qed
  have composition: "?R \<circ> ?Va = ?Vb \<circ> ?T"
    by (rule ext) (simp add: fun_eq_iff)

  have "distr (lborel :: (real^'a) measure) borel ?R =
      distr (distr ?Pa borel ?Va) borel ?R"
    by (simp only: slp_lborel_cartesian_vector_product)
  also have "... = distr ?Pa borel (?R \<circ> ?Va)"
    by (rule distr_distr[OF R_measurable Va_measurable])
  also have "... = distr ?Pa borel (?Vb \<circ> ?T)"
    by (simp only: composition)
  also have "... = distr (distr ?Pa ?Pb ?T) borel ?Vb"
    by (rule distr_distr[OF Vb_measurable T_measurable, symmetric])
  also have "... = distr ?Pb borel ?Vb"
    by (simp only: product_reindex)
  also have "... = (lborel :: (real^'b) measure)"
    by (rule slp_lborel_cartesian_vector_product[symmetric])
  finally show ?thesis .
qed

end
