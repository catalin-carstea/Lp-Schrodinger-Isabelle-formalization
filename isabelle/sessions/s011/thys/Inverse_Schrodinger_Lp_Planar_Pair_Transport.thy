theory Inverse_Schrodinger_Lp_Planar_Pair_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Hyperbolic_Iterated_Integral"
begin

section \<open>Lebesgue transport between the plane and a coordinate pair\<close>

definition slp_point_to_pair :: "slp_point \<Rightarrow> real \<times> real"
where
  "slp_point_to_pair x = (x $ 0, x $ 1)"

definition slp_pair_to_point :: "real \<times> real \<Rightarrow> slp_point"
where
  "slp_pair_to_point xy =
    (\<chi> i. if i = 0 then fst xy else snd xy)"

lemma slp_pair_to_point_to_pair [simp]:
  "slp_pair_to_point (slp_point_to_pair x) = x"
  unfolding vec_eq_iff
proof (intro allI)
  fix i
  have two_is_zero: "(2 :: 2) = 0"
    by simp
  have i_cases: "i = 1 \<or> i = (2 :: 2)"
    by (rule exhaust_2)
  show "slp_pair_to_point (slp_point_to_pair x) $ i = x $ i"
    using i_cases
    by (auto simp: slp_pair_to_point_def slp_point_to_pair_def two_is_zero)
qed

lemma slp_point_to_pair_to_point [simp]:
  "slp_point_to_pair (slp_pair_to_point xy) = xy"
  by (cases xy)
    (simp add: slp_point_to_pair_def slp_pair_to_point_def)

lemma slp_point_to_pair_linear:
  "linear slp_point_to_pair"
proof (rule linearI)
  show "slp_point_to_pair (x + y) =
      slp_point_to_pair x + slp_point_to_pair y" for x y
    by (simp add: slp_point_to_pair_def)
  show "slp_point_to_pair (r *\<^sub>R x) =
      r *\<^sub>R slp_point_to_pair x" for r x
    by (simp add: slp_point_to_pair_def)
qed

lemma slp_pair_to_point_linear:
  "linear slp_pair_to_point"
proof (rule linearI)
  show "slp_pair_to_point (x + y) =
      slp_pair_to_point x + slp_pair_to_point y" for x y
    unfolding slp_pair_to_point_def vec_eq_iff
    by simp
  show "slp_pair_to_point (r *\<^sub>R x) =
      r *\<^sub>R slp_pair_to_point x" for r x
    unfolding slp_pair_to_point_def vec_eq_iff
    by simp
qed

lemma slp_point_to_pair_measurable:
  "slp_point_to_pair \<in>
    measurable (borel :: slp_point measure) borel"
proof -
  have bounded: "bounded_linear slp_point_to_pair"
    using slp_point_to_pair_linear
    by (simp add: linear_conv_bounded_linear)
  have continuous: "continuous_on UNIV slp_point_to_pair"
    by (rule linear_continuous_on[OF bounded])
  show ?thesis
    using borel_measurable_continuous_onI[OF continuous] by simp
qed

lemma slp_pair_to_point_measurable:
  "slp_pair_to_point \<in>
    measurable (borel :: (real \<times> real) measure) borel"
proof -
  have bounded: "bounded_linear slp_pair_to_point"
    using slp_pair_to_point_linear
    by (simp add: linear_conv_bounded_linear)
  have continuous: "continuous_on UNIV slp_pair_to_point"
    by (rule linear_continuous_on[OF bounded])
  show ?thesis
    using borel_measurable_continuous_onI[OF continuous] by simp
qed

lemma slp_point_to_pair_distr_lborel:
  "distr (lborel :: slp_point measure) borel slp_point_to_pair = lborel"
proof (rule lborel_eqI[symmetric])
  fix l u :: "real \<times> real"
  assume ordered:
    "\<And>b. b \<in> Basis \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b"
  have to_pair_vimage_box:
      "slp_point_to_pair -` box l u =
        box (slp_pair_to_point l) (slp_pair_to_point u)"
  proof -
    have coordinate_cases: "i = 0 \<or> i = 1" for i :: 2
    proof -
      have two_is_zero: "(2 :: 2) = 0"
        by simp
      have raw_cases: "i = 1 \<or> i = (2 :: 2)"
        by (rule exhaust_2)
      show ?thesis
        using raw_cases two_is_zero by blast
    qed
    show ?thesis
    proof (rule equalityI)
      show "slp_point_to_pair -` box l u \<subseteq>
          box (slp_pair_to_point l) (slp_pair_to_point u)"
      proof
        fix x :: slp_point
        assume left: "x \<in> slp_point_to_pair -` box l u"
        have left_bounds:
            "fst l < x $ 0 \<and> x $ 0 < fst u \<and>
              snd l < x $ 1 \<and> x $ 1 < snd u"
          using left
          by (simp add: slp_point_to_pair_def box_prod)
        show "x \<in> box (slp_pair_to_point l) (slp_pair_to_point u)"
          unfolding mem_box_cart
        proof
          fix i
          show "slp_pair_to_point l $ i < x $ i \<and>
              x $ i < slp_pair_to_point u $ i"
            using coordinate_cases[of i] left_bounds
            by (auto simp: slp_pair_to_point_def)
        qed
      qed
      show "box (slp_pair_to_point l) (slp_pair_to_point u) \<subseteq>
          slp_point_to_pair -` box l u"
      proof
        fix x :: slp_point
        assume right:
          "x \<in> box (slp_pair_to_point l) (slp_pair_to_point u)"
        have bounds:
            "slp_pair_to_point l $ i < x $ i \<and>
              x $ i < slp_pair_to_point u $ i" for i
          using right unfolding mem_box_cart by blast
        have zero_bounds:
            "fst l < x $ 0 \<and> x $ 0 < fst u"
          using bounds[of 0]
          by (simp add: slp_pair_to_point_def)
        have one_bounds:
            "snd l < x $ 1 \<and> x $ 1 < snd u"
          using bounds[of 1]
          by (simp add: slp_pair_to_point_def)
        show "x \<in> slp_point_to_pair -` box l u"
          using zero_bounds one_bounds
          by (simp add: slp_point_to_pair_def box_prod)
      qed
    qed
  qed
  have joined_ordered:
      "\<And>b. b \<in> Basis \<Longrightarrow>
        slp_pair_to_point l \<bullet> b \<le>
          slp_pair_to_point u \<bullet> b"
  proof -
    fix b :: slp_point
    assume "b \<in> Basis"
    then obtain i where b_axis: "b = axis i 1"
      by (auto simp: Basis_vec_def)
    show "slp_pair_to_point l \<bullet> b \<le>
        slp_pair_to_point u \<bullet> b"
      using ordered[of "(1, 0)"] ordered[of "(0, 1)"]
      unfolding b_axis
      by (cases l; cases u; cases i)
        (auto simp: Basis_prod_def slp_pair_to_point_def
          inner_axis inner_prod_def)
  qed
  have joined_diff:
      "slp_pair_to_point u - slp_pair_to_point l =
        slp_pair_to_point (u - l)"
    by (metis linear_diff slp_pair_to_point_linear)
  have from_pair_basis_product:
      "(\<Prod>b\<in>Basis. slp_pair_to_point z \<bullet> b) =
        (\<Prod>b\<in>Basis. z \<bullet> b)" for z
    by (cases z)
      (simp add: slp_prod_inner_Basis_real_cartesian
        slp_pair_to_point_def UNIV_2 Basis_prod_def
        prod.union_disjoint prod.reindex_nontrivial inner_prod_def
        inner_axis exhaust_2 mult.commute)
  have box_sets:
      "box l u \<in> sets (borel :: (real \<times> real) measure)"
    by simp
  have joined_box_measure:
      "emeasure lborel
          (box (slp_pair_to_point l) (slp_pair_to_point u)) =
        (\<Prod>b\<in>Basis.
          (slp_pair_to_point u - slp_pair_to_point l) \<bullet> b)"
    by (rule emeasure_lborel_box; rule joined_ordered)
  have joined_box_measure_final:
      "emeasure lborel
          (box (slp_pair_to_point l) (slp_pair_to_point u)) =
        (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
    using joined_box_measure
    by (simp only: joined_diff from_pair_basis_product)
  have distr_box:
      "emeasure
          (distr (lborel :: slp_point measure) borel slp_point_to_pair)
          (box l u) =
        emeasure lborel
          (box (slp_pair_to_point l) (slp_pair_to_point u))"
  proof -
    have to_pair_lborel_measurable:
        "slp_point_to_pair \<in>
          measurable (lborel :: slp_point measure) borel"
      using slp_point_to_pair_measurable
      by (simp only: measurable_cong_sets[OF sets_lborel refl])
    show ?thesis
    apply (subst emeasure_distr[OF to_pair_lborel_measurable box_sets])
    apply (simp add: to_pair_vimage_box)
    done
  qed
  show "emeasure
      (distr (lborel :: slp_point measure) borel slp_point_to_pair)
      (box l u) = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
    by (rule trans[OF distr_box joined_box_measure_final])
next
  show "sets
      (distr (lborel :: slp_point measure) borel slp_point_to_pair) =
    sets borel"
    by simp
qed

lemma slp_pair_to_point_distr_lborel:
  "distr (lborel :: (real \<times> real) measure)
      borel slp_pair_to_point =
    (lborel :: slp_point measure)"
proof -
  have to_pair_lborel_measurable:
      "slp_point_to_pair \<in>
        measurable (lborel :: slp_point measure) borel"
    using slp_point_to_pair_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have composition:
      "slp_pair_to_point \<circ> slp_point_to_pair = id"
    by (rule ext) simp
  have
      "distr (lborel :: (real \<times> real) measure)
          borel slp_pair_to_point =
        distr
          (distr (lborel :: slp_point measure)
            borel slp_point_to_pair)
          borel slp_pair_to_point"
    by (simp only: slp_point_to_pair_distr_lborel)
  also have "... =
      distr (lborel :: slp_point measure) borel
        (slp_pair_to_point \<circ> slp_point_to_pair)"
    by (rule distr_distr[OF slp_pair_to_point_measurable
          to_pair_lborel_measurable])
  also have "... = distr (lborel :: slp_point measure) borel id"
    by (simp only: composition)
  also have "... = (lborel :: slp_point measure)"
    unfolding id_def
    by (rule distr_id2) (rule sym, rule sets_lborel)
  finally show ?thesis .
qed

lemma slp_pair_pullback_integrable:
  fixes F :: "slp_point \<Rightarrow> complex"
  assumes F_integrable: "integrable lborel F"
  shows "integrable (lborel :: (real \<times> real) measure)
    (\<lambda>xy. F (slp_pair_to_point xy))"
proof -
  have from_pair_lborel_measurable:
      "slp_pair_to_point \<in>
        measurable (lborel :: (real \<times> real) measure) borel"
    using slp_pair_to_point_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have F_measurable:
      "F \<in> borel_measurable (borel :: slp_point measure)"
    using F_integrable[THEN borel_measurable_integrable]
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  show ?thesis
    using integrable_distr_eq[
      OF from_pair_lborel_measurable F_measurable]
      F_integrable slp_pair_to_point_distr_lborel
    by simp
qed

lemma slp_pair_pullback_integral:
  fixes F :: "slp_point \<Rightarrow> complex"
  assumes F_integrable: "integrable lborel F"
  shows "integral\<^sup>L lborel F =
    integral\<^sup>L (lborel :: (real \<times> real) measure)
      (\<lambda>xy. F (slp_pair_to_point xy))"
proof -
  have from_pair_lborel_measurable:
      "slp_pair_to_point \<in>
        measurable (lborel :: (real \<times> real) measure) borel"
    using slp_pair_to_point_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have F_measurable:
      "F \<in> borel_measurable (borel :: slp_point measure)"
    using F_integrable[THEN borel_measurable_integrable]
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have transported:
      "integral\<^sup>L
          (distr (lborel :: (real \<times> real) measure)
            borel slp_pair_to_point) F =
        integral\<^sup>L (lborel :: (real \<times> real) measure)
          (\<lambda>xy. F (slp_pair_to_point xy))"
    using integral_distr[OF from_pair_lborel_measurable F_measurable]
    by simp
  show ?thesis
    using transported
    by (simp only: slp_pair_to_point_distr_lborel)
qed

end
