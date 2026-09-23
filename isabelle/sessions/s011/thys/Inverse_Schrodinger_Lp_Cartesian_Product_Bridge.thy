theory Inverse_Schrodinger_Lp_Cartesian_Product_Bridge
  imports Inverse_Schrodinger_Lp_Cartesian_Coordinates
begin

section \<open>Passive/active product coordinates\<close>

text \<open>
  The signed Cartesian output has one complex passive coordinate and a finite
  complex active tail.  The following maps merely regroup the corresponding
  real and imaginary Cartesian coordinates into the product type consumed by
  the finite quadratic Riemann--Lebesgue theorem.
\<close>

definition slp_signed_cartesian_to_product ::
  "real^((unit + 'i::finite) \<times> bool) \<Rightarrow>
    (real^bool) \<times> (real^('i \<times> bool))"
where
  "slp_signed_cartesian_to_product x =
    ((\<chi> b. x $ (Inl (), b)),
      (\<chi> ib. x $ (Inr (fst ib), snd ib)))"

definition slp_signed_product_to_cartesian ::
  "((real^bool) \<times> (real^('i::finite \<times> bool))) \<Rightarrow>
    real^((unit + 'i) \<times> bool)"
where
  "slp_signed_product_to_cartesian cu =
    (\<chi> kb. case fst kb of
      Inl _ \<Rightarrow> fst cu $ snd kb
    | Inr i \<Rightarrow> snd cu $ (i, snd kb))"

lemma slp_signed_product_to_cartesian_to_product:
  "slp_signed_product_to_cartesian
      (slp_signed_cartesian_to_product x) = x"
  unfolding vec_eq_iff
  by (auto simp: slp_signed_cartesian_to_product_def
      slp_signed_product_to_cartesian_def split: sum.splits)

lemma slp_signed_cartesian_to_product_to_cartesian:
  "slp_signed_cartesian_to_product
      (slp_signed_product_to_cartesian cu) = cu"
  by (cases cu)
    (auto simp: slp_signed_cartesian_to_product_def
      slp_signed_product_to_cartesian_def vec_eq_iff)

lemma slp_signed_cartesian_to_product_linear:
  "linear (slp_signed_cartesian_to_product ::
    real^((unit + 'i::finite) \<times> bool) \<Rightarrow>
      (real^bool) \<times> (real^('i \<times> bool)))"
proof (rule linearI)
  show "slp_signed_cartesian_to_product (x + y) =
      slp_signed_cartesian_to_product x +
        slp_signed_cartesian_to_product y"
    for x y :: "real^((unit + 'i) \<times> bool)"
    by (simp add: slp_signed_cartesian_to_product_def vec_eq_iff)
  show "slp_signed_cartesian_to_product (r *\<^sub>R x) =
      r *\<^sub>R slp_signed_cartesian_to_product x"
    for r and x :: "real^((unit + 'i) \<times> bool)"
    by (simp add: slp_signed_cartesian_to_product_def vec_eq_iff)
qed

lemma slp_signed_product_to_cartesian_linear:
  "linear (slp_signed_product_to_cartesian ::
    ((real^bool) \<times> (real^('i::finite \<times> bool))) \<Rightarrow>
      real^((unit + 'i) \<times> bool))"
proof (rule linearI)
  show "slp_signed_product_to_cartesian (x + y) =
      slp_signed_product_to_cartesian x +
        slp_signed_product_to_cartesian y"
    for x y :: "(real^bool) \<times> (real^('i \<times> bool))"
    unfolding vec_eq_iff
    by (auto simp: slp_signed_product_to_cartesian_def split: sum.splits)
  show "slp_signed_product_to_cartesian (r *\<^sub>R x) =
      r *\<^sub>R slp_signed_product_to_cartesian x"
    for r and x :: "(real^bool) \<times> (real^('i \<times> bool))"
    unfolding vec_eq_iff
    by (auto simp: slp_signed_product_to_cartesian_def split: sum.splits)
qed

lemma slp_signed_cartesian_to_product_bij:
  "bij (slp_signed_cartesian_to_product ::
    real^((unit + 'i::finite) \<times> bool) \<Rightarrow>
      (real^bool) \<times> (real^('i \<times> bool)))"
proof (rule bijI)
  show "inj (slp_signed_cartesian_to_product ::
      real^((unit + 'i) \<times> bool) \<Rightarrow>
        (real^bool) \<times> (real^('i \<times> bool)))"
    by (rule injI)
      (metis slp_signed_product_to_cartesian_to_product)
  show "surj (slp_signed_cartesian_to_product ::
      real^((unit + 'i) \<times> bool) \<Rightarrow>
        (real^bool) \<times> (real^('i \<times> bool)))"
    by (rule surjI[where f = slp_signed_product_to_cartesian])
      (rule slp_signed_cartesian_to_product_to_cartesian)
qed

lemma slp_signed_product_to_cartesian_bij:
  "bij (slp_signed_product_to_cartesian ::
    ((real^bool) \<times> (real^('i::finite \<times> bool))) \<Rightarrow>
      real^((unit + 'i) \<times> bool))"
proof (rule bijI)
  show "inj (slp_signed_product_to_cartesian ::
      ((real^bool) \<times> (real^('i \<times> bool))) \<Rightarrow>
        real^((unit + 'i) \<times> bool))"
    by (rule injI)
      (metis slp_signed_cartesian_to_product_to_cartesian)
  show "surj (slp_signed_product_to_cartesian ::
      ((real^bool) \<times> (real^('i \<times> bool))) \<Rightarrow>
        real^((unit + 'i) \<times> bool))"
    by (rule surjI[where f = slp_signed_cartesian_to_product])
      (rule slp_signed_product_to_cartesian_to_product)
qed

definition slp_signed_complex_pair_pack ::
  "(complex \<times> ('i::finite \<Rightarrow> complex)) \<Rightarrow>
    (real^bool) \<times> (real^('i \<times> bool))"
where
  "slp_signed_complex_pair_pack cu =
    ((\<chi> b. if b then Im (fst cu) else Re (fst cu)),
      (\<chi> ib. if snd ib then Im (snd cu (fst ib))
        else Re (snd cu (fst ib))))"

lemma slp_signed_cartesian_split_product_coordinates:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  shows
    "slp_signed_cartesian_to_product
        (slp_signed_cartesian_split epsilon x) =
      slp_signed_complex_pair_pack
        (slp_signed_coordinate_split epsilon
          (slp_complex_family_unpack x))"
  unfolding slp_signed_cartesian_split_def
    slp_signed_cartesian_to_product_def
    slp_signed_complex_pair_pack_def
    slp_signed_pair_to_family_def
    slp_complex_family_pack_def
  by (simp add: o_def vec_eq_iff split: sum.splits)

lemma slp_signed_cartesian_to_product_measurable:
  "slp_signed_cartesian_to_product \<in>
    measurable (lborel :: (real^((unit + 'i::finite) \<times> bool)) measure)
      lborel"
proof -
  have bounded:
    "bounded_linear (slp_signed_cartesian_to_product ::
      real^((unit + 'i) \<times> bool) \<Rightarrow>
        (real^bool) \<times> (real^('i \<times> bool)))"
    using slp_signed_cartesian_to_product_linear
    by (simp add: linear_conv_bounded_linear)
  have continuous:
    "continuous_on UNIV (slp_signed_cartesian_to_product ::
      real^((unit + 'i) \<times> bool) \<Rightarrow>
        (real^bool) \<times> (real^('i \<times> bool)))"
    by (rule linear_continuous_on[OF bounded])
  show ?thesis
    using borel_measurable_continuous_onI[OF continuous] by simp
qed

lemma slp_signed_product_to_cartesian_measurable:
  "slp_signed_product_to_cartesian \<in>
    measurable (lborel ::
      ((real^bool) \<times> (real^('i::finite \<times> bool))) measure) lborel"
proof -
  have bounded:
    "bounded_linear (slp_signed_product_to_cartesian ::
      ((real^bool) \<times> (real^('i \<times> bool))) \<Rightarrow>
        real^((unit + 'i) \<times> bool))"
    using slp_signed_product_to_cartesian_linear
    by (simp add: linear_conv_bounded_linear)
  have continuous:
    "continuous_on UNIV (slp_signed_product_to_cartesian ::
      ((real^bool) \<times> (real^('i \<times> bool))) \<Rightarrow>
        real^((unit + 'i) \<times> bool))"
    by (rule linear_continuous_on[OF bounded])
  show ?thesis
    using borel_measurable_continuous_onI[OF continuous] by simp
qed

lemma slp_signed_cartesian_to_product_vimage_box:
  "slp_signed_cartesian_to_product -` box l u =
    box (slp_signed_product_to_cartesian l)
      (slp_signed_product_to_cartesian u)"
  by (rule set_eqI)
    (auto simp: box_prod mem_box_cart
      slp_signed_cartesian_to_product_def
      slp_signed_product_to_cartesian_def split: sum.splits)

lemma slp_prod_inner_Basis_real_cartesian:
  fixes z :: "real^'a::finite"
  shows "(\<Prod>b\<in>Basis. z \<bullet> b) = (\<Prod>i\<in>UNIV. z $ i)"
  by (simp add: Basis_vec_def UNION_singleton_eq_range prod.reindex
      axis_eq_axis inj_on_def inner_axis)

lemma slp_prod_sum_bool_split:
  fixes f :: "((unit + 'i::finite) \<times> bool) \<Rightarrow>
    'a::comm_monoid_mult"
  shows "(\<Prod>k\<in>UNIV. f k) =
    (\<Prod>b\<in>UNIV. f (Inl (), b)) *
      (\<Prod>ib\<in>UNIV. f (Inr (fst ib), snd ib))"
proof -
  have univ_split:
    "(UNIV :: ((unit + 'i) \<times> bool) set) =
      (\<lambda>b. (Inl (), b)) ` UNIV \<union>
        (\<lambda>ib. (Inr (fst ib), snd ib)) ` UNIV"
  proof (rule set_eqI)
    fix k :: "(unit + 'i) \<times> bool"
    show "k \<in> UNIV \<longleftrightarrow>
        k \<in> (\<lambda>b. (Inl (), b)) ` UNIV \<union>
          (\<lambda>ib. (Inr (fst ib), snd ib)) ` UNIV"
    proof
      assume "k \<in> UNIV"
      obtain s b where k: "k = (s, b)"
        by (cases k)
      show "k \<in> (\<lambda>b. (Inl (), b)) ` UNIV \<union>
          (\<lambda>ib. (Inr (fst ib), snd ib)) ` UNIV"
      proof (cases s)
        case (Inl a)
        then have "a = ()" by simp
        with Inl k show ?thesis
          by (intro UnI1 image_eqI[where x = b]) simp_all
      next
        case (Inr i)
        with k show ?thesis
          by (intro UnI2 image_eqI[where x = "(i, b)"]) simp_all
      qed
    next
      assume "k \<in> (\<lambda>b. (Inl (), b)) ` UNIV \<union>
          (\<lambda>ib. (Inr (fst ib), snd ib)) ` UNIV"
      show "k \<in> UNIV" by simp
    qed
  qed
  have left_inj:
    "inj_on (\<lambda>b. (Inl (), b)) (UNIV :: bool set)"
    by (rule inj_onI) simp
  have right_inj:
    "inj_on (\<lambda>ib::'i \<times> bool. (Inr (fst ib), snd ib)) UNIV"
    by (rule inj_onI) auto
  have disjoint:
    "(\<lambda>b. (Inl (), b)) ` (UNIV :: bool set) \<inter>
      (\<lambda>ib::'i \<times> bool. (Inr (fst ib), snd ib)) ` UNIV = {}"
    by auto
  show ?thesis
    unfolding univ_split
    using disjoint
    by (simp add: prod.union_disjoint prod.reindex[OF left_inj]
        prod.reindex[OF right_inj])
qed

lemma slp_prod_inner_Basis_cartesian_product:
  fixes z :: "(real^bool) \<times> (real^('i::finite \<times> bool))"
  shows "(\<Prod>b\<in>Basis. z \<bullet> b) =
    (\<Prod>k\<in>UNIV. fst z $ k) * (\<Prod>k\<in>UNIV. snd z $ k)"
proof -
  have pair_basis:
    "(\<Prod>b\<in>Basis. z \<bullet> b) =
      (\<Prod>b\<in>Basis. fst z \<bullet> b) *
        (\<Prod>b\<in>Basis. snd z \<bullet> b)"
    unfolding Basis_prod_def
    using Basis_zero
    apply (simp add: prod.union_disjoint disjoint_iff image_iff ball_Un
        prod.reindex_nontrivial)
    apply (subst (1 2) prod.reindex_nontrivial)
    apply (auto simp: inner_prod_def)
    done
  show ?thesis
    using pair_basis
    by (simp add: slp_prod_inner_Basis_real_cartesian)
qed

lemma slp_signed_product_to_cartesian_basis_product:
  fixes z :: "(real^bool) \<times> (real^('i::finite \<times> bool))"
  shows "(\<Prod>b\<in>Basis.
      slp_signed_product_to_cartesian z \<bullet> b) =
    (\<Prod>b\<in>Basis. z \<bullet> b)"
  by (simp add: slp_prod_inner_Basis_real_cartesian
      slp_prod_inner_Basis_cartesian_product slp_prod_sum_bool_split
      slp_signed_product_to_cartesian_def)

theorem slp_signed_cartesian_to_product_distr_lborel:
  "distr lborel lborel (slp_signed_cartesian_to_product ::
    real^((unit + 'i::finite) \<times> bool) \<Rightarrow>
      (real^bool) \<times> (real^('i \<times> bool))) = lborel"
proof (rule lborel_eqI[symmetric])
  fix l u :: "(real^bool) \<times> (real^('i \<times> bool))"
  assume ordered:
    "\<And>b. b \<in> Basis \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b"
  show "emeasure
      (distr lborel lborel
        (slp_signed_cartesian_to_product ::
          real^((unit + 'i) \<times> bool) \<Rightarrow>
            (real^bool) \<times> (real^('i \<times> bool))))
      (box l u) = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
  proof -
    have joined_ordered:
      "\<And>b. b \<in> Basis \<Longrightarrow>
        slp_signed_product_to_cartesian l \<bullet> b \<le>
          slp_signed_product_to_cartesian u \<bullet> b"
    proof -
      have passive_ordered:
        "fst l $ b \<le> fst u $ b" for b
      proof -
        have axis_basis:
          "axis b 1 \<in> (Basis :: (real^bool) set)"
          by simp
        have "(axis b 1, 0) \<in>
            (Basis :: ((real^bool) \<times>
              (real^('i \<times> bool))) set)"
          unfolding Basis_prod_def
          by (intro UnI1 image_eqI[where x = "axis b 1"])
            (simp_all add: axis_basis)
        from ordered[OF this] show ?thesis
          by (simp add: inner_prod_def inner_axis)
      qed
      have active_ordered:
        "snd l $ ib \<le> snd u $ ib" for ib
      proof -
        have axis_basis:
          "axis ib 1 \<in> (Basis :: (real^('i \<times> bool)) set)"
          by simp
        have "(0, axis ib 1) \<in>
            (Basis :: ((real^bool) \<times>
              (real^('i \<times> bool))) set)"
          unfolding Basis_prod_def
          by (intro UnI2 image_eqI[where x = "axis ib 1"])
            (simp_all add: axis_basis)
        from ordered[OF this] show ?thesis
          by (simp add: inner_prod_def inner_axis)
      qed
      fix b :: "real^((unit + 'i) \<times> bool)"
      assume "b \<in> Basis"
      then obtain k where b_axis: "b = axis k 1"
        by (auto simp: Basis_vec_def)
      obtain s bit where k_pair: "k = (s, bit)"
        by (cases k)
      show "slp_signed_product_to_cartesian l \<bullet> b \<le>
          slp_signed_product_to_cartesian u \<bullet> b"
        using passive_ordered active_ordered
        unfolding b_axis k_pair
        by (cases s)
          (simp_all add: slp_signed_product_to_cartesian_def inner_axis)
    qed
    have joined_diff:
      "slp_signed_product_to_cartesian u -
          slp_signed_product_to_cartesian l =
        slp_signed_product_to_cartesian (u - l)"
      by (metis linear_diff slp_signed_product_to_cartesian_linear)
    have box_sets:
      "box l u \<in> sets (lborel ::
        ((real^bool) \<times> (real^('i \<times> bool))) measure)"
      by simp
    have joined_box_measure:
      "emeasure lborel
          (box (slp_signed_product_to_cartesian l)
            (slp_signed_product_to_cartesian u)) =
        (\<Prod>b\<in>Basis.
          (slp_signed_product_to_cartesian u -
            slp_signed_product_to_cartesian l) \<bullet> b)"
      by (rule emeasure_lborel_box; rule joined_ordered)
    have joined_box_measure_final:
      "emeasure lborel
          (box (slp_signed_product_to_cartesian l)
            (slp_signed_product_to_cartesian u)) =
        (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
      using joined_box_measure
      by (simp only: joined_diff
          slp_signed_product_to_cartesian_basis_product)
    have distr_box:
      "emeasure
          (distr lborel lborel
            (slp_signed_cartesian_to_product ::
              real^((unit + 'i) \<times> bool) \<Rightarrow>
                (real^bool) \<times> (real^('i \<times> bool))))
          (box l u) =
        emeasure lborel
          (box (slp_signed_product_to_cartesian l)
            (slp_signed_product_to_cartesian u))"
      apply (subst emeasure_distr[OF
          slp_signed_cartesian_to_product_measurable box_sets])
      apply (simp add: slp_signed_cartesian_to_product_vimage_box)
      done
    show ?thesis
      by (rule trans[OF distr_box joined_box_measure_final])
  qed
next
  show "sets
      (distr lborel lborel
        (slp_signed_cartesian_to_product ::
          real^((unit + 'i) \<times> bool) \<Rightarrow>
            (real^bool) \<times> (real^('i \<times> bool)))) = sets borel"
    by simp
qed

corollary slp_signed_cartesian_product_integrable_iff:
  fixes F :: "((real^bool) \<times> (real^('i::finite \<times> bool))) \<Rightarrow>
    'a::{banach, second_countable_topology}"
  assumes F_measurable: "F \<in> borel_measurable lborel"
  shows "integrable lborel F \<longleftrightarrow>
    integrable lborel (\<lambda>x. F (slp_signed_cartesian_to_product x))"
  using integrable_distr_eq[
    OF slp_signed_cartesian_to_product_measurable F_measurable]
  by (simp only: slp_signed_cartesian_to_product_distr_lborel)

corollary slp_signed_cartesian_product_integral:
  fixes F :: "((real^bool) \<times> (real^('i::finite \<times> bool))) \<Rightarrow>
    'a::{banach, second_countable_topology}"
  assumes F_measurable: "F \<in> borel_measurable lborel"
  shows "integral\<^sup>L lborel F =
    integral\<^sup>L lborel
      (\<lambda>x. F (slp_signed_cartesian_to_product x))"
  using integral_distr[
    OF slp_signed_cartesian_to_product_measurable F_measurable]
  by (simp only: slp_signed_cartesian_to_product_distr_lborel)

end
