theory Inverse_Schrodinger_Lp_Localized_Cauchy_Kernel_Lp
  imports
    Inverse_Schrodinger_Lp_Localized_Cauchy_Kernel
    Inverse_Schrodinger_Lp_Cartesian_Product_Bridge
    "HOL-Analysis.Ball_Volume"
begin

section \<open>Power integrability of the localized kernel below two\<close>

definition slp_coordinate_majorant ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_coordinate_majorant R s x =
    (if abs (x $ 0) \<le> R \<and> abs (x $ 1) \<le> R then
      (abs (x $ 0)) powr (-s / 2) *
        (abs (x $ 1)) powr (-s / 2)
    else 0)"

lemma slp_abs_powr_half_integrable_on_symmetric_interval:
  assumes radius_nonnegative: "0 \<le> R"
    and exponent_upper: "s < 2"
  shows "(\<lambda>x::real. abs x powr (-s / 2)) integrable_on {-R..R}"
proof -
  have power_lower: "-1 < -s / 2"
    using exponent_upper by linarith
  have positive_half:
    "(\<lambda>x::real. x powr (-s / 2)) integrable_on {0..R}"
    by (rule integrable_on_powr_from_0[OF power_lower radius_nonnegative])
  have negative_half:
    "(\<lambda>x::real. abs x powr (-s / 2)) integrable_on {-R..0}"
  proof -
    have reflected:
      "(\<lambda>x::real. (-x) powr (-s / 2)) integrable_on {-R..0}"
    proof -
      have reflect_iff:
        "((\<lambda>x::real. (-x) powr (-s / 2)) integrable_on {-R..0})
          \<longleftrightarrow>
        ((\<lambda>x::real. x powr (-s / 2)) integrable_on {0..R})"
        using Henstock_Kurzweil_Integration.integrable_reflect_real[
          where f="\<lambda>x::real. x powr (-s / 2)" and a=0 and b=R]
        by simp
      from reflect_iff positive_half show ?thesis
        by blast
    qed
    show ?thesis
      by (rule integrable_eq[OF reflected]) auto
  qed
  have positive_abs:
    "(\<lambda>x::real. abs x powr (-s / 2)) integrable_on {0..R}"
    by (rule integrable_eq[OF positive_half]) auto
  have joined:
    "(\<lambda>x::real. abs x powr (-s / 2))
      integrable_on ({-R..0} \<union> {0..R})"
  proof (rule integrable_Un[OF _ negative_half positive_abs])
    have "{-R..0} \<inter> {0..R} = {0}"
      using radius_nonnegative by auto
    then show "negligible ({-R..0} \<inter> {0..R})"
      by simp
  qed
  have union_eq: "{-R..0} \<union> {0..R} = {-R..R}"
    using radius_nonnegative by auto
  show ?thesis
    using joined by (simp only: union_eq)
qed

lemma slp_coordinate_majorant_borel_measurable:
  "slp_coordinate_majorant R s \<in> borel_measurable lborel"
  unfolding slp_coordinate_majorant_def
  by measurable

lemma slp_coordinate_majorant_integrable:
  assumes radius_nonnegative: "0 \<le> R"
    and exponent_upper: "s < 2"
  shows "integrable lborel (slp_coordinate_majorant R s)"
proof -
  let ?h = "\<lambda>x::real. abs x powr (-s / 2)"
  let ?g = "\<lambda>x::real. indicator {-R..R} x * ?h x"
  let ?F = "\<lambda>xy::real \<times> real.
    ?g (fst xy) * ?g (snd xy)"

  have interval_integrable: "?h integrable_on {-R..R}"
    by (rule slp_abs_powr_half_integrable_on_symmetric_interval[
          OF radius_nonnegative exponent_upper])
  have interval_absolute: "?h absolutely_integrable_on {-R..R}"
  proof -
    have nonnegative: "\<And>x. x \<in> {-R..R} \<Longrightarrow> 0 \<le> ?h x"
      by simp
    have equivalence:
      "?h absolutely_integrable_on {-R..R} \<longleftrightarrow>
        ?h integrable_on {-R..R}"
      by (rule absolutely_integrable_on_iff_nonneg[OF nonnegative])
    show ?thesis
      using equivalence interval_integrable by blast
  qed
  have interval_lborel:
    "integrable lborel ?g"
    using interval_absolute[unfolded set_integrable_def]
    by (subst (asm) integrable_completion) auto

  have pair_measurable:
    "?F \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have pair_fibers:
    "AE x in lborel. integrable lborel (\<lambda>y. ?F (x, y))"
  proof (rule AE_I2)
    fix x :: real
    have scalar_integrable:
      "integrable lborel (\<lambda>y. ?g x * ?g y)"
      using interval_lborel by (rule integrable_mult_right)
    show "integrable lborel (\<lambda>y. ?F (x, y))"
      using scalar_integrable by simp
  qed
  have iterated_integrable:
    "integrable lborel (\<lambda>x. \<integral>y. norm (?F (x, y)) \<partial>lborel)"
  proof -
    have g_nonnegative: "0 \<le> ?g x" for x
      by simp
    have fiber_eq:
      "(\<lambda>x. \<integral>y. norm (?F (x, y)) \<partial>lborel) =
        (\<lambda>x. integral\<^sup>L lborel (\<lambda>y. ?g x * ?g y))"
      by (rule ext) (simp add: g_nonnegative)
    have integral_eq:
      "(\<lambda>x. integral\<^sup>L lborel (\<lambda>y. ?g x * ?g y)) =
        (\<lambda>x. ?g x * integral\<^sup>L lborel ?g)"
      by (rule ext) simp
    show ?thesis
      unfolding fiber_eq integral_eq
      using interval_lborel by simp
  qed
  have pair_integrable:
    "integrable (lborel \<Otimes>\<^sub>M lborel) ?F"
    by (rule lborel_pair.Fubini_integrable[
          OF pair_measurable iterated_integrable pair_fibers])
  have product_integrable:
    "integrable (lborel :: (real \<times> real) measure) ?F"
    using pair_integrable by (simp only: lborel_prod)

  define to_pair :: "slp_point \<Rightarrow> real \<times> real" where
    "to_pair x = (x $ 0, x $ 1)" for x
  define from_pair :: "real \<times> real \<Rightarrow> slp_point" where
    "from_pair xy = (\<chi> i. if i = 0 then fst xy else snd xy)" for xy

  have from_to: "from_pair (to_pair x) = x" for x
    unfolding vec_eq_iff
  proof (intro allI)
    fix i
    have two_is_zero: "(2::2) = 0"
      by simp
    have i_cases: "i = 1 \<or> i = (2::2)"
      by (rule exhaust_2)
    show "from_pair (to_pair x) $ i = x $ i"
      using i_cases
      by (auto simp: from_pair_def to_pair_def two_is_zero)
  qed
  have to_from: "to_pair (from_pair xy) = xy" for xy
    by (cases xy) (simp add: to_pair_def from_pair_def)
  have to_pair_linear: "linear to_pair"
  proof (rule linearI)
    show "to_pair (x + y) = to_pair x + to_pair y" for x y
      by (simp add: to_pair_def)
    show "to_pair (r *\<^sub>R x) = r *\<^sub>R to_pair x" for r x
      by (simp add: to_pair_def)
  qed
  have from_pair_linear: "linear from_pair"
  proof (rule linearI)
    show "from_pair (x + y) = from_pair x + from_pair y" for x y
      unfolding from_pair_def vec_eq_iff
      by simp
    show "from_pair (r *\<^sub>R x) = r *\<^sub>R from_pair x" for r x
      unfolding from_pair_def vec_eq_iff
      by simp
  qed
  have to_pair_bij: "bij to_pair"
  proof (rule bijI)
    show "inj to_pair"
      by (rule injI) (metis from_to)
    show "surj to_pair"
      by (rule surjI[where f=from_pair]) (rule to_from)
  qed
  have to_pair_measurable:
    "to_pair \<in> measurable (lborel :: slp_point measure) lborel"
  proof -
    have bounded: "bounded_linear to_pair"
      using to_pair_linear by (simp add: linear_conv_bounded_linear)
    have continuous: "continuous_on UNIV to_pair"
      by (rule linear_continuous_on[OF bounded])
    show ?thesis
      using borel_measurable_continuous_onI[OF continuous] by simp
  qed
  have from_pair_measurable:
    "from_pair \<in> measurable (lborel :: (real \<times> real) measure) lborel"
  proof -
    have bounded: "bounded_linear from_pair"
      using from_pair_linear by (simp add: linear_conv_bounded_linear)
    have continuous: "continuous_on UNIV from_pair"
      by (rule linear_continuous_on[OF bounded])
    show ?thesis
      using borel_measurable_continuous_onI[OF continuous] by simp
  qed
  have to_pair_vimage_box:
    "to_pair -` box l u = box (from_pair l) (from_pair u)" for l u
  proof -
    have two_is_zero: "(2::2) = 0"
      by simp
    show ?thesis
      by (rule set_eqI)
        (auto simp: mem_box_cart forall_2 box_prod to_pair_def
          from_pair_def two_is_zero)
  qed
  have from_pair_basis_product:
    "(\<Prod>b\<in>Basis. from_pair z \<bullet> b) =
      (\<Prod>b\<in>Basis. z \<bullet> b)" for z
    by (cases z)
      (simp add: slp_prod_inner_Basis_real_cartesian from_pair_def
        UNIV_2 Basis_prod_def
        prod.union_disjoint prod.reindex_nontrivial inner_prod_def
        inner_axis exhaust_2 mult.commute)
  have to_pair_distr:
    "distr (lborel :: slp_point measure) lborel to_pair = lborel"
  proof (rule lborel_eqI[symmetric])
    fix l u :: "real \<times> real"
    assume ordered:
      "\<And>b. b \<in> Basis \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b"
    have joined_ordered:
      "\<And>b. b \<in> Basis \<Longrightarrow>
        from_pair l \<bullet> b \<le> from_pair u \<bullet> b"
    proof -
      fix b :: slp_point
      assume "b \<in> Basis"
      then obtain i where b_axis: "b = axis i 1"
        by (auto simp: Basis_vec_def)
      show "from_pair l \<bullet> b \<le> from_pair u \<bullet> b"
        using ordered[of "(1,0)"] ordered[of "(0,1)"]
        unfolding b_axis
        by (cases l; cases u; cases i)
          (auto simp: Basis_prod_def from_pair_def inner_axis inner_prod_def)
    qed
    have joined_diff:
      "from_pair u - from_pair l = from_pair (u - l)"
      by (metis linear_diff from_pair_linear)
    have box_sets: "box l u \<in> sets (lborel :: (real \<times> real) measure)"
      by simp
    have joined_box_measure:
      "emeasure lborel (box (from_pair l) (from_pair u)) =
        (\<Prod>b\<in>Basis. (from_pair u - from_pair l) \<bullet> b)"
      by (rule emeasure_lborel_box; rule joined_ordered)
    have joined_box_measure_final:
      "emeasure lborel (box (from_pair l) (from_pair u)) =
        (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
      using joined_box_measure
      by (simp only: joined_diff from_pair_basis_product)
    have distr_box:
      "emeasure (distr lborel lborel to_pair) (box l u) =
        emeasure lborel (box (from_pair l) (from_pair u))"
      apply (subst emeasure_distr[OF to_pair_measurable box_sets])
      apply (simp add: to_pair_vimage_box)
      done
    show "emeasure (distr lborel lborel to_pair) (box l u) =
        (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
      by (rule trans[OF distr_box joined_box_measure_final])
  next
    show "sets (distr (lborel :: slp_point measure) lborel to_pair) =
        sets borel"
      by simp
  qed

  have composed_integrable:
    "integrable lborel (\<lambda>x. ?F (to_pair x))"
  proof -
    have F_measurable:
      "?F \<in> borel_measurable
        (lborel :: (real \<times> real) measure)"
      using pair_measurable by (simp only: lborel_prod)
    show ?thesis
    using integrable_distr_eq[
      OF to_pair_measurable F_measurable]
      product_integrable to_pair_distr
    by simp
  qed
  have composed_eq:
    "(\<lambda>x. ?F (to_pair x)) = slp_coordinate_majorant R s"
  proof (rule ext)
    fix x :: slp_point
    have first_interval:
      "x $ 0 \<in> {-R..R} \<longleftrightarrow> abs (x $ 0) \<le> R"
      by auto
    have second_interval:
      "x $ 1 \<in> {-R..R} \<longleftrightarrow> abs (x $ 1) \<le> R"
      by auto
    have first_indicator:
      "indicator {-R..R} (x $ 0) =
        (if abs (x $ 0) \<le> R then (1::real) else 0)"
      unfolding indicator_def of_bool_def
      using first_interval by simp
    have second_indicator:
      "indicator {-R..R} (x $ 1) =
        (if abs (x $ 1) \<le> R then (1::real) else 0)"
      unfolding indicator_def of_bool_def
      using second_interval by simp
    show "?F (to_pair x) = slp_coordinate_majorant R s x"
      by (cases "abs (x $ 0) \<le> R"; cases "abs (x $ 1) \<le> R")
    (simp_all add: to_pair_def slp_coordinate_majorant_def
      first_indicator second_indicator)
  qed
  show ?thesis
    using composed_integrable by (simp only: composed_eq)
qed

lemma slp_localized_cauchy_kernel_power_le_coordinate_majorant:
  assumes radius_nonnegative: "0 \<le> R"
    and exponent_nonnegative: "0 \<le> s"
    and first_coordinate_nonzero: "x $ 0 \<noteq> 0"
    and second_coordinate_nonzero: "x $ 1 \<noteq> 0"
  shows "abs (slp_localized_cauchy_kernel R x) powr s \<le>
    slp_coordinate_majorant R s x"
proof (cases "norm x \<le> R")
  case False
  then show ?thesis
    by (simp add: slp_localized_cauchy_kernel_def
        slp_coordinate_majorant_def)
next
  case True
  have coordinate_bounds:
    "abs (x $ 0) \<le> R" "abs (x $ 1) \<le> R"
    using component_le_norm_cart[of x 0]
      component_le_norm_cart[of x 1] True by linarith+
  have x_nonzero: "x \<noteq> 0"
    using first_coordinate_nonzero by auto
  have norm_positive: "0 < norm x"
    using x_nonzero by simp
  have product_le_norm_square:
    "abs (x $ 0) * abs (x $ 1) \<le> norm x ^ 2 / 2"
  proof -
    have square_diff_nonnegative:
      "0 \<le> (abs (x $ 0) - abs (x $ 1)) ^ 2"
      by (rule zero_le_power2)
      have twice_product:
        "2 * (abs (x $ 0) * abs (x $ 1)) \<le>
          (x $ 0) ^ 2 + (x $ 1) ^ 2"
    proof -
      have expanded:
        "(abs (x $ 0) - abs (x $ 1)) ^ 2 =
          (x $ 0) ^ 2 + (x $ 1) ^ 2 -
            2 * (abs (x $ 0) * abs (x $ 1))"
        by (simp add: power2_diff algebra_simps)
      show ?thesis
        using square_diff_nonnegative expanded by linarith
    qed
    have norm_square:
      "norm x ^ 2 = (x $ 0) ^ 2 + (x $ 1) ^ 2"
    proof -
      have universe_two: "(UNIV :: 2 set) = {0, 1}"
        using UNIV_2 by auto
      have sum_nonnegative:
        "0 \<le> (\<Sum>i\<in>UNIV. (x $ i) ^ 2)"
        by (rule sum_nonneg) simp
      show ?thesis
        by (simp add: norm_vec_def L2_set_def universe_two
            real_sqrt_pow2[OF sum_nonnegative])
    qed
    show ?thesis
      using twice_product norm_square by linarith
  qed
  have product_le_norm_square_plain:
    "abs (x $ 0) * abs (x $ 1) \<le> norm x ^ 2"
  proof -
    have norm_square_nonnegative: "0 \<le> norm x ^ 2"
      by simp
    show ?thesis
      using product_le_norm_square norm_square_nonnegative by linarith
  qed
  have inverse_norm_power:
    "abs (inverse (norm x)) powr s = norm x powr (-s)"
    using norm_positive
    by (simp add: abs_of_pos inverse_powr powr_minus)
  have negative_exponent: "-s / 2 \<le> 0"
    using exponent_nonnegative by linarith
  have product_majorization:
    "norm x powr (-s) \<le>
      (abs (x $ 0) * abs (x $ 1)) powr (-s / 2)"
  proof -
    have product_positive:
      "0 < abs (x $ 0) * abs (x $ 1)"
      by (rule mult_pos_pos; simp add: first_coordinate_nonzero
            second_coordinate_nonzero)
    have monotone:
      "(norm x ^ 2) powr (-s / 2) \<le>
        (abs (x $ 0) * abs (x $ 1)) powr (-s / 2)"
      by (rule powr_mono2'[OF negative_exponent product_positive
            product_le_norm_square_plain])
    have norm_rewrite:
      "(norm x ^ 2) powr (-s / 2) = norm x powr (-s)"
    proof -
      have square_as_powr:
        "norm x ^ (2::nat) = norm x powr (real 2)"
        by (rule sym, rule powr_realpow[OF norm_positive])
      have nested_power:
        "(norm x powr (real 2)) powr (-s / 2) =
          norm x powr ((real 2) * (-s / 2))"
        by (rule powr_powr)
      have exponent_identity: "(real 2) * (-s / 2) = -s"
        by simp
      show ?thesis
        by (simp only: square_as_powr nested_power exponent_identity)
    qed
    show ?thesis
      using monotone by (simp only: norm_rewrite)
  qed
  have product_split:
    "(abs (x $ 0) * abs (x $ 1)) powr (-s / 2) =
      (abs (x $ 0)) powr (-s / 2) *
        (abs (x $ 1)) powr (-s / 2)"
    by (rule powr_mult)
  have majorant_value:
    "slp_coordinate_majorant R s x =
      (abs (x $ 0)) powr (-s / 2) *
        (abs (x $ 1)) powr (-s / 2)"
    unfolding slp_coordinate_majorant_def
    using coordinate_bounds by simp
  show ?thesis
    unfolding slp_localized_cauchy_kernel_inside[OF True]
      majorant_value
    using coordinate_bounds inverse_norm_power product_majorization
    by (simp only: product_split)
qed

theorem slp_localized_cauchy_kernel_power_integrable:
  assumes exponent_lower: "1 \<le> s"
    and exponent_upper: "s < 2"
  shows "integrable lborel
    (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s)"
proof (cases "R < 0")
  case True
  then show ?thesis
    by simp
next
  case False
  then have radius_nonnegative: "0 \<le> R"
    by simp
  have exponent_nonnegative: "0 \<le> s"
    using exponent_lower by linarith
  have majorant_integrable:
    "integrable lborel (slp_coordinate_majorant R s)"
    by (rule slp_coordinate_majorant_integrable[
          OF radius_nonnegative exponent_upper])
  have target_measurable:
    "(\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s)
      \<in> borel_measurable lborel"
    using slp_localized_cauchy_kernel_borel_measurable by measurable
  have first_axis_negligible:
    "negligible {x::slp_point. x $ 0 = 0}"
    by (rule negligible_standard_hyperplane_cart)
  have second_axis_negligible:
    "negligible {x::slp_point. x $ 1 = 0}"
    by (rule negligible_standard_hyperplane_cart)
  have first_axis_null:
    "{x::slp_point. x $ 0 = 0} \<in> null_sets lborel"
    using first_axis_negligible
    by (auto simp: negligible_iff_null_sets null_sets_completion_iff)
  have second_axis_null:
    "{x::slp_point. x $ 1 = 0} \<in> null_sets lborel"
    using second_axis_negligible
    by (auto simp: negligible_iff_null_sets null_sets_completion_iff)
  have coordinates_nonzero:
    "AE x in (lborel :: slp_point measure).
      (x $ 0 \<noteq> 0 \<and> x $ 1 \<noteq> 0)"
  proof -
    have axes_null:
      "{x::slp_point. x $ 0 = 0} \<union> {x::slp_point. x $ 1 = 0}
        \<in> null_sets lborel"
      by (rule null_sets.Un[OF first_axis_null second_axis_null])
    have outside:
      "AE x in lborel.
        x \<notin> ({x::slp_point. x $ 0 = 0} \<union>
          {x::slp_point. x $ 1 = 0})"
      by (rule AE_not_in[OF axes_null])
    show ?thesis
    proof (rule eventually_mono[OF outside])
      fix x :: slp_point
      assume x_outside:
        "x \<notin> ({x::slp_point. x $ 0 = 0} \<union>
          {x::slp_point. x $ 1 = 0})"
      show "x $ 0 \<noteq> 0 \<and> x $ 1 \<noteq> 0"
        using x_outside by auto
    qed
  qed
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[
      OF majorant_integrable target_measurable])
    show "AE x in lborel.
        norm (abs (slp_localized_cauchy_kernel R x) powr s) \<le>
        norm (slp_coordinate_majorant R s x)"
      using coordinates_nonzero
    proof eventually_elim
      fix x :: slp_point
      assume coordinates: "x $ 0 \<noteq> 0 \<and> x $ 1 \<noteq> 0"
      have first_nonzero: "x $ 0 \<noteq> 0"
        by (rule conjunct1[OF coordinates])
      have second_nonzero: "x $ 1 \<noteq> 0"
        by (rule conjunct2[OF coordinates])
      show "norm (abs (slp_localized_cauchy_kernel R x) powr s) \<le>
          norm (slp_coordinate_majorant R s x)"
      using slp_localized_cauchy_kernel_power_le_coordinate_majorant[
          OF radius_nonnegative exponent_nonnegative first_nonzero
            second_nonzero]
        by (simp add: slp_coordinate_majorant_def)
    qed
  qed
qed

end
