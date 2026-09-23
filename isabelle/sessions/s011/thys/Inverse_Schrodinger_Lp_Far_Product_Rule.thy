theory Inverse_Schrodinger_Lp_Far_Product_Rule
  imports Inverse_Schrodinger_Lp_Scaled_Cutoff
begin

section \<open>Pointwise calculus for the far coefficient\<close>

lemma slp_complex_wirtinger_partial_add:
  "slp_complex_wirtinger_partial (\<lambda>h. F h + G h) =
    slp_complex_wirtinger_partial F + slp_complex_wirtinger_partial G"
  unfolding slp_complex_wirtinger_partial_def
  by (simp only: add_divide_distrib distrib_left add_diff_add)

lemma slp_complex_wirtinger_partial_uminus:
  "slp_complex_wirtinger_partial (\<lambda>h. - F h) =
    - slp_complex_wirtinger_partial F"
  unfolding slp_complex_wirtinger_partial_def
  apply (simp only: minus_divide_left[symmetric] mult_minus_right
      diff_minus_eq_add minus_diff_eq)
  unfolding diff_conv_add_uminus
  by (rule add.commute)

lemma slp_complex_wirtinger_partial_diff:
  "slp_complex_wirtinger_partial (\<lambda>h. F h - G h) =
    slp_complex_wirtinger_partial F - slp_complex_wirtinger_partial G"
proof -
  have add:
    "slp_complex_wirtinger_partial (\<lambda>h. F h + (- G h)) =
      slp_complex_wirtinger_partial F +
        slp_complex_wirtinger_partial (\<lambda>h. - G h)"
    by (rule slp_complex_wirtinger_partial_add)
  show ?thesis
    using add
    by (simp only: diff_conv_add_uminus
        slp_complex_wirtinger_partial_uminus)
qed

lemma slp_complex_wirtinger_partial_left_multiplier:
  "slp_complex_wirtinger_partial (\<lambda>h. k * F h) =
    k * slp_complex_wirtinger_partial F"
  unfolding slp_complex_wirtinger_partial_def
  by (simp add: algebra_simps)

lemma slp_complex_wirtinger_partial_point_as_complex [simp]:
  "slp_complex_wirtinger_partial slp_point_as_complex = 1"
  unfolding slp_complex_wirtinger_partial_def slp_point_as_complex_def
  by (rule complex_eqI) (simp_all add: axis_def)

lemma slp_complex_wirtinger_partial_of_real:
  "slp_complex_wirtinger_partial (\<lambda>h. of_real (D h)) =
    slp_real_wirtinger_partial D"
  unfolding slp_complex_wirtinger_partial_def
    slp_real_wirtinger_partial_def
  by (rule refl)

lemma slp_point_as_complex_eq_zero_iff [simp]:
  "slp_point_as_complex x = 0 \<longleftrightarrow> x = 0"
proof
  assume zero: "slp_point_as_complex x = 0"
  have "norm (slp_point_as_complex x) = 0"
    using zero by simp
  then have "norm x = 0" by simp
  then show "x = 0" by simp
next
  assume zero: "x = 0"
  have zero_map: "slp_point_as_complex 0 = 0"
    unfolding slp_point_as_complex_def
    by (rule complex_eqI) simp_all
  show "slp_point_as_complex x = 0"
    unfolding zero using zero_map .
qed

lemma slp_center_difference_has_derivative:
  "((\<lambda>w :: slp_point. slp_point_as_complex (w - c)) has_derivative
      slp_point_as_complex) (at z)"
proof -
  have affine_derivative:
    "((\<lambda>w :: slp_point. w - c) has_derivative id) (at z)"
  proof -
    have function_eq:
      "(\<lambda>w :: slp_point. w - c) = (\<lambda>w. id w + (- c))"
      by (rule ext) (simp only: id_apply diff_conv_add_uminus)
    show ?thesis
      unfolding function_eq
      by (rule has_derivative_add_const[OF has_derivative_id])
  qed
  have complex_derivative:
    "(slp_point_as_complex has_derivative slp_point_as_complex)
      (at (z - c))"
    using bounded_linear.has_derivative[OF
        slp_point_as_complex_bounded_linear has_derivative_id]
    by (simp only: id_apply)
  have composed:
    "((\<lambda>w. slp_point_as_complex (w - c)) has_derivative
      (\<lambda>h. slp_point_as_complex (id h))) (at z)"
    by (rule has_derivative_compose[OF affine_derivative
          complex_derivative])
  show ?thesis
    using composed by (simp only: id_apply)
qed

context slp_cutoff_profile
begin

definition slp_far_product ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field"
where
  "slp_far_product delta c f z =
    of_real (1 - slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c)) * f z"

definition slp_far_product_derivative ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
    (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> complex"
where
  "slp_far_product_derivative delta c f Df z h =
    (of_real (1 - slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c))) * Df h -
    (inverse (slp_point_as_complex (z - c)) * f z) *
      of_real (slp_scaled_cutoff_derivative delta c z h) -
    (of_real (1 - slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c)) ^ 2 * f z) *
      slp_point_as_complex h"

lemma slp_far_product_has_derivative:
  assumes away_from_center: "z \<noteq> c"
    and f_derivative: "(f has_derivative Df) (at z)"
  shows "((slp_far_product delta c f) has_derivative
      slp_far_product_derivative delta c f Df z) (at z)"
proof -
  have difference_nonzero:
    "slp_point_as_complex (z - c) \<noteq> 0"
  proof
    assume "slp_point_as_complex (z - c) = 0"
    then have "z - c = 0"
      by (simp only: slp_point_as_complex_eq_zero_iff)
    with away_from_center show False by simp
  qed
  have inverse_derivative:
    "((\<lambda>w :: slp_point.
        inverse (slp_point_as_complex (w - c))) has_derivative
      (\<lambda>h. - (inverse (slp_point_as_complex (z - c)) *
        slp_point_as_complex h *
        inverse (slp_point_as_complex (z - c))))) (at z)"
    by (rule Deriv.has_derivative_inverse[OF difference_nonzero
          slp_center_difference_has_derivative])
  have cutoff_derivative:
    "((\<lambda>w. of_real (1 - slp_scaled_cutoff delta c w))
      has_derivative
        (\<lambda>h. of_real
          (- slp_scaled_cutoff_derivative delta c z h))) (at z)"
    using slp_scaled_cutoff_has_derivative[of delta c z]
    by (auto intro!: derivative_eq_intros)
  have first_product:
    "((\<lambda>w. of_real (1 - slp_scaled_cutoff delta c w) *
        inverse (slp_point_as_complex (w - c))) has_derivative
      (\<lambda>h.
        of_real (1 - slp_scaled_cutoff delta c z) *
          (- (inverse (slp_point_as_complex (z - c)) *
            slp_point_as_complex h *
            inverse (slp_point_as_complex (z - c)))) +
        of_real (- slp_scaled_cutoff_derivative delta c z h) *
          inverse (slp_point_as_complex (z - c)))) (at z)"
    by (rule has_derivative_mult[OF cutoff_derivative
          inverse_derivative])
  have full_product:
    "((\<lambda>w. of_real (1 - slp_scaled_cutoff delta c w) *
        inverse (slp_point_as_complex (w - c)) * f w) has_derivative
      (\<lambda>h.
        (of_real (1 - slp_scaled_cutoff delta c z) *
          inverse (slp_point_as_complex (z - c))) * Df h +
        (of_real (1 - slp_scaled_cutoff delta c z) *
          (- (inverse (slp_point_as_complex (z - c)) *
            slp_point_as_complex h *
            inverse (slp_point_as_complex (z - c)))) +
        of_real (- slp_scaled_cutoff_derivative delta c z h) *
          inverse (slp_point_as_complex (z - c))) * f z)) (at z)"
    by (rule has_derivative_mult[OF first_product f_derivative])
  have derivative_eq:
    "(\<lambda>h.
        (of_real (1 - slp_scaled_cutoff delta c z) *
          inverse (slp_point_as_complex (z - c))) * Df h +
        (of_real (1 - slp_scaled_cutoff delta c z) *
          (- (inverse (slp_point_as_complex (z - c)) *
            slp_point_as_complex h *
            inverse (slp_point_as_complex (z - c)))) +
        of_real (- slp_scaled_cutoff_derivative delta c z h) *
          inverse (slp_point_as_complex (z - c))) * f z) =
      slp_far_product_derivative delta c f Df z"
    by (rule ext)
      (simp add: slp_far_product_derivative_def algebra_simps;
        simp only: power2_eq_square;
        simp add: ac_simps)
  have normalized:
    "((\<lambda>w. of_real (1 - slp_scaled_cutoff delta c w) *
        inverse (slp_point_as_complex (w - c)) * f w) has_derivative
      slp_far_product_derivative delta c f Df z) (at z)"
    by (rule has_derivative_eq_rhs[OF full_product derivative_eq])
  show ?thesis
    unfolding slp_far_product_def by (rule normalized)
qed

lemma slp_far_product_partial:
  "slp_complex_wirtinger_partial
      (slp_far_product_derivative delta c f Df z) =
    of_real (1 - slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c)) *
        slp_complex_wirtinger_partial Df -
    slp_real_wirtinger_partial
        (slp_scaled_cutoff_derivative delta c z) *
      inverse (slp_point_as_complex (z - c)) * f z -
    of_real (1 - slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c)) ^ 2 * f z"
  unfolding slp_far_product_derivative_def
  unfolding slp_complex_wirtinger_partial_diff
  unfolding slp_complex_wirtinger_partial_left_multiplier
  unfolding slp_complex_wirtinger_partial_real_multiplier
  unfolding slp_complex_wirtinger_partial_of_real
  by (simp add: algebra_simps)

end

end
