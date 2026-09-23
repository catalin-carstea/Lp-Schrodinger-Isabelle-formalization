theory Inverse_Schrodinger_Lp_Center_Phase_Derivative
  imports
    Inverse_Schrodinger_Lp_Oscillatory_Cauchy
    Inverse_Schrodinger_Lp_Localized_Cauchy_Riesz
begin

section \<open>Differential identities for the physical center phase\<close>

definition slp_center_phase_derivative ::
  "slp_point \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_center_phase_derivative c z h =
    2 * (z $ (0 :: 2) - c $ (0 :: 2)) * h $ (0 :: 2) -
    2 * (z $ (1 :: 2) - c $ (1 :: 2)) * h $ (1 :: 2)"

definition slp_real_wirtinger_partial ::
  "(slp_point \<Rightarrow> real) \<Rightarrow> complex"
where
  "slp_real_wirtinger_partial D =
    of_real (D (axis (0 :: 2) 1)) / 2 -
      \<i> * of_real (D (axis (1 :: 2) 1)) / 2"

definition slp_complex_wirtinger_partial ::
  "(slp_point \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_complex_wirtinger_partial D =
    D (axis (0 :: 2) 1) / 2 -
      \<i> * D (axis (1 :: 2) 1) / 2"

definition slp_center_phase_partial ::
  "slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_center_phase_partial c z =
    slp_real_wirtinger_partial (slp_center_phase_derivative c z)"

definition slp_center_phase_partial_derivative ::
  "slp_point \<Rightarrow> complex"
where
  "slp_center_phase_partial_derivative h = slp_point_as_complex h"

definition slp_center_phase_second_partial :: complex
where
  "slp_center_phase_second_partial =
    slp_complex_wirtinger_partial slp_center_phase_partial_derivative"

lemma slp_center_phase_has_derivative:
  "((slp_center_phase c) has_derivative
      slp_center_phase_derivative c z) (at z)"
proof -
  have coordinate_zero:
    "((\<lambda>w :: slp_point. w $ (0 :: 2)) has_derivative
      (\<lambda>h. h $ (0 :: 2))) (at z)"
    using bounded_linear.has_derivative[OF bounded_linear_vec_nth
        has_derivative_id]
    by (simp only: id_apply)
  have coordinate_one:
    "((\<lambda>w :: slp_point. w $ (1 :: 2)) has_derivative
      (\<lambda>h. h $ (1 :: 2))) (at z)"
    using bounded_linear.has_derivative[OF bounded_linear_vec_nth
        has_derivative_id]
    by (simp only: id_apply)
  have square_zero:
    "((\<lambda>w :: slp_point. (w $ (0 :: 2) - c $ (0 :: 2)) ^ 2)
      has_derivative
        (\<lambda>h. 2 * (z $ (0 :: 2) - c $ (0 :: 2)) *
          h $ (0 :: 2))) (at z)"
    using coordinate_zero
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have square_one:
    "((\<lambda>w :: slp_point. (w $ (1 :: 2) - c $ (1 :: 2)) ^ 2)
      has_derivative
        (\<lambda>h. 2 * (z $ (1 :: 2) - c $ (1 :: 2)) *
          h $ (1 :: 2))) (at z)"
    using coordinate_one
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  show ?thesis
    unfolding slp_center_phase_def slp_center_phase_derivative_def
    by (rule has_derivative_diff[OF square_zero square_one])
qed

lemma slp_center_phase_derivative_first_axis [simp]:
  "slp_center_phase_derivative c z (axis (0 :: 2) 1) =
    2 * (z $ (0 :: 2) - c $ (0 :: 2))"
  by (simp add: slp_center_phase_derivative_def axis_def)

lemma slp_center_phase_derivative_second_axis [simp]:
  "slp_center_phase_derivative c z (axis (1 :: 2) 1) =
    - 2 * (z $ (1 :: 2) - c $ (1 :: 2))"
  by (simp add: slp_center_phase_derivative_def axis_def)

lemma slp_axis_zero_at_one [simp]:
  "(axis (0 :: 2) (1 :: real)) $ (1 :: 2) = 0"
  by (simp add: axis_def)

lemma slp_axis_one_at_zero [simp]:
  "(axis (1 :: 2) (1 :: real)) $ (0 :: 2) = 0"
  by (simp add: axis_def)

lemma slp_center_phase_partial_eq_difference:
  "slp_center_phase_partial c z = slp_point_as_complex (z - c)"
proof -
  have first_axis:
    "slp_center_phase_derivative c z (axis (0 :: 2) 1) =
      2 * (z $ (0 :: 2) - c $ (0 :: 2))"
    by (rule slp_center_phase_derivative_first_axis)
  have second_axis:
    "slp_center_phase_derivative c z (axis (1 :: 2) 1) =
      - 2 * (z $ (1 :: 2) - c $ (1 :: 2))"
    by (rule slp_center_phase_derivative_second_axis)
  have scalar_identity:
    "- ((2 * x - 2 * y) / 2) = y - x" for x y :: real
  proof -
    have expand: "2 * (x - y) = 2 * x - 2 * y"
      by (simp only: right_diff_distrib)
    have cancel: "(2 * (x - y)) / 2 = x - y"
      by (rule nonzero_mult_div_cancel_left) simp
    show ?thesis
      by (simp only: expand[symmetric] cancel minus_diff_eq)
  qed
  show ?thesis
    unfolding slp_center_phase_partial_def slp_real_wirtinger_partial_def
    unfolding first_axis second_axis slp_point_as_complex_def
    apply (rule complex_eqI)
    subgoal by simp
    subgoal by (simp add: scalar_identity)
    done
qed

lemma slp_point_as_complex_bounded_linear:
  "bounded_linear slp_point_as_complex"
proof (rule bounded_linear_intro[where K=1])
  show "slp_point_as_complex (x + y) =
      slp_point_as_complex x + slp_point_as_complex y" for x y
    by (rule complex_eqI)
      (simp_all add: slp_point_as_complex_def)
  show "slp_point_as_complex (r *\<^sub>R x) =
      r *\<^sub>R slp_point_as_complex x" for r x
    by (rule complex_eqI)
      (simp_all add: slp_point_as_complex_def)
  show "norm (slp_point_as_complex x) \<le> norm x * 1" for x
    by simp
qed

lemma slp_center_phase_partial_has_derivative:
  "((slp_center_phase_partial c) has_derivative
      slp_center_phase_partial_derivative) (at z)"
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
  have function_eq:
    "slp_center_phase_partial c =
      (\<lambda>w. slp_point_as_complex (w - c))"
    by (rule ext) (rule slp_center_phase_partial_eq_difference)
  show ?thesis
    unfolding function_eq slp_center_phase_partial_derivative_def
    using composed by (simp only: id_apply)
qed

lemma slp_center_phase_partial_derivative_first_axis [simp]:
  "slp_center_phase_partial_derivative (axis (0 :: 2) 1) = 1"
  unfolding slp_center_phase_partial_derivative_def
    slp_point_as_complex_def
  by (rule complex_eqI) (simp_all add: axis_def)

lemma slp_center_phase_partial_derivative_second_axis [simp]:
  "slp_center_phase_partial_derivative (axis (1 :: 2) 1) = \<i>"
  unfolding slp_center_phase_partial_derivative_def
    slp_point_as_complex_def
  by (rule complex_eqI) (simp_all add: axis_def)

lemma slp_center_phase_second_partial_eq_one [simp]:
  "slp_center_phase_second_partial = 1"
  unfolding slp_center_phase_second_partial_def
    slp_complex_wirtinger_partial_def
  by simp

end
