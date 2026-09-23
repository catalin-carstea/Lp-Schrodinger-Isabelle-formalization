theory Inverse_Schrodinger_Lp_Residual_Matrix_QRL
  imports
    Inverse_Schrodinger_Lp_Residual_Phase
    Inverse_Schrodinger_Lp_Cartesian_Product_Bridge
    Inverse_Schrodinger_Lp_Finite_Quadratic_RL
begin

section \<open>Real Hessian representation of the residual phase\<close>

definition slp_complex_coordinate_unpack :: "real^bool \<Rightarrow> complex"
where
  "slp_complex_coordinate_unpack x =
    Complex (x $ False) (x $ True)"

definition slp_signed_active_cartesian_bilinear ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow>
    real^('i \<times> bool) \<Rightarrow> real^('i \<times> bool) \<Rightarrow> real"
where
  "slp_signed_active_cartesian_bilinear epsilon x y =
    slp_signed_active_bilinear epsilon
      (slp_complex_family_unpack x) (slp_complex_family_unpack y)"

definition slp_signed_active_hessian ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow>
    real^('i \<times> bool)^('i \<times> bool)"
where
  "slp_signed_active_hessian epsilon =
    (\<chi> i j. 2 * slp_signed_active_cartesian_bilinear epsilon
      (axis i 1) (axis j 1))"

definition slp_signed_passive_cartesian_bilinear ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow> real^bool \<Rightarrow>
    real^('i \<times> bool) \<Rightarrow> real"
where
  "slp_signed_passive_cartesian_bilinear epsilon c u =
    slp_signed_passive_active_linear epsilon
      (slp_complex_coordinate_unpack c) (slp_complex_family_unpack u)"

definition slp_signed_passive_coefficient ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow>
    real^bool \<Rightarrow> real^('i \<times> bool)"
where
  "slp_signed_passive_coefficient epsilon c =
    (\<chi> j. slp_signed_passive_cartesian_bilinear epsilon c (axis j 1))"

definition slp_signed_passive_constant ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow> real^bool \<Rightarrow> real"
where
  "slp_signed_passive_constant epsilon c =
    slp_signed_passive_scalar epsilon (slp_complex_coordinate_unpack c)"

lemma slp_signed_bilinear_sum_type:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
    and y z :: "(unit + 'i) \<Rightarrow> complex"
  shows "slp_signed_bilinear epsilon y z =
    of_real (epsilon (Inl ())) * y (Inl ()) * z (Inl ()) +
      (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * y (Inr i) * z (Inr i))"
proof -
  let ?f = "\<lambda>k. of_real (epsilon k) * y k * z k"
  have univ_decomposition:
    "(UNIV :: (unit + 'i) set) = range Inl \<union> range Inr"
    by (rule UNIV_sum)
  have range_disjoint:
    "(range (Inl :: unit \<Rightarrow> unit + 'i)) \<inter> range Inr = {}"
    by auto
  have range_split:
    "(\<Sum>k\<in>range Inl \<union> range Inr. ?f k) =
      (\<Sum>k\<in>range Inl. ?f k) + (\<Sum>k\<in>range Inr. ?f k)"
    by (rule sum.union_disjoint) (use range_disjoint in auto)
  have left_range:
    "range (Inl :: unit \<Rightarrow> unit + 'i) = {Inl ()}"
    by auto
  have right_reindex:
    "(\<Sum>k\<in>range Inr. ?f k) = (\<Sum>i\<in>UNIV. ?f (Inr i))"
    using sum.reindex[of Inr UNIV ?f]
    by simp
  show ?thesis
    unfolding slp_signed_bilinear_def
    using range_split
    by (simp add: univ_decomposition left_range right_reindex)
qed

lemma slp_signed_active_bilinear_explicit:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
  shows "slp_signed_active_bilinear epsilon u v =
    Re (of_real (epsilon (Inl ())) *
        slp_signed_tail_output epsilon u *
        slp_signed_tail_output epsilon v +
      (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * u i * v i))"
proof -
  have distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
    using distinguished_sign by auto
  have u_tangent:
    "slp_signed_output epsilon
      (slp_signed_coordinate_join epsilon (0, u)) = 0"
    by (rule slp_signed_coordinate_join_output
        [where epsilon = epsilon and c = 0 and u = u])
      (rule distinguished_nonzero)
  have v_tangent:
    "slp_signed_output epsilon
      (slp_signed_coordinate_join epsilon (0, v)) = 0"
    by (rule slp_signed_coordinate_join_output
        [where epsilon = epsilon and c = 0 and u = v])
      (rule distinguished_nonzero)
  have tangent_form:
    "slp_signed_active_bilinear epsilon u v =
      Re (slp_signed_bilinear epsilon
        (slp_signed_coordinate_join epsilon (0, u))
        (slp_signed_coordinate_join epsilon (0, v)))"
    unfolding slp_signed_active_bilinear_def
    by (rule slp_signed_residual_bilinear_on_tangent[OF u_tangent v_tangent])
  show ?thesis
    using distinguished_sign tangent_form
    by (elim disjE)
      (simp_all add: slp_signed_bilinear_sum_type
        slp_signed_coordinate_join_def power2_eq_square algebra_simps)
qed

lemma slp_signed_active_cartesian_bilinear:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
  shows "bilinear (slp_signed_active_cartesian_bilinear epsilon)"
proof (unfold bilinear_def, intro conjI allI)
  fix x :: "real^('i \<times> bool)"
  show "linear (\<lambda>y. slp_signed_active_cartesian_bilinear epsilon x y)"
  proof (rule linearI)
    show "slp_signed_active_cartesian_bilinear epsilon x (y + z) =
        slp_signed_active_cartesian_bilinear epsilon x y +
          slp_signed_active_cartesian_bilinear epsilon x z"
      for y z :: "real^('i \<times> bool)"
      using distinguished_sign
      by (simp add: slp_signed_active_cartesian_bilinear_def
          slp_signed_active_bilinear_explicit
          slp_complex_family_unpack_def slp_signed_tail_output_def
          sum.distrib sum_subtractf algebra_simps)
    show "slp_signed_active_cartesian_bilinear epsilon x (r *\<^sub>R y) =
        r *\<^sub>R slp_signed_active_cartesian_bilinear epsilon x y"
      for r and y :: "real^('i \<times> bool)"
      using distinguished_sign
      by (simp add: slp_signed_active_cartesian_bilinear_def
          slp_signed_active_bilinear_explicit
          slp_complex_family_unpack_def slp_signed_tail_output_def
          sum.distrib sum_subtractf sum_distrib_left algebra_simps)
  qed
next
  fix y :: "real^('i \<times> bool)"
  show "linear (\<lambda>x. slp_signed_active_cartesian_bilinear epsilon x y)"
  proof (rule linearI)
    show "slp_signed_active_cartesian_bilinear epsilon (x + z) y =
        slp_signed_active_cartesian_bilinear epsilon x y +
          slp_signed_active_cartesian_bilinear epsilon z y"
      for x z :: "real^('i \<times> bool)"
      using distinguished_sign
      by (simp add: slp_signed_active_cartesian_bilinear_def
          slp_signed_active_bilinear_explicit
          slp_complex_family_unpack_def slp_signed_tail_output_def
          sum.distrib sum_subtractf algebra_simps)
    show "slp_signed_active_cartesian_bilinear epsilon (r *\<^sub>R x) y =
        r *\<^sub>R slp_signed_active_cartesian_bilinear epsilon x y"
      for r and x :: "real^('i \<times> bool)"
      using distinguished_sign
      by (simp add: slp_signed_active_cartesian_bilinear_def
          slp_signed_active_bilinear_explicit
          slp_complex_family_unpack_def slp_signed_tail_output_def
          sum.distrib sum_subtractf sum_distrib_left algebra_simps)
  qed
qed

lemma slp_signed_active_cartesian_bilinear_symmetric:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
  shows "slp_signed_active_cartesian_bilinear epsilon x y =
    slp_signed_active_cartesian_bilinear epsilon y x"
proof -
  have uv:
    "slp_signed_active_bilinear epsilon
        (slp_complex_family_unpack x) (slp_complex_family_unpack y) =
      Re (of_real (epsilon (Inl ())) *
          slp_signed_tail_output epsilon (slp_complex_family_unpack x) *
          slp_signed_tail_output epsilon (slp_complex_family_unpack y) +
        (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) *
          slp_complex_family_unpack x i * slp_complex_family_unpack y i))"
    by (rule slp_signed_active_bilinear_explicit
        [where epsilon = epsilon and u = "slp_complex_family_unpack x"
          and v = "slp_complex_family_unpack y"])
      (rule distinguished_sign)
  have vu:
    "slp_signed_active_bilinear epsilon
        (slp_complex_family_unpack y) (slp_complex_family_unpack x) =
      Re (of_real (epsilon (Inl ())) *
          slp_signed_tail_output epsilon (slp_complex_family_unpack y) *
          slp_signed_tail_output epsilon (slp_complex_family_unpack x) +
        (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) *
          slp_complex_family_unpack y i * slp_complex_family_unpack x i))"
    by (rule slp_signed_active_bilinear_explicit
        [where epsilon = epsilon and u = "slp_complex_family_unpack y"
          and v = "slp_complex_family_unpack x"])
      (rule distinguished_sign)
  have sum_comm:
    "(\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) *
        slp_complex_family_unpack x i * slp_complex_family_unpack y i) =
      (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) *
        slp_complex_family_unpack y i * slp_complex_family_unpack x i)"
    by (rule sum.cong) (simp_all add: mult_ac)
  show ?thesis
    unfolding slp_signed_active_cartesian_bilinear_def
    using uv vu sum_comm
    by (simp add: mult_ac)
qed

lemma slp_signed_active_hessian_form:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
  shows "inner x (slp_signed_active_hessian epsilon *v y) / 2 =
    slp_signed_active_cartesian_bilinear epsilon x y"
proof -
  have left_bilinear:
    "bilinear (\<lambda>x y::real^('i \<times> bool).
      inner x (slp_signed_active_hessian epsilon *v y) / 2)"
    by (simp add: bilinear_def linear_iff algebra_simps)
  have right_bilinear:
    "bilinear (slp_signed_active_cartesian_bilinear epsilon)"
    by (rule slp_signed_active_cartesian_bilinear
        [where epsilon = epsilon])
      (rule distinguished_sign)
  have forms_equal:
    "(\<lambda>x y::real^('i \<times> bool).
      inner x (slp_signed_active_hessian epsilon *v y) / 2) =
      slp_signed_active_cartesian_bilinear epsilon"
  proof (rule bilinear_eq_stdbasis[OF left_bilinear right_bilinear])
    fix p q :: "real^('i \<times> bool)"
    assume p_basis: "p \<in> Basis" and q_basis: "q \<in> Basis"
    obtain i where p: "p = axis i 1"
      using p_basis by (auto simp: Basis_vec_def)
    obtain j where q: "q = axis j 1"
      using q_basis by (auto simp: Basis_vec_def)
    show "inner p (slp_signed_active_hessian epsilon *v q) / 2 =
        slp_signed_active_cartesian_bilinear epsilon p q"
      unfolding p q
      apply (subst inner_axis')
      apply (simp add: slp_signed_active_hessian_def
          matrix_vector_mult_def axis_def if_distrib sum.If_cases
          cong del: if_weak_cong)
      done
  qed
  show ?thesis
    using fun_cong[OF fun_cong[OF forms_equal, of x], of y] .
qed

lemma slp_signed_active_hessian_symmetric:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
  shows "hormander_real_symmetric_matrix
    (slp_signed_active_hessian epsilon)"
proof (unfold hormander_real_symmetric_matrix_def, intro allI)
  fix i j
  have symmetry:
    "slp_signed_active_cartesian_bilinear epsilon
        (axis i 1) (axis j 1) =
      slp_signed_active_cartesian_bilinear epsilon
        (axis j 1) (axis i 1)"
    by (rule slp_signed_active_cartesian_bilinear_symmetric
        [where epsilon = epsilon and x = "axis i 1" and y = "axis j 1"])
      (rule distinguished_sign)
  show "slp_signed_active_hessian epsilon $ i $ j =
      slp_signed_active_hessian epsilon $ j $ i"
    using symmetry by (simp add: slp_signed_active_hessian_def)
qed

lemma slp_signed_active_hessian_nondegenerate:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes signs: "\<And>k. epsilon k = -1 \<or> epsilon k = 1"
    and signed_sum: "(\<Sum>k\<in>UNIV. epsilon k) = 1"
  shows "hormander_real_nondegenerate_matrix
    (slp_signed_active_hessian epsilon)"
proof (unfold hormander_real_nondegenerate_matrix_def, intro allI impI)
  fix x :: "real^('i \<times> bool)"
  assume matrix_kernel: "slp_signed_active_hessian epsilon *v x = 0"
  have distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
    by (rule signs)
  have cartesian_kernel:
    "\<forall>y. slp_signed_active_cartesian_bilinear epsilon x y = 0"
  proof
    fix y :: "real^('i \<times> bool)"
    have reverse_zero:
      "slp_signed_active_cartesian_bilinear epsilon y x = 0"
      using slp_signed_active_hessian_form[
          where epsilon = epsilon and x = y and y = x, OF distinguished_sign]
        matrix_kernel
      by simp
    show "slp_signed_active_cartesian_bilinear epsilon x y = 0"
      using reverse_zero
        slp_signed_active_cartesian_bilinear_symmetric[
          where epsilon = epsilon and x = x and y = y,
          OF distinguished_sign]
      by simp
  qed
  have complex_kernel:
    "\<forall>v. slp_signed_active_bilinear epsilon
      (slp_complex_family_unpack x) v = 0"
  proof
    fix v :: "'i \<Rightarrow> complex"
    have packed_zero:
      "slp_signed_active_cartesian_bilinear epsilon x
        (slp_complex_family_pack v) = 0"
      using cartesian_kernel by blast
    show "slp_signed_active_bilinear epsilon
        (slp_complex_family_unpack x) v = 0"
      using packed_zero
      by (simp only: slp_signed_active_cartesian_bilinear_def
          slp_complex_family_unpack_pack)
  qed
  have unpack_zero: "slp_complex_family_unpack x = 0"
    using slp_signed_active_bilinear_nondegenerate[
        where epsilon = epsilon, OF signs signed_sum]
      complex_kernel
    by blast
  have "slp_complex_family_pack (slp_complex_family_unpack x) =
      slp_complex_family_pack 0"
    using unpack_zero by simp
  then have x_pack_zero: "x = slp_complex_family_pack 0"
    by (simp only: slp_complex_family_pack_unpack)
  have pack_zero:
    "(slp_complex_family_pack 0 ::
      real^('i \<times> bool)) = 0"
    unfolding vec_eq_iff
    by (simp add: slp_complex_family_pack_def)
  show "x = 0"
    using x_pack_zero pack_zero by simp
qed

lemma slp_signed_passive_cartesian_bilinear:
  "bilinear (slp_signed_passive_cartesian_bilinear epsilon)"
  unfolding bilinear_def linear_iff
    slp_signed_passive_cartesian_bilinear_def
    slp_signed_passive_active_linear_def
    slp_complex_coordinate_unpack_def slp_complex_family_unpack_def
    slp_signed_tail_output_def
  by (simp add: sum.distrib sum_subtractf sum_distrib_left algebra_simps)

lemma slp_signed_passive_coefficient_inner:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
    and c :: "real^bool"
    and u :: "real^('i \<times> bool)"
  shows "inner (slp_signed_passive_coefficient epsilon c) u =
    slp_signed_passive_cartesian_bilinear epsilon c u"
proof -
  have left_linear:
    "linear (\<lambda>u::real^('i::finite \<times> bool).
      inner (slp_signed_passive_coefficient epsilon c) u)"
  proof (rule linearI)
    show "inner (slp_signed_passive_coefficient epsilon c) (x + y) =
        inner (slp_signed_passive_coefficient epsilon c) x +
          inner (slp_signed_passive_coefficient epsilon c) y"
      for x y :: "real^('i \<times> bool)"
      by (rule inner_add_right)
    show "inner (slp_signed_passive_coefficient epsilon c) (r *\<^sub>R x) =
        r *\<^sub>R inner (slp_signed_passive_coefficient epsilon c) x"
      for r and x :: "real^('i \<times> bool)"
      by simp
  qed
  have right_linear:
    "linear (slp_signed_passive_cartesian_bilinear epsilon c)"
    using slp_signed_passive_cartesian_bilinear[where epsilon = epsilon]
    by (simp add: bilinear_def)
  have functions_equal:
    "(\<lambda>u::real^('i \<times> bool).
      inner (slp_signed_passive_coefficient epsilon c) u) =
      slp_signed_passive_cartesian_bilinear epsilon c"
  proof (rule linear_eq_stdbasis[OF left_linear right_linear])
    fix q :: "real^('i \<times> bool)"
    assume q_basis: "q \<in> Basis"
    obtain j where q: "q = axis j 1"
      using q_basis by (auto simp: Basis_vec_def)
    show "inner (slp_signed_passive_coefficient epsilon c) q =
        slp_signed_passive_cartesian_bilinear epsilon c q"
      by (simp add: q slp_signed_passive_coefficient_def inner_axis)
  qed
  show ?thesis
    using fun_cong[OF functions_equal, of u] .
qed

lemma slp_signed_passive_coefficient_linear:
  "linear (slp_signed_passive_coefficient epsilon)"
proof (rule linearI)
  have form_bilinear:
    "bilinear (slp_signed_passive_cartesian_bilinear epsilon)"
    by (rule slp_signed_passive_cartesian_bilinear)
  show "slp_signed_passive_coefficient epsilon (x + y) =
      slp_signed_passive_coefficient epsilon x +
        slp_signed_passive_coefficient epsilon y"
    for x y :: "real^bool"
    by (simp add: slp_signed_passive_coefficient_def vec_eq_iff
        bilinear_ladd[OF form_bilinear])
  show "slp_signed_passive_coefficient epsilon (r *\<^sub>R x) =
      r *\<^sub>R slp_signed_passive_coefficient epsilon x"
    for r and x :: "real^bool"
    by (simp add: slp_signed_passive_coefficient_def vec_eq_iff
        bilinear_lmul[OF form_bilinear])
qed

lemma slp_signed_passive_coefficient_measurable:
  "slp_signed_passive_coefficient epsilon \<in>
    borel_measurable (lborel :: (real^bool) measure)"
proof -
  have bounded:
    "bounded_linear (slp_signed_passive_coefficient epsilon)"
    using slp_signed_passive_coefficient_linear
    by (simp add: linear_conv_bounded_linear)
  have continuous:
    "continuous_on UNIV (slp_signed_passive_coefficient epsilon)"
    by (rule linear_continuous_on[OF bounded])
  show ?thesis
    using borel_measurable_continuous_onI[OF continuous] by simp
qed

lemma slp_signed_passive_constant_measurable:
  "slp_signed_passive_constant epsilon \<in>
    borel_measurable (lborel :: (real^bool) measure)"
proof -
  have unpack_linear: "linear slp_complex_coordinate_unpack"
  proof (rule linearI)
    show "slp_complex_coordinate_unpack (x + y) =
        slp_complex_coordinate_unpack x + slp_complex_coordinate_unpack y"
      for x y :: "real^bool"
      by (simp add: slp_complex_coordinate_unpack_def complex_eq_iff)
    show "slp_complex_coordinate_unpack (r *\<^sub>R x) =
        r *\<^sub>R slp_complex_coordinate_unpack x"
      for r and x :: "real^bool"
      by (simp add: slp_complex_coordinate_unpack_def complex_eq_iff)
  qed
  have unpack_bounded: "bounded_linear slp_complex_coordinate_unpack"
    using unpack_linear by (simp add: linear_conv_bounded_linear)
  have unpack_continuous:
    "continuous_on UNIV slp_complex_coordinate_unpack"
    by (rule linear_continuous_on[OF unpack_bounded])
  have unpack_measurable:
    "slp_complex_coordinate_unpack \<in>
      borel_measurable (lborel :: (real^bool) measure)"
    using borel_measurable_continuous_onI[OF unpack_continuous] by simp
  show ?thesis
    unfolding slp_signed_passive_constant_def slp_signed_passive_scalar_def
    using unpack_measurable
    by measurable
qed

lemma slp_signed_residual_product_phase:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
  shows "slp_signed_residual epsilon
      (slp_signed_coordinate_join epsilon
        (slp_complex_coordinate_unpack c, slp_complex_family_unpack u)) =
    inner u (slp_signed_active_hessian epsilon *v u) / 2 +
      inner (slp_signed_passive_coefficient epsilon c) u +
      slp_signed_passive_constant epsilon c"
proof -
  have residual_split:
    "slp_signed_residual epsilon
        (slp_signed_coordinate_join epsilon
          (slp_complex_coordinate_unpack c, slp_complex_family_unpack u)) =
      slp_signed_active_quadratic epsilon
          (slp_complex_family_unpack u) +
        slp_signed_passive_active_linear epsilon
          (slp_complex_coordinate_unpack c)
          (slp_complex_family_unpack u) +
        slp_signed_passive_scalar epsilon
          (slp_complex_coordinate_unpack c)"
    by (rule slp_signed_residual_passive_active
        [where epsilon = epsilon and c = "slp_complex_coordinate_unpack c"
          and u = "slp_complex_family_unpack u"])
      (rule distinguished_sign)
  have active_term:
    "inner u (slp_signed_active_hessian epsilon *v u) / 2 =
      slp_signed_active_quadratic epsilon (slp_complex_family_unpack u)"
    using slp_signed_active_hessian_form[
        where epsilon = epsilon and x = u and y = u,
        OF distinguished_sign]
      slp_signed_active_quadratic_diagonal[where epsilon = epsilon
        and u = "slp_complex_family_unpack u"]
    by (simp add: slp_signed_active_cartesian_bilinear_def)
  have linear_term:
    "inner (slp_signed_passive_coefficient epsilon c) u =
      slp_signed_passive_active_linear epsilon
        (slp_complex_coordinate_unpack c) (slp_complex_family_unpack u)"
    using slp_signed_passive_coefficient_inner[where epsilon = epsilon
        and c = c and u = u]
    by (simp add: slp_signed_passive_cartesian_bilinear_def)
  show ?thesis
    using residual_split active_term linear_term
    by (simp add: slp_signed_passive_constant_def)
qed

theorem slp_signed_residual_product_quadratic_decay:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
    and F :: "real^bool \<Rightarrow> real^('i \<times> bool) \<Rightarrow> complex"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim TYPE('i \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE('i \<times> bool)"
    and signs: "\<And>k. epsilon k = -1 \<or> epsilon k = 1"
    and signed_sum: "(\<Sum>k\<in>UNIV. epsilon k) = 1"
    and F_integrable: "integrable lborel (case_prod F)"
  shows
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>(c, u). exp (\<i> * of_real
          (omega * slp_signed_residual epsilon
            (slp_signed_coordinate_join epsilon
              (slp_complex_coordinate_unpack c,
                slp_complex_family_unpack u)))) * F c u))
      \<longlongrightarrow> 0) at_top"
proof -
  interpret active_decay: hormander_quadratic_stationary_phase_decay
      "TYPE('i \<times> bool)"
  proof
    show "hormander_quadratic_stationary_phase_decay_claim
        TYPE('i \<times> bool)"
      by (rule stationary_phase)
  qed
  have distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
    by (rule signs)
  have symmetric:
    "hormander_real_symmetric_matrix (slp_signed_active_hessian epsilon)"
    by (rule slp_signed_active_hessian_symmetric
        [where epsilon = epsilon])
      (rule distinguished_sign)
  have nondegenerate:
    "hormander_real_nondegenerate_matrix
      (slp_signed_active_hessian epsilon)"
    by (rule slp_signed_active_hessian_nondegenerate
        [where epsilon = epsilon, OF signs signed_sum])
  have decay:
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>(c, u). exp (\<i> * of_real
          (omega * (inner u (slp_signed_active_hessian epsilon *v u) / 2 +
            inner (slp_signed_passive_coefficient epsilon c) u +
            slp_signed_passive_constant epsilon c))) * F c u))
      \<longlongrightarrow> 0) at_top"
    by (rule active_decay.slp_finite_quadratic_riemann_lebesgue[
      where A = "slp_signed_active_hessian epsilon"
        and b = "slp_signed_passive_coefficient epsilon",
      OF density symmetric nondegenerate
        slp_signed_passive_coefficient_measurable
        slp_signed_passive_constant_measurable F_integrable])
  have phase_identity:
    "slp_signed_residual epsilon
        (slp_signed_coordinate_join epsilon
          (slp_complex_coordinate_unpack c, slp_complex_family_unpack u)) =
      inner u (slp_signed_active_hessian epsilon *v u) / 2 +
        inner (slp_signed_passive_coefficient epsilon c) u +
        slp_signed_passive_constant epsilon c"
    for c u
    by (rule slp_signed_residual_product_phase[
        where epsilon = epsilon and c = c and u = u])
      (rule distinguished_sign)
  show ?thesis
    using decay
    by (simp only: phase_identity)
qed

end
