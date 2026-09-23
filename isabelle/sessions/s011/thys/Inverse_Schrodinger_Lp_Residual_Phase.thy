theory Inverse_Schrodinger_Lp_Residual_Phase
  imports Inverse_Schrodinger_Lp_Signed_Coordinates
begin

section \<open>Residual phase in passive and active coordinates\<close>

text \<open>
  The distinguished signed-output coordinate is passive.  The remaining
  complex coordinates carry a fixed real quadratic form.  This theory keeps
  that form abstract: its later real-matrix representation and the quadratic
  Riemann--Lebesgue application belong to a separate packet.
\<close>

definition slp_signed_active_quadratic ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> complex) \<Rightarrow> real"
where
  "slp_signed_active_quadratic epsilon u =
    slp_signed_residual epsilon
      (slp_signed_coordinate_join epsilon (0, u))"

definition slp_signed_active_bilinear ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> complex) \<Rightarrow>
    ('i \<Rightarrow> complex) \<Rightarrow> real"
where
  "slp_signed_active_bilinear epsilon u v =
    slp_signed_residual_bilinear epsilon
      (slp_signed_coordinate_join epsilon (0, u))
      (slp_signed_coordinate_join epsilon (0, v))"

definition slp_signed_passive_active_linear ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow> complex \<Rightarrow>
    ('i \<Rightarrow> complex) \<Rightarrow> real"
where
  "slp_signed_passive_active_linear epsilon c u =
    Re (-2 * of_real (epsilon (Inl ())) * c *
      slp_signed_tail_output epsilon u)"

definition slp_signed_passive_scalar ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow> complex \<Rightarrow> real"
where
  "slp_signed_passive_scalar epsilon c =
    Re ((of_real (epsilon (Inl ())) - 1) * c ^ 2)"

lemma slp_signed_square_sum_type:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
    and y :: "(unit + 'i) \<Rightarrow> complex"
  shows "(\<Sum>k\<in>UNIV. of_real (epsilon k) * (y k) ^ 2) =
    of_real (epsilon (Inl ())) * (y (Inl ())) ^ 2 +
      (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * (y (Inr i)) ^ 2)"
proof -
  let ?f = "\<lambda>k. of_real (epsilon k) * (y k) ^ 2"
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
    using range_split
    by (simp add: univ_decomposition left_range right_reindex)
qed

lemma slp_signed_active_quadratic_explicit:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
  shows "slp_signed_active_quadratic epsilon u =
    Re (of_real (epsilon (Inl ())) *
        (slp_signed_tail_output epsilon u) ^ 2 +
      (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * (u i) ^ 2))"
proof -
  have distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
    using distinguished_sign by auto
  have output_zero:
    "slp_signed_output epsilon
      (slp_signed_coordinate_join epsilon (0, u)) = 0"
    by (rule slp_signed_coordinate_join_output
        [where epsilon = epsilon and c = 0 and u = u])
      (rule distinguished_nonzero)
  have square_split:
    "(\<Sum>k\<in>UNIV. of_real (epsilon k) *
        (slp_signed_coordinate_join epsilon (0, u) k) ^ 2) =
      of_real (epsilon (Inl ())) *
        (slp_signed_coordinate_join epsilon (0, u) (Inl ())) ^ 2 +
      (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) *
        (slp_signed_coordinate_join epsilon (0, u) (Inr i)) ^ 2)"
    by (rule slp_signed_square_sum_type)
  have square_join:
    "(\<Sum>k\<in>UNIV. of_real (epsilon k) *
        (slp_signed_coordinate_join epsilon (0, u) k) ^ 2) =
      of_real (epsilon (Inl ())) *
        (slp_signed_tail_output epsilon u) ^ 2 +
      (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * (u i) ^ 2)"
    using distinguished_sign square_split
    by (elim disjE)
      (simp_all add: slp_signed_coordinate_join_def
        power2_eq_square algebra_simps)
  show ?thesis
    using output_zero square_join
    unfolding slp_signed_active_quadratic_def slp_signed_residual_def
    by simp
qed

lemma slp_signed_residual_passive_active:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
  shows "slp_signed_residual epsilon
      (slp_signed_coordinate_join epsilon (c, u)) =
    slp_signed_active_quadratic epsilon u +
      slp_signed_passive_active_linear epsilon c u +
      slp_signed_passive_scalar epsilon c"
proof -
  have distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
    using distinguished_sign by auto
  have output_c:
    "slp_signed_output epsilon
      (slp_signed_coordinate_join epsilon (c, u)) = c"
    by (rule slp_signed_coordinate_join_output
        [where epsilon = epsilon and c = c and u = u])
      (rule distinguished_nonzero)
  have active_explicit:
    "slp_signed_active_quadratic epsilon u =
      Re (of_real (epsilon (Inl ())) *
          (slp_signed_tail_output epsilon u) ^ 2 +
        (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * (u i) ^ 2))"
    by (rule slp_signed_active_quadratic_explicit
        [where epsilon = epsilon and u = u])
      (rule distinguished_sign)
  have square_split:
    "(\<Sum>k\<in>UNIV. of_real (epsilon k) *
        (slp_signed_coordinate_join epsilon (c, u) k) ^ 2) =
      of_real (epsilon (Inl ())) *
        (slp_signed_coordinate_join epsilon (c, u) (Inl ())) ^ 2 +
      (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) *
        (slp_signed_coordinate_join epsilon (c, u) (Inr i)) ^ 2)"
    by (rule slp_signed_square_sum_type)
  have square_join:
    "(\<Sum>k\<in>UNIV. of_real (epsilon k) *
        (slp_signed_coordinate_join epsilon (c, u) k) ^ 2) =
      of_real (epsilon (Inl ())) *
        (c - slp_signed_tail_output epsilon u) ^ 2 +
      (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * (u i) ^ 2)"
    using distinguished_sign square_split
    by (elim disjE)
      (simp_all add: slp_signed_coordinate_join_def
        power2_eq_square algebra_simps)
  have residual_explicit:
    "slp_signed_residual epsilon
        (slp_signed_coordinate_join epsilon (c, u)) =
      Re (of_real (epsilon (Inl ())) *
          (c - slp_signed_tail_output epsilon u) ^ 2 +
        (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * (u i) ^ 2) - c ^ 2)"
    using output_c square_join
    unfolding slp_signed_residual_def
    by simp
  have complex_decomposition:
    "of_real (epsilon (Inl ())) *
        (c - slp_signed_tail_output epsilon u) ^ 2 +
      (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * (u i) ^ 2) - c ^ 2 =
      (of_real (epsilon (Inl ())) *
          (slp_signed_tail_output epsilon u) ^ 2 +
        (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * (u i) ^ 2)) +
      (-2 * of_real (epsilon (Inl ())) * c *
        slp_signed_tail_output epsilon u) +
      ((of_real (epsilon (Inl ())) - 1) * c ^ 2)"
    using distinguished_sign
    by (elim disjE)
      (simp_all add: power2_eq_square algebra_simps)
  show ?thesis
    using residual_explicit active_explicit complex_decomposition
    unfolding
      slp_signed_passive_active_linear_def slp_signed_passive_scalar_def
    by simp
qed

lemma slp_signed_active_quadratic_diagonal:
  "slp_signed_active_quadratic epsilon u =
    slp_signed_active_bilinear epsilon u u"
  unfolding slp_signed_active_quadratic_def
    slp_signed_active_bilinear_def
  by (rule slp_signed_residual_diagonal)

theorem slp_signed_active_bilinear_nondegenerate:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes signs: "\<And>k. epsilon k = -1 \<or> epsilon k = 1"
    and signed_sum: "(\<Sum>k\<in>UNIV. epsilon k) = 1"
  shows "\<forall>u. (\<forall>v. slp_signed_active_bilinear epsilon u v = 0) \<longrightarrow>
    u = 0"
proof (intro allI impI)
  fix u :: "'i \<Rightarrow> complex"
  assume active_kernel:
    "\<forall>v. slp_signed_active_bilinear epsilon u v = 0"
  have distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
    using signs[of "Inl ()"] by auto
  let ?U = "slp_signed_coordinate_join epsilon (0, u)"
  have U_tangent: "slp_signed_output epsilon ?U = 0"
    by (rule slp_signed_coordinate_join_output
        [where epsilon = epsilon and c = 0 and u = u])
      (rule distinguished_nonzero)
  have residual_kernel:
    "\<forall>w. slp_signed_output epsilon w = 0 \<longrightarrow>
      slp_signed_residual_bilinear epsilon ?U w = 0"
  proof (intro allI impI)
    fix w :: "(unit + 'i) \<Rightarrow> complex"
    assume w_tangent: "slp_signed_output epsilon w = 0"
    let ?v = "\<lambda>i. w (Inr i)"
    have w_join: "w = slp_signed_coordinate_join epsilon (0, ?v)"
    proof -
      have split_w:
        "slp_signed_coordinate_split epsilon w = (0, ?v)"
        using w_tangent
        by (simp add: slp_signed_coordinate_split_def)
      have "slp_signed_coordinate_join epsilon
          (slp_signed_coordinate_split epsilon w) = w"
        by (rule slp_signed_coordinate_join_split
            [where epsilon = epsilon and y = w])
          (rule distinguished_nonzero)
      then show ?thesis
        using split_w by simp
    qed
    have "slp_signed_active_bilinear epsilon u ?v = 0"
      using active_kernel by blast
    then show "slp_signed_residual_bilinear epsilon ?U w = 0"
      using w_join
      by (simp add: slp_signed_active_bilinear_def)
  qed
  have U_zero: "?U = 0"
    using slp_signed_fiber_nondegenerate[OF signs signed_sum]
      U_tangent residual_kernel
    unfolding slp_signed_fiber_nondegenerate_def
    by blast
  show "u = 0"
  proof
    fix i
    have coordinate_zero: "?U (Inr i) = 0"
      using fun_cong[OF U_zero, of "Inr i"] by simp
    show "u i = 0 i"
      using coordinate_zero
      by (simp add: slp_signed_coordinate_join_def)
  qed
qed

end
