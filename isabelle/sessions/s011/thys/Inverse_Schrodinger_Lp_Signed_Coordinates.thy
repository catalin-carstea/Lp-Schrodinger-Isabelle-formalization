theory Inverse_Schrodinger_Lp_Signed_Coordinates
  imports Inverse_Schrodinger_Lp_Quadratic_Phase
begin

section \<open>Signed-output and active-tail coordinates\<close>

text \<open>
  The index type @{typ "unit + 'i"} chooses one distinguished coordinate and
  leaves a nonempty finite active tail.  This realizes the fixed algebraic
  coordinate split used before the quadratic Riemann--Lebesgue reduction.  A
  later packet will pack these complex coordinates into real Cartesian form
  and calculate the corresponding real Jacobian.
\<close>

definition slp_signed_tail_output ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_signed_tail_output epsilon u =
    (\<Sum>i\<in>UNIV. of_real (epsilon (Inr i)) * u i)"

definition slp_signed_coordinate_split ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow>
    ((unit + 'i) \<Rightarrow> complex) \<Rightarrow> complex \<times> ('i \<Rightarrow> complex)"
where
  "slp_signed_coordinate_split epsilon y =
    (slp_signed_output epsilon y, \<lambda>i. y (Inr i))"

definition slp_signed_coordinate_join ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow>
    (complex \<times> ('i \<Rightarrow> complex)) \<Rightarrow> (unit + 'i) \<Rightarrow> complex"
where
  "slp_signed_coordinate_join epsilon cu =
    (case cu of (c, u) \<Rightarrow>
      case_sum
        (\<lambda>_. (c - slp_signed_tail_output epsilon u) /
          of_real (epsilon (Inl ())))
        u)"

lemma slp_signed_output_sum_type:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
    and y :: "(unit + 'i) \<Rightarrow> complex"
  shows "slp_signed_output epsilon y =
    of_real (epsilon (Inl ())) * y (Inl ()) +
      slp_signed_tail_output epsilon (\<lambda>i. y (Inr i))"
proof -
  let ?f = "\<lambda>i. of_real (epsilon i) * y i"
  have univ_decomposition:
    "(UNIV :: (unit + 'i) set) = range Inl \<union> range Inr"
    by (rule UNIV_sum)
  have range_disjoint:
    "(range (Inl :: unit \<Rightarrow> unit + 'i)) \<inter> range Inr = {}"
    by auto
  have range_split:
    "(\<Sum>i\<in>range Inl \<union> range Inr. ?f i) =
      (\<Sum>i\<in>range Inl. ?f i) + (\<Sum>i\<in>range Inr. ?f i)"
    by (rule sum.union_disjoint) (use range_disjoint in auto)
  have left_range:
    "range (Inl :: unit \<Rightarrow> unit + 'i) = {Inl ()}"
    by auto
  have right_reindex:
    "(\<Sum>i\<in>range Inr. ?f i) = (\<Sum>i\<in>UNIV. ?f (Inr i))"
    using sum.reindex[of Inr UNIV ?f]
    by simp
  show ?thesis
    unfolding slp_signed_output_def slp_signed_tail_output_def
    using range_split
    by (simp add: univ_decomposition left_range right_reindex)
qed

lemma slp_signed_coordinate_join_output:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
  shows "slp_signed_output epsilon
      (slp_signed_coordinate_join epsilon (c, u)) = c"
  using distinguished_nonzero
  by (simp add: slp_signed_coordinate_join_def slp_signed_output_sum_type
      slp_signed_tail_output_def)

lemma slp_signed_coordinate_join_split:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
  shows "slp_signed_coordinate_join epsilon
      (slp_signed_coordinate_split epsilon y) = y"
proof (rule ext)
  fix k
  show "slp_signed_coordinate_join epsilon
      (slp_signed_coordinate_split epsilon y) k = y k"
    using distinguished_nonzero
    by (cases k)
      (simp_all add: slp_signed_coordinate_join_def
        slp_signed_coordinate_split_def slp_signed_output_sum_type
        slp_signed_tail_output_def)
qed

lemma slp_signed_coordinate_split_join:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
  shows "slp_signed_coordinate_split epsilon
      (slp_signed_coordinate_join epsilon cu) = cu"
proof (cases cu)
  case (Pair c u)
  have output_eq:
    "slp_signed_output epsilon
        (slp_signed_coordinate_join epsilon (c, u)) = c"
    by (rule slp_signed_coordinate_join_output
        [where epsilon = epsilon and c = c and u = u])
      (rule distinguished_nonzero)
  show ?thesis
    using Pair output_eq
    by (simp add: slp_signed_coordinate_split_def
        slp_signed_coordinate_join_def)
qed

theorem slp_signed_coordinate_split_bij:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
  shows "bij (slp_signed_coordinate_split epsilon)"
proof (rule bijI)
  show "inj (slp_signed_coordinate_split epsilon)"
  proof (rule injI)
    fix y z
    assume equal_split:
      "slp_signed_coordinate_split epsilon y =
        slp_signed_coordinate_split epsilon z"
    have joined_equal:
      "slp_signed_coordinate_join epsilon
        (slp_signed_coordinate_split epsilon y) =
      slp_signed_coordinate_join epsilon
        (slp_signed_coordinate_split epsilon z)"
      using equal_split by (rule arg_cong)
    have join_y:
      "slp_signed_coordinate_join epsilon
          (slp_signed_coordinate_split epsilon y) = y"
      by (rule slp_signed_coordinate_join_split
          [where epsilon = epsilon and y = y])
        (rule distinguished_nonzero)
    have join_z:
      "slp_signed_coordinate_join epsilon
          (slp_signed_coordinate_split epsilon z) = z"
      by (rule slp_signed_coordinate_join_split
          [where epsilon = epsilon and y = z])
        (rule distinguished_nonzero)
    show "y = z"
      using joined_equal join_y join_z by simp
  qed
  show "surj (slp_signed_coordinate_split epsilon)"
  proof (rule surjI
      [where f = "slp_signed_coordinate_join epsilon"])
    fix cu
    show "slp_signed_coordinate_split epsilon
        (slp_signed_coordinate_join epsilon cu) = cu"
      by (rule slp_signed_coordinate_split_join
          [where epsilon = epsilon and cu = cu])
        (rule distinguished_nonzero)
  qed
qed

corollary slp_signed_coordinate_split_bij_of_signs:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes signs: "\<And>k. epsilon k = -1 \<or> epsilon k = 1"
  shows "bij (slp_signed_coordinate_split epsilon)"
  by (rule slp_signed_coordinate_split_bij) (use signs[of "Inl ()"] in auto)

end
