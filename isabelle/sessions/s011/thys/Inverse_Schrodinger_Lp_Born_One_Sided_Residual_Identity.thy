theory Inverse_Schrodinger_Lp_Born_One_Sided_Residual_Identity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Residual_QRL"
begin

section \<open>Indexed presentation of the one-sided residual phase\<close>

lemma slp_sum_UNIV_sum_type_add:
  fixes f :: "('a::finite + 'b::finite) \<Rightarrow> 'c::comm_monoid_add"
  shows "(\<Sum>x\<in>UNIV. f x) =
    (\<Sum>a\<in>UNIV. f (Inl a)) + (\<Sum>b\<in>UNIV. f (Inr b))"
proof -
  have left_reindex:
    "(\<Sum>x\<in>Inl ` (UNIV :: 'a set). f x) =
      (\<Sum>a\<in>UNIV. f (Inl a))"
    using sum.reindex[where h = Inl and A = "UNIV :: 'a set" and g = f]
    by (simp add: o_def)
  have right_reindex:
    "(\<Sum>x\<in>Inr ` (UNIV :: 'b set). f x) =
      (\<Sum>b\<in>UNIV. f (Inr b))"
    using sum.reindex[where h = Inr and A = "UNIV :: 'b set" and g = f]
    by (simp add: o_def)
  have disjoint:
    "Inl ` (UNIV :: 'a set) \<inter> Inr ` (UNIV :: 'b set) = {}"
    by auto
  have union_sum:
    "(\<Sum>x\<in>Inl ` (UNIV :: 'a set) \<union> Inr ` (UNIV :: 'b set). f x) =
      (\<Sum>x\<in>Inl ` (UNIV :: 'a set). f x) +
        (\<Sum>x\<in>Inr ` (UNIV :: 'b set). f x)"
    by (rule sum.union_disjoint) (simp_all add: disjoint)
  show ?thesis
    using union_sum left_reindex right_reindex
    by (simp only: UNIV_sum)
qed

definition slp_one_sided_branch_family ::
    "('i::finite \<Rightarrow> complex) \<Rightarrow> ('i \<Rightarrow> complex) \<Rightarrow>
      complex \<Rightarrow> (unit + ('i + 'i) \<Rightarrow> complex)"
where
  "slp_one_sided_branch_family lambda eta s k =
    (case k of
      Inl _ \<Rightarrow> s
    | Inr side \<Rightarrow> case side of
        Inl i \<Rightarrow> lambda i
      | Inr i \<Rightarrow> eta i)"

lemma slp_one_sided_branch_output_identity:
  fixes lambda eta :: "'i::finite \<Rightarrow> complex"
    and s :: complex
  shows "slp_signed_output slp_one_sided_branch_sign
      (slp_one_sided_branch_family lambda eta s) =
    s + (\<Sum>i\<in>UNIV. lambda i - eta i)"
proof -
  note outer = slp_sum_UNIV_sum_type_add[
      where 'a = unit and 'b = "'i + 'i" and 'c = complex
        and f = "\<lambda>k :: unit + ('i + 'i).
        of_real (slp_one_sided_branch_sign k) *
          slp_one_sided_branch_family lambda eta s k"]
  note inner = slp_sum_UNIV_sum_type_add[
      where 'a = 'i and 'b = 'i and 'c = complex
        and f = "\<lambda>side :: 'i + 'i.
        of_real (slp_one_sided_branch_sign (Inr side)) *
          slp_one_sided_branch_family lambda eta s (Inr side)"]
  have weighted_sum:
    "(\<Sum>k\<in>UNIV.
        of_real (slp_one_sided_branch_sign k) *
          slp_one_sided_branch_family lambda eta s k) =
      s + (\<Sum>i\<in>UNIV. lambda i - eta i)"
    using outer inner
    by (simp add: slp_one_sided_branch_sign_def
        slp_one_sided_branch_family_def sum_negf sum_subtractf)
  show ?thesis
    unfolding slp_signed_output_def
    by (rule weighted_sum)
qed

lemma slp_one_sided_branch_residual_identity:
  fixes lambda eta :: "'i::finite \<Rightarrow> complex"
    and s :: complex
  shows "slp_signed_residual slp_one_sided_branch_sign
      (slp_one_sided_branch_family lambda eta s) =
    Re ((\<Sum>i\<in>UNIV. (lambda i) ^ 2) -
      (\<Sum>i\<in>UNIV. (eta i) ^ 2) + s ^ 2 -
      (s + (\<Sum>i\<in>UNIV. lambda i - eta i)) ^ 2)"
proof -
  note outer = slp_sum_UNIV_sum_type_add[
      where 'a = unit and 'b = "'i + 'i" and 'c = complex
        and f = "\<lambda>k :: unit + ('i + 'i).
        of_real (slp_one_sided_branch_sign k) *
          (slp_one_sided_branch_family lambda eta s k) ^ 2"]
  note inner = slp_sum_UNIV_sum_type_add[
      where 'a = 'i and 'b = 'i and 'c = complex
        and f = "\<lambda>side :: 'i + 'i.
        of_real (slp_one_sided_branch_sign (Inr side)) *
          (slp_one_sided_branch_family lambda eta s (Inr side)) ^ 2"]
  have square_sum:
    "(\<Sum>k\<in>UNIV.
        of_real (slp_one_sided_branch_sign k) *
          (slp_one_sided_branch_family lambda eta s k) ^ 2) =
      (\<Sum>i\<in>UNIV. (lambda i) ^ 2) -
        (\<Sum>i\<in>UNIV. (eta i) ^ 2) + s ^ 2"
    using outer inner
    by (simp add: slp_one_sided_branch_sign_def
        slp_one_sided_branch_family_def sum_negf algebra_simps)
  have output_identity:
    "slp_signed_output slp_one_sided_branch_sign
        (slp_one_sided_branch_family lambda eta s) =
      s + (\<Sum>i\<in>UNIV. lambda i - eta i)"
    by (rule slp_one_sided_branch_output_identity)
  show ?thesis
    unfolding slp_signed_residual_def
    using square_sum output_identity by simp
qed

end
