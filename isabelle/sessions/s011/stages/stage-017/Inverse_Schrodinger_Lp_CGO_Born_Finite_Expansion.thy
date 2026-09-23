theory Inverse_Schrodinger_Lp_CGO_Born_Finite_Expansion
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Common_CGO_Born_Joint_Series"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exact finite Neumann expansion of the Born bracket\<close>

definition slp_left_neumann_partial_sum ::
    "slp_point set \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
  where
  "slp_left_neumann_partial_sum X N tau c cutoff coefficient =
    (\<lambda>z. \<Sum>j<N.
      slp_restrict_field X
        (slp_neumann_iterate
          (slp_left_neumann_step tau c cutoff coefficient)
          (slp_left_neumann_base tau c cutoff coefficient
            SLP_Dbar_Inverse) j) z)"

definition slp_right_neumann_partial_sum ::
    "slp_point set \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
  where
  "slp_right_neumann_partial_sum X N tau c cutoff coefficient =
    (\<lambda>z. \<Sum>j<N.
      slp_restrict_field X
        (slp_neumann_iterate
          (slp_right_neumann_step tau c cutoff coefficient)
          (slp_right_neumann_base tau c cutoff coefficient
            SLP_Partial_Inverse) j) z)"

definition slp_left_neumann_series_tail ::
    "slp_point set \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
  where
  "slp_left_neumann_series_tail X N tau c cutoff coefficient =
    (\<lambda>z. slp_left_neumann_series_sum X tau c cutoff coefficient z -
      slp_left_neumann_partial_sum X N tau c cutoff coefficient z)"

definition slp_right_neumann_series_tail ::
    "slp_point set \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
  where
  "slp_right_neumann_series_tail X N tau c cutoff coefficient =
    (\<lambda>z. slp_right_neumann_series_sum X tau c cutoff coefficient z -
      slp_right_neumann_partial_sum X N tau c cutoff coefficient z)"

definition slp_cgo_born_neumann_bracket ::
    "slp_point set \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field"
  where
  "slp_cgo_born_neumann_bracket X tau c cutoff coefficient
      coefficient_tilde =
    (\<lambda>z. slp_center_kernel tau c z +
      slp_left_neumann_series_sum X tau c cutoff coefficient z +
      slp_right_neumann_series_sum X tau c cutoff coefficient_tilde z +
      slp_center_kernel (- tau) c z *
        slp_left_neumann_series_sum X tau c cutoff coefficient z *
        slp_right_neumann_series_sum X tau c cutoff coefficient_tilde z)"

definition slp_cgo_born_partial_bracket ::
    "slp_point set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow>
      slp_point \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field"
  where
  "slp_cgo_born_partial_bracket X N M tau c cutoff coefficient
      coefficient_tilde =
    (\<lambda>z. slp_center_kernel tau c z +
      slp_left_neumann_partial_sum X N tau c cutoff coefficient z +
      slp_right_neumann_partial_sum X M tau c cutoff coefficient_tilde z +
      slp_center_kernel (- tau) c z *
        slp_left_neumann_partial_sum X N tau c cutoff coefficient z *
        slp_right_neumann_partial_sum X M tau c cutoff coefficient_tilde z)"

definition slp_cgo_born_neumann_remainder ::
    "slp_point set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow>
      slp_point \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field"
  where
  "slp_cgo_born_neumann_remainder X N M tau c cutoff coefficient
      coefficient_tilde =
    (\<lambda>z.
      slp_left_neumann_series_tail X N tau c cutoff coefficient z +
      slp_right_neumann_series_tail X M tau c cutoff coefficient_tilde z +
      slp_center_kernel (- tau) c z *
        (slp_left_neumann_partial_sum X N tau c cutoff coefficient z *
          slp_right_neumann_series_tail X M tau c cutoff coefficient_tilde z +
         slp_left_neumann_series_tail X N tau c cutoff coefficient z *
          slp_right_neumann_partial_sum X M tau c cutoff coefficient_tilde z +
         slp_left_neumann_series_tail X N tau c cutoff coefficient z *
          slp_right_neumann_series_tail X M tau c cutoff coefficient_tilde z))"

lemma slp_left_neumann_partial_sum_on_carrier:
  assumes z_in: "z \<in> X"
  shows
    "slp_left_neumann_partial_sum X N tau c cutoff coefficient z =
      (\<Sum>j<N. slp_left_neumann_iterate j tau c cutoff coefficient
        SLP_Dbar_Inverse z)"
  unfolding slp_left_neumann_partial_sum_def
  using z_in
  by (simp add: slp_restrict_field_def
      slp_left_neumann_iterate_eq_abstract)

lemma slp_right_neumann_partial_sum_on_carrier:
  assumes z_in: "z \<in> X"
  shows
    "slp_right_neumann_partial_sum X N tau c cutoff coefficient z =
      (\<Sum>j<N. slp_right_neumann_iterate j tau c cutoff coefficient
        SLP_Partial_Inverse z)"
  unfolding slp_right_neumann_partial_sum_def
  using z_in
  by (simp add: slp_restrict_field_def
      slp_right_neumann_iterate_eq_abstract)

lemma slp_finite_sum_product_expansion:
  fixes a :: complex and f g :: "nat \<Rightarrow> complex"
  shows
    "a * (\<Sum>j<N. f j) * (\<Sum>k<M. g k) =
      (\<Sum>j<N. \<Sum>k<M. a * f j * g k)"
  by (simp add: sum_distrib_left sum_distrib_right algebra_simps)

theorem slp_cgo_born_partial_bracket_expansion_on_carrier:
  assumes z_in: "z \<in> X"
  shows
    "slp_cgo_born_partial_bracket X N M tau c cutoff coefficient
        coefficient_tilde z =
      slp_center_kernel tau c z +
      (\<Sum>j<N. slp_left_neumann_iterate j tau c cutoff coefficient
        SLP_Dbar_Inverse z) +
      (\<Sum>k<M. slp_right_neumann_iterate k tau c cutoff coefficient_tilde
        SLP_Partial_Inverse z) +
      (\<Sum>j<N. \<Sum>k<M.
        slp_center_kernel (- tau) c z *
        slp_left_neumann_iterate j tau c cutoff coefficient
          SLP_Dbar_Inverse z *
        slp_right_neumann_iterate k tau c cutoff coefficient_tilde
          SLP_Partial_Inverse z)"
  unfolding slp_cgo_born_partial_bracket_def
  using slp_left_neumann_partial_sum_on_carrier[OF z_in]
    slp_right_neumann_partial_sum_on_carrier[OF z_in]
    slp_finite_sum_product_expansion[where
      a="slp_center_kernel (- tau) c z" and N=N and M=M and
      f="\<lambda>j. slp_left_neumann_iterate j tau c cutoff coefficient
        SLP_Dbar_Inverse z" and
      g="\<lambda>k. slp_right_neumann_iterate k tau c cutoff coefficient_tilde
        SLP_Partial_Inverse z"]
  by simp

theorem slp_cgo_born_neumann_bracket_finite_remainder:
  "slp_cgo_born_neumann_bracket X tau c cutoff coefficient
      coefficient_tilde z =
    slp_cgo_born_partial_bracket X N M tau c cutoff coefficient
      coefficient_tilde z +
    slp_cgo_born_neumann_remainder X N M tau c cutoff coefficient
      coefficient_tilde z"
  unfolding slp_cgo_born_neumann_bracket_def
    slp_cgo_born_partial_bracket_def
    slp_cgo_born_neumann_remainder_def
    slp_left_neumann_series_tail_def slp_right_neumann_series_tail_def
  by (simp add: algebra_simps)

end
