theory Inverse_Schrodinger_Lp_Finite_Product_Nat_Reindex
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Finite_Product_Reindex"
begin

section \<open>Natural-range reindexing of finite uniform products\<close>

theorem slp_distr_PiM_uniform_finite_nat_reindex:
  "distr
      (PiM {..<CARD('i::finite)}
        (\<lambda>_::nat. (lborel :: 'a::euclidean_space measure)))
      (PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure)))
      (\<lambda>omega. \<lambda>i\<in>UNIV. omega (to_nat_on UNIV i)) =
    PiM UNIV (\<lambda>_::'i. (lborel :: 'a measure))"
proof -
  interpret scalar:
    product_sigma_finite
      "\<lambda>_::nat. (lborel :: 'a measure)"
    by standard
  show ?thesis
  proof (rule scalar.slp_distr_PiM_reindex_bij_betw)
    show "finite (UNIV :: 'i set)"
      by simp
    show "finite {..<CARD('i)}"
      by simp
    show "bij_betw (to_nat_on (UNIV :: 'i set))
        (UNIV :: 'i set) {..<CARD('i)}"
      by (rule to_nat_on_finite) simp
  qed
qed

end
