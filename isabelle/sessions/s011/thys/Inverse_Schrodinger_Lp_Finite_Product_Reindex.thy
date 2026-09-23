theory Inverse_Schrodinger_Lp_Finite_Product_Reindex
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Coordinate_Inverse_Measurable"
begin

section \<open>Bijective reindexing of finite sigma-finite products\<close>

lemma (in product_sigma_finite) slp_distr_PiM_reindex_bij_betw:
  fixes I :: "'j set" and K :: "'i set" and t :: "'j \<Rightarrow> 'i"
  assumes finite_I: "finite I"
    and finite_K: "finite K"
    and t_bij: "bij_betw t I K"
  shows
    "distr (PiM K M) (PiM I (\<lambda>j. M (t j)))
        (\<lambda>omega. \<lambda>j\<in>I. omega (t j)) =
      PiM I (\<lambda>j. M (t j))"
proof (rule product_sigma_finite.PiM_eqI)
  show "product_sigma_finite (\<lambda>j. M (t j))"
    by standard
  show "finite I"
    by (rule finite_I)
  have t_inj: "inj_on t I"
    using t_bij by (simp add: bij_betw_def)
  have t_into: "t \<in> I \<rightarrow> K"
    using t_bij unfolding bij_betw_def by auto
  have t_image: "t ` I = K"
    using t_bij by (simp add: bij_betw_def)
  fix A
  assume A: "\<And>j. j \<in> I \<Longrightarrow> A j \<in> sets (M (t j))"
  moreover have
    "((\<lambda>omega. \<lambda>j\<in>I. omega (t j)) -` PiE I A \<inter>
      space (PiM K M)) =
      PiE K (\<lambda>k.
        if k \<in> t ` I then A (the_inv_into I t k) else space (M k))"
    using A A[THEN sets.sets_into_space] t_into t_inj t_image
    by (subst prod_emb_Pi[symmetric])
      (auto simp: space_PiM PiE_iff the_inv_into_f_f prod_emb_def)
  ultimately show
    "distr (PiM K M) (PiM I (\<lambda>j. M (t j)))
        (\<lambda>omega. \<lambda>j\<in>I. omega (t j)) (PiE I A) =
      (\<Prod>j\<in>I. emeasure (M (t j)) (A j))"
    using finite_I finite_K t_inj t_into t_image
    apply (subst emeasure_distr)
     apply (auto intro!: sets_PiM_I_finite measurable_restrict
        simp: Pi_iff)
    apply (subst emeasure_PiM)
      apply (auto simp: the_inv_into_f_f prod.reindex[OF t_inj]
        intro!: sets_PiM_I_finite)
    done
qed simp

end
