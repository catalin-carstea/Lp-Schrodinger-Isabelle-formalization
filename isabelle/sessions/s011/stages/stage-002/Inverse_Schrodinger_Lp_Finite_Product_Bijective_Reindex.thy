theory Inverse_Schrodinger_Lp_Finite_Product_Bijective_Reindex
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Successor_Shifted_Fubini"
begin

section \<open>Bijective reindexing of finite sigma-finite products\<close>

context product_sigma_finite
begin

theorem slp_distr_PiM_reindex_bijective_finite:
  assumes finite_I: "finite I"
    and finite_J: "finite J"
    and bijective: "bij_betw t I J"
  shows
    "distr (PiM J M) (PiM I (\<lambda>i. M (t i)))
        (\<lambda>omega. \<lambda>i\<in>I. omega (t i)) =
      PiM I (\<lambda>i. M (t i))"
proof (rule product_sigma_finite.PiM_eqI)
  show "product_sigma_finite (\<lambda>i. M (t i))"
    by standard
  show "finite I"
    by (rule finite_I)
  fix A
  assume A: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M (t i))"
  have injective: "inj_on t I"
    using bijective by (rule bij_betw_imp_inj_on)
  have into: "t \<in> I \<rightarrow> J"
    using bijective by (rule bij_betw_imp_funcset)
  have image: "t ` I = J"
    using bijective unfolding bij_betw_def by simp
  have reindex_measurable:
      "(\<lambda>omega. \<lambda>i\<in>I. omega (t i)) \<in>
        measurable (PiM J M) (PiM I (\<lambda>i. M (t i)))"
  proof (rule measurable_restrict)
    fix i
    assume iI: "i \<in> I"
    have tiJ: "t i \<in> J"
      using into iI by auto
    show "(\<lambda>omega. omega (t i)) \<in> measurable (PiM J M) (M (t i))"
      by (rule measurable_component_singleton[OF tiJ])
  qed
  have preimage:
      "((\<lambda>omega. \<lambda>i\<in>I. omega (t i)) -` PiE I A \<inter>
          space (PiM J M)) =
        PiE J (\<lambda>j.
          if j \<in> t ` I then A (the_inv_into I t j) else space (M j))"
    using A A[THEN sets.sets_into_space] into injective image
    by (subst prod_emb_Pi[symmetric])
      (auto simp: space_PiM PiE_iff the_inv_into_f_f prod_emb_def)
  show
    "distr (PiM J M) (PiM I (\<lambda>i. M (t i)))
        (\<lambda>omega. \<lambda>i\<in>I. omega (t i)) (PiE I A) =
      (\<Prod>i\<in>I. M (t i) (A i))"
    apply (subst emeasure_distr[OF reindex_measurable])
    apply (rule sets_PiM_I_finite)
    apply (rule finite_I)
    apply (rule A)
    apply assumption
    apply (subst preimage)
    apply (subst emeasure_PiM)
    using finite_I finite_J injective into image A
    by (auto simp: the_inv_into_f_f prod.reindex[OF injective])
qed simp

end

end
