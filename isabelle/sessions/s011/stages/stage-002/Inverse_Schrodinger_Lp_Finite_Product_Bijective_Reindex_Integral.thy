theory Inverse_Schrodinger_Lp_Finite_Product_Bijective_Reindex_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Bijective_Reindex"
begin

section \<open>Complex Bochner transport across finite product reindexing\<close>

context product_sigma_finite
begin

lemma slp_measurable_PiM_reindex_bij_betw:
  assumes bijective: "bij_betw t I K"
  shows
    "(\<lambda>omega. \<lambda>i\<in>I. omega (t i)) \<in>
      measurable (PiM K M) (PiM I (\<lambda>i. M (t i)))"
proof (rule measurable_restrict)
  fix i
  assume iI: "i \<in> I"
  have tiK: "t i \<in> K"
    using bijective iI unfolding bij_betw_def by auto
  show "(\<lambda>omega. omega (t i)) \<in> measurable (PiM K M) (M (t i))"
    by (rule measurable_component_singleton[OF tiK])
qed

lemma slp_integrable_PiM_reindex_bij_betw_iff:
  fixes f :: "('j \<Rightarrow> 'a) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes finite_I: "finite I"
    and finite_K: "finite K"
    and bijective: "bij_betw t I K"
    and f_measurable:
      "f \<in> borel_measurable (PiM I (\<lambda>i. M (t i)))"
  shows
    "integrable (PiM I (\<lambda>i. M (t i))) f \<longleftrightarrow>
      integrable (PiM K M)
        (\<lambda>omega. f (\<lambda>i\<in>I. omega (t i)))"
proof -
  let ?T = "\<lambda>omega. \<lambda>i\<in>I. omega (t i)"
  have T_measurable:
      "?T \<in> measurable (PiM K M) (PiM I (\<lambda>i. M (t i)))"
    by (rule slp_measurable_PiM_reindex_bij_betw[OF bijective])
  have distr_eq:
      "distr (PiM K M) (PiM I (\<lambda>i. M (t i))) ?T =
        PiM I (\<lambda>i. M (t i))"
    by (rule slp_distr_PiM_reindex_bij_betw[
          OF finite_I finite_K bijective])
  have transported:
      "integrable
          (distr (PiM K M) (PiM I (\<lambda>i. M (t i))) ?T) f \<longleftrightarrow>
        integrable (PiM K M) (\<lambda>omega. f (?T omega))"
    by (rule integrable_distr_eq[OF T_measurable f_measurable])
  show ?thesis
    using transported by (simp only: distr_eq)
qed

lemma slp_integral_PiM_reindex_bij_betw:
  fixes f :: "('j \<Rightarrow> 'a) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes finite_I: "finite I"
    and finite_K: "finite K"
    and bijective: "bij_betw t I K"
    and f_measurable:
      "f \<in> borel_measurable (PiM I (\<lambda>i. M (t i)))"
  shows
    "integral\<^sup>L (PiM I (\<lambda>i. M (t i))) f =
      integral\<^sup>L (PiM K M)
        (\<lambda>omega. f (\<lambda>i\<in>I. omega (t i)))"
proof -
  let ?T = "\<lambda>omega. \<lambda>i\<in>I. omega (t i)"
  have T_measurable:
      "?T \<in> measurable (PiM K M) (PiM I (\<lambda>i. M (t i)))"
    by (rule slp_measurable_PiM_reindex_bij_betw[OF bijective])
  have distr_eq:
      "distr (PiM K M) (PiM I (\<lambda>i. M (t i))) ?T =
        PiM I (\<lambda>i. M (t i))"
    by (rule slp_distr_PiM_reindex_bij_betw[
          OF finite_I finite_K bijective])
  have transported:
      "integral\<^sup>L
          (distr (PiM K M) (PiM I (\<lambda>i. M (t i))) ?T) f =
        integral\<^sup>L (PiM K M) (\<lambda>omega. f (?T omega))"
    by (rule integral_distr[OF T_measurable f_measurable])
  show ?thesis
    using transported by (simp only: distr_eq)
qed

end

end
