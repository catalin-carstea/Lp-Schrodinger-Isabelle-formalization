theory Inverse_Schrodinger_Lp_Finite_Product_Bijective_Reindex_Pair_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Bijective_Reindex_Integral"
begin

section \<open>Paired complex transport across finite product reindexing\<close>

context product_sigma_finite
begin

lemma slp_distr_PiM_pair_reindex_bij_betw:
  assumes finite_I: "finite I"
    and finite_K: "finite K"
    and bijective: "bij_betw t I K"
  shows
    "distr
        (PiM K M \<Otimes>\<^sub>M PiM K M)
        (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
          PiM I (\<lambda>i. M (t i)))
        (\<lambda>(left, right).
          ((\<lambda>i\<in>I. left (t i)), (\<lambda>i\<in>I. right (t i)))) =
      PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
        PiM I (\<lambda>i. M (t i))"
proof -
  let ?T = "\<lambda>omega. \<lambda>i\<in>I. omega (t i)"
  let ?S = "PiM K M"
  let ?R = "PiM I (\<lambda>i. M (t i))"
  have T_measurable: "?T \<in> measurable ?S ?R"
    by (rule slp_measurable_PiM_reindex_bij_betw[OF bijective])
  have T_distr: "distr ?S ?R ?T = ?R"
    by (rule slp_distr_PiM_reindex_bij_betw[
          OF finite_I finite_K bijective])
  have R_sigma: "sigma_finite_measure ?R"
  proof -
    interpret target: finite_product_sigma_finite
      "\<lambda>i. M (t i)" I
      by standard fact
    show ?thesis ..
  qed
  show ?thesis
    by (rule slp_distr_pair_map_eq[
          OF T_measurable T_measurable T_distr T_distr R_sigma])
qed

lemma slp_integrable_PiM_pair_reindex_bij_betw_iff:
  fixes f :: "(('j \<Rightarrow> 'a) \<times> ('j \<Rightarrow> 'a)) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes finite_I: "finite I"
    and finite_K: "finite K"
    and bijective: "bij_betw t I K"
    and f_measurable:
      "f \<in> borel_measurable
        (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
          PiM I (\<lambda>i. M (t i)))"
  shows
    "integrable
        (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
          PiM I (\<lambda>i. M (t i))) f \<longleftrightarrow>
      integrable (PiM K M \<Otimes>\<^sub>M PiM K M)
        (\<lambda>(left, right).
          f ((\<lambda>i\<in>I. left (t i)), (\<lambda>i\<in>I. right (t i))))"
proof -
  let ?T = "\<lambda>omega. \<lambda>i\<in>I. omega (t i)"
  let ?P = "\<lambda>(left, right). (?T left, ?T right)"
  let ?S = "PiM K M \<Otimes>\<^sub>M PiM K M"
  let ?R = "PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
    PiM I (\<lambda>i. M (t i))"
  have T_measurable:
      "?T \<in> measurable (PiM K M) (PiM I (\<lambda>i. M (t i)))"
    by (rule slp_measurable_PiM_reindex_bij_betw[OF bijective])
  have P_measurable: "?P \<in> measurable ?S ?R"
    using T_measurable by measurable
  have P_distr: "distr ?S ?R ?P = ?R"
    by (rule slp_distr_PiM_pair_reindex_bij_betw[
          OF finite_I finite_K bijective])
  have transported:
      "integrable (distr ?S ?R ?P) f \<longleftrightarrow>
        integrable ?S (\<lambda>omega. f (?P omega))"
    by (rule integrable_distr_eq[OF P_measurable f_measurable])
  have transported_rewritten:
      "integrable ?R f \<longleftrightarrow>
        integrable ?S (\<lambda>omega. f (?P omega))"
    using transported by (simp only: P_distr)
  show ?thesis
    using transported_rewritten by (simp only: split_beta')
qed

lemma slp_integral_PiM_pair_reindex_bij_betw:
  fixes f :: "(('j \<Rightarrow> 'a) \<times> ('j \<Rightarrow> 'a)) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes finite_I: "finite I"
    and finite_K: "finite K"
    and bijective: "bij_betw t I K"
    and f_measurable:
      "f \<in> borel_measurable
        (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
          PiM I (\<lambda>i. M (t i)))"
  shows
    "integral\<^sup>L
        (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
          PiM I (\<lambda>i. M (t i))) f =
      integral\<^sup>L (PiM K M \<Otimes>\<^sub>M PiM K M)
        (\<lambda>(left, right).
          f ((\<lambda>i\<in>I. left (t i)), (\<lambda>i\<in>I. right (t i))))"
proof -
  let ?T = "\<lambda>omega. \<lambda>i\<in>I. omega (t i)"
  let ?P = "\<lambda>(left, right). (?T left, ?T right)"
  let ?S = "PiM K M \<Otimes>\<^sub>M PiM K M"
  let ?R = "PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
    PiM I (\<lambda>i. M (t i))"
  have T_measurable:
      "?T \<in> measurable (PiM K M) (PiM I (\<lambda>i. M (t i)))"
    by (rule slp_measurable_PiM_reindex_bij_betw[OF bijective])
  have P_measurable: "?P \<in> measurable ?S ?R"
    using T_measurable by measurable
  have P_distr: "distr ?S ?R ?P = ?R"
    by (rule slp_distr_PiM_pair_reindex_bij_betw[
          OF finite_I finite_K bijective])
  have transported:
      "integral\<^sup>L (distr ?S ?R ?P) f =
        integral\<^sup>L ?S (\<lambda>omega. f (?P omega))"
    by (rule integral_distr[OF P_measurable f_measurable])
  have transported_rewritten:
      "integral\<^sup>L ?R f =
        integral\<^sup>L ?S (\<lambda>omega. f (?P omega))"
    using transported by (simp only: P_distr)
  show ?thesis
    using transported_rewritten by (simp only: split_beta')
qed

end

end
