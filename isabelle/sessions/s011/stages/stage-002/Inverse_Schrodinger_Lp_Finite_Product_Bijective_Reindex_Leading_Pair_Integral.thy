theory Inverse_Schrodinger_Lp_Finite_Product_Bijective_Reindex_Leading_Pair_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Bijective_Reindex_Pair_Integral"
begin

section \<open>Paired finite-product reindexing under a leading factor\<close>

context product_sigma_finite
begin

lemma slp_distr_leading_PiM_pair_reindex_bij_betw:
  assumes finite_I: "finite I"
    and finite_K: "finite K"
    and bijective: "bij_betw t I K"
  shows
    "distr
        (L \<Otimes>\<^sub>M (PiM K M \<Otimes>\<^sub>M PiM K M))
        (L \<Otimes>\<^sub>M
          (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
            PiM I (\<lambda>i. M (t i))))
        (\<lambda>(leading, (left, right)).
          (leading,
            ((\<lambda>i\<in>I. left (t i)), (\<lambda>i\<in>I. right (t i))))) =
      L \<Otimes>\<^sub>M
        (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
          PiM I (\<lambda>i. M (t i)))"
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
  have R_sigma: "sigma_finite_measure ?R"
  proof -
    interpret target: finite_product_sigma_finite
      "\<lambda>i. M (t i)" I
      by standard fact
    have one_sigma:
        "sigma_finite_measure (PiM I (\<lambda>i. M (t i)))"
      by standard
    interpret one: sigma_finite_measure "PiM I (\<lambda>i. M (t i))"
      by (rule one_sigma)
    interpret pair: pair_sigma_finite
      "PiM I (\<lambda>i. M (t i))" "PiM I (\<lambda>i. M (t i))" ..
    show ?thesis
      by standard
  qed
  have id_measurable: "(\<lambda>x. x) \<in> measurable L L"
    by measurable
  have id_distr: "distr L L (\<lambda>x. x) = L"
    by simp
  note raw = slp_distr_pair_map_eq[
    OF id_measurable P_measurable id_distr P_distr R_sigma]
  show ?thesis
    using raw by (simp only: split_beta')
qed

lemma slp_integrable_leading_PiM_pair_reindex_bij_betw_iff:
  fixes f :: "('h \<times> (('j \<Rightarrow> 'a) \<times> ('j \<Rightarrow> 'a))) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes finite_I: "finite I"
    and finite_K: "finite K"
    and bijective: "bij_betw t I K"
    and f_measurable:
      "f \<in> borel_measurable
        (L \<Otimes>\<^sub>M
          (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
            PiM I (\<lambda>i. M (t i))))"
  shows
    "integrable
        (L \<Otimes>\<^sub>M
          (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
            PiM I (\<lambda>i. M (t i)))) f \<longleftrightarrow>
      integrable (L \<Otimes>\<^sub>M (PiM K M \<Otimes>\<^sub>M PiM K M))
        (\<lambda>(leading, (left, right)).
          f (leading,
            ((\<lambda>i\<in>I. left (t i)), (\<lambda>i\<in>I. right (t i)))))"
proof -
  let ?T = "\<lambda>omega. \<lambda>i\<in>I. omega (t i)"
  let ?P = "\<lambda>(left, right). (?T left, ?T right)"
  let ?Q = "\<lambda>omega. (fst omega, ?P (snd omega))"
  let ?S = "L \<Otimes>\<^sub>M (PiM K M \<Otimes>\<^sub>M PiM K M)"
  let ?R = "L \<Otimes>\<^sub>M
    (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
      PiM I (\<lambda>i. M (t i)))"
  have T_measurable:
      "?T \<in> measurable (PiM K M) (PiM I (\<lambda>i. M (t i)))"
    by (rule slp_measurable_PiM_reindex_bij_betw[OF bijective])
  have P_measurable:
      "?P \<in> measurable
        (PiM K M \<Otimes>\<^sub>M PiM K M)
        (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
          PiM I (\<lambda>i. M (t i)))"
    using T_measurable by measurable
  have Q_measurable: "?Q \<in> measurable ?S ?R"
    using P_measurable by measurable
  have Q_distr: "distr ?S ?R ?Q = ?R"
  proof -
    note raw = slp_distr_leading_PiM_pair_reindex_bij_betw[
      OF finite_I finite_K bijective, where L = L]
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have transported:
      "integrable (distr ?S ?R ?Q) f \<longleftrightarrow>
        integrable ?S (\<lambda>omega. f (?Q omega))"
    by (rule integrable_distr_eq[OF Q_measurable f_measurable])
  show ?thesis
    apply (subst (1) Q_distr[symmetric])
    using transported by (simp only: split_beta')
qed

lemma slp_integral_leading_PiM_pair_reindex_bij_betw:
  fixes f :: "('h \<times> (('j \<Rightarrow> 'a) \<times> ('j \<Rightarrow> 'a))) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes finite_I: "finite I"
    and finite_K: "finite K"
    and bijective: "bij_betw t I K"
    and f_measurable:
      "f \<in> borel_measurable
        (L \<Otimes>\<^sub>M
          (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
            PiM I (\<lambda>i. M (t i))))"
  shows
    "integral\<^sup>L
        (L \<Otimes>\<^sub>M
          (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
            PiM I (\<lambda>i. M (t i)))) f =
      integral\<^sup>L (L \<Otimes>\<^sub>M (PiM K M \<Otimes>\<^sub>M PiM K M))
        (\<lambda>(leading, (left, right)).
          f (leading,
            ((\<lambda>i\<in>I. left (t i)), (\<lambda>i\<in>I. right (t i)))))"
proof -
  let ?T = "\<lambda>omega. \<lambda>i\<in>I. omega (t i)"
  let ?P = "\<lambda>(left, right). (?T left, ?T right)"
  let ?Q = "\<lambda>omega. (fst omega, ?P (snd omega))"
  let ?S = "L \<Otimes>\<^sub>M (PiM K M \<Otimes>\<^sub>M PiM K M)"
  let ?R = "L \<Otimes>\<^sub>M
    (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
      PiM I (\<lambda>i. M (t i)))"
  have T_measurable:
      "?T \<in> measurable (PiM K M) (PiM I (\<lambda>i. M (t i)))"
    by (rule slp_measurable_PiM_reindex_bij_betw[OF bijective])
  have P_measurable:
      "?P \<in> measurable
        (PiM K M \<Otimes>\<^sub>M PiM K M)
        (PiM I (\<lambda>i. M (t i)) \<Otimes>\<^sub>M
          PiM I (\<lambda>i. M (t i)))"
    using T_measurable by measurable
  have Q_measurable: "?Q \<in> measurable ?S ?R"
    using P_measurable by measurable
  have Q_distr: "distr ?S ?R ?Q = ?R"
  proof -
    note raw = slp_distr_leading_PiM_pair_reindex_bij_betw[
      OF finite_I finite_K bijective, where L = L]
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have transported:
      "integral\<^sup>L (distr ?S ?R ?Q) f =
        integral\<^sup>L ?S (\<lambda>omega. f (?Q omega))"
    by (rule integral_distr[OF Q_measurable f_measurable])
  show ?thesis
    apply (subst (1) Q_distr[symmetric])
    using transported by (simp only: split_beta')
qed

end

end
