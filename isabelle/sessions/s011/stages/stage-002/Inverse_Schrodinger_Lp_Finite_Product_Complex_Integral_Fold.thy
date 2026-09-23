theory Inverse_Schrodinger_Lp_Finite_Product_Complex_Integral_Fold
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Fubini"
begin

section \<open>Complex Bochner folding across finite product coordinates\<close>

context product_sigma_finite
begin

lemma slp_integrable_PiM_fold_iff:
  fixes f :: "('i \<Rightarrow> 'a) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes disjoint: "I \<inter> J = {}"
    and finite_I: "finite I"
    and finite_J: "finite J"
    and f_measurable: "f \<in> borel_measurable (PiM (I \<union> J) M)"
  shows
    "integrable (PiM (I \<union> J) M) f \<longleftrightarrow>
      integrable (PiM I M \<Otimes>\<^sub>M PiM J M)
        (\<lambda>coordinates. f (merge I J coordinates))"
proof -
  let ?P = "PiM I M \<Otimes>\<^sub>M PiM J M"
  let ?U = "PiM (I \<union> J) M"
  have merge_measurable: "merge I J \<in> measurable ?P ?U"
    by (rule measurable_merge)
  have merge_distr: "distr ?P ?U (merge I J) = ?U"
    by (rule distr_merge[OF disjoint finite_I finite_J])
  have transported:
      "integrable (distr ?P ?U (merge I J)) f \<longleftrightarrow>
        integrable ?P (\<lambda>coordinates. f (merge I J coordinates))"
    by (rule integrable_distr_eq[OF merge_measurable f_measurable])
  show ?thesis
    using transported by (simp only: merge_distr)
qed

lemma slp_integral_PiM_fold:
  fixes f :: "('i \<Rightarrow> 'a) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes disjoint: "I \<inter> J = {}"
    and finite_I: "finite I"
    and finite_J: "finite J"
    and f_measurable: "f \<in> borel_measurable (PiM (I \<union> J) M)"
  shows
    "integral\<^sup>L (PiM (I \<union> J) M) f =
      integral\<^sup>L (PiM I M \<Otimes>\<^sub>M PiM J M)
        (\<lambda>coordinates. f (merge I J coordinates))"
proof -
  let ?P = "PiM I M \<Otimes>\<^sub>M PiM J M"
  let ?U = "PiM (I \<union> J) M"
  have merge_measurable: "merge I J \<in> measurable ?P ?U"
    by (rule measurable_merge)
  have merge_distr: "distr ?P ?U (merge I J) = ?U"
    by (rule distr_merge[OF disjoint finite_I finite_J])
  have transported:
      "integral\<^sup>L (distr ?P ?U (merge I J)) f =
        integral\<^sup>L ?P
          (\<lambda>coordinates. f (merge I J coordinates))"
    by (rule integral_distr[OF merge_measurable f_measurable])
  show ?thesis
    using transported by (simp only: merge_distr)
qed

lemma slp_integral_PiM_fold_fubini:
  fixes f :: "('i \<Rightarrow> 'a) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes disjoint: "I \<inter> J = {}"
    and finite_I: "finite I"
    and finite_J: "finite J"
    and f_measurable: "f \<in> borel_measurable (PiM (I \<union> J) M)"
    and f_integrable: "integrable (PiM (I \<union> J) M) f"
  shows
    "integral\<^sup>L (PiM (I \<union> J) M) f =
      (\<integral>left. (\<integral>right. f (merge I J (left, right))
          \<partial>PiM J M) \<partial>PiM I M)"
proof -
  let ?PI = "PiM I M"
  let ?PJ = "PiM J M"
  let ?P = "?PI \<Otimes>\<^sub>M ?PJ"
  let ?pulled = "\<lambda>coordinates. f (merge I J coordinates)"
  interpret left: finite_product_sigma_finite M I
    by standard fact
  interpret right: finite_product_sigma_finite M J
    by standard fact
  interpret pair: pair_sigma_finite ?PI ?PJ ..
  have pulled_integrable: "integrable ?P ?pulled"
    using slp_integrable_PiM_fold_iff[OF disjoint finite_I finite_J
        f_measurable]
      f_integrable
    by simp
  have iterated:
      "(\<integral>left. (\<integral>right. f (merge I J (left, right))
          \<partial>?PJ) \<partial>?PI) =
        integral\<^sup>L ?P ?pulled"
    using pair.integral_fst'[OF pulled_integrable]
    by simp
  have folded:
      "integral\<^sup>L (PiM (I \<union> J) M) f =
        integral\<^sup>L ?P ?pulled"
    by (rule slp_integral_PiM_fold[OF disjoint finite_I finite_J
          f_measurable])
  show ?thesis
    using folded iterated by simp
qed

end

end
