theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Shifted_Reindex
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Bijective_Reindex_Pair_Integral"
begin

section \<open>Predecessor reindexing of shifted natural graph coordinates\<close>

lemma slp_predecessor_bij_betw_shifted:
  "bij_betw (\<lambda>i::nat. i - 1) {1..<Suc n} {..<n}"
  by (rule bij_betwI[where g = Suc]) auto

theorem slp_integrable_PiM_pair_shifted_predecessor_iff:
  fixes f :: "((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point))
    \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f_measurable:
    "f \<in> borel_measurable
      (PiM {1..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))
        \<Otimes>\<^sub>M
       PiM {1..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure)))"
  shows
    "integrable
        (PiM {1..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))
          \<Otimes>\<^sub>M
         PiM {1..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))) f
      \<longleftrightarrow>
      integrable
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))
          \<Otimes>\<^sub>M
         PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
        (\<lambda>(positive, negative).
          f ((\<lambda>i\<in>{1..<Suc n}. positive (i - 1)),
             (\<lambda>i\<in>{1..<Suc n}. negative (i - 1))))"
proof -
  interpret planar: product_sigma_finite
    "\<lambda>_::nat. (lborel :: slp_point measure)"
    by standard
  note raw = planar.slp_integrable_PiM_pair_reindex_bij_betw_iff[
    where I = "{1..<Suc n}" and K = "{..<n}"
      and t = "\<lambda>i::nat. i - 1" and f = f,
    OF _ _ slp_predecessor_bij_betw_shifted f_measurable]
  show ?thesis
    using raw by simp
qed

theorem slp_integral_PiM_pair_shifted_predecessor:
  fixes f :: "((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point))
    \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f_measurable:
    "f \<in> borel_measurable
      (PiM {1..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))
        \<Otimes>\<^sub>M
       PiM {1..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure)))"
  shows
    "integral\<^sup>L
        (PiM {1..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))
          \<Otimes>\<^sub>M
         PiM {1..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))) f =
      integral\<^sup>L
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))
          \<Otimes>\<^sub>M
         PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
        (\<lambda>(positive, negative).
          f ((\<lambda>i\<in>{1..<Suc n}. positive (i - 1)),
             (\<lambda>i\<in>{1..<Suc n}. negative (i - 1))))"
proof -
  interpret planar: product_sigma_finite
    "\<lambda>_::nat. (lborel :: slp_point measure)"
    by standard
  note raw = planar.slp_integral_PiM_pair_reindex_bij_betw[
    where I = "{1..<Suc n}" and K = "{..<n}"
      and t = "\<lambda>i::nat. i - 1" and f = f,
    OF _ _ slp_predecessor_bij_betw_shifted f_measurable]
  show ?thesis
    using raw by simp
qed

theorem slp_left_graph_indices_shifted_predecessor:
  fixes positive negative :: "nat \<Rightarrow> slp_point"
    and terminal :: slp_point
  shows
    "slp_left_branch_oscillatory_graph_kernel_indices [1..<Suc n] tau center
        cutoff potential terminal_value origin
        (((\<lambda>i\<in>{1..<Suc n}. positive (i - 1)),
          (\<lambda>i\<in>{1..<Suc n}. negative (i - 1))), terminal) =
      slp_left_branch_oscillatory_graph_kernel_indices [0..<n] tau center
        cutoff potential terminal_value origin
        ((positive, negative), terminal)"
proof -
  have shifted_indices:
      "map (\<lambda>i::nat. i - 1) [1..<Suc n] = [0..<n]"
    using map_decr_upt[where m = 0 and n = n]
    by simp
  have pairs:
      "map (\<lambda>i. (positive (i - 1), negative (i - 1))) [1..<Suc n] =
        map (\<lambda>i. (positive i, negative i)) [0..<n]"
  proof -
    have mapped:
        "map (\<lambda>i. (positive i, negative i))
            (map (\<lambda>i::nat. i - 1) [1..<Suc n]) =
          map (\<lambda>i. (positive i, negative i)) [0..<n]"
      using shifted_indices by simp
    show ?thesis
      using mapped by (simp only: map_map comp_def)
  qed
  have guarded_pairs:
      "map (\<lambda>i.
          ((\<lambda>j\<in>{1..<Suc n}. positive (j - 1)) i,
           (\<lambda>j\<in>{1..<Suc n}. negative (j - 1)) i)) [1..<Suc n] =
        map (\<lambda>i. (positive i, negative i)) [0..<n]"
  proof -
    have guard:
        "map (\<lambda>i.
            ((\<lambda>j\<in>{1..<Suc n}. positive (j - 1)) i,
             (\<lambda>j\<in>{1..<Suc n}. negative (j - 1)) i)) [1..<Suc n] =
          map (\<lambda>i. (positive (i - 1), negative (i - 1))) [1..<Suc n]"
      by (rule map_cong) auto
    show ?thesis
      using guard pairs by (rule trans)
  qed
  show ?thesis
    unfolding slp_left_branch_oscillatory_graph_kernel_indices_def
    by (simp only: prod.sel guarded_pairs)
qed

end
