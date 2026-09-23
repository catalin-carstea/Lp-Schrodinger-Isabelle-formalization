theory Inverse_Schrodinger_Lp_Finite_Product_Complex_Integral_Insert_Rev
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Complex_Integral_Fold"
begin

section \<open>Head-first complex integration over an inserted coordinate\<close>

context product_sigma_finite
begin

lemma slp_product_integral_insert_rev:
  fixes f :: "('i \<Rightarrow> 'a) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes finite_I: "finite I"
    and i_notin: "i \<notin> I"
    and f_integrable: "integrable (PiM (insert i I) M) f"
  shows
    "integral\<^sup>L (PiM (insert i I) M) f =
      (\<integral>head. (\<integral>tail. f (tail(i := head)) \<partial>PiM I M)
        \<partial>M i)"
proof -
  let ?PI = "PiM I M"
  let ?H = "\<lambda>head. integral\<^sup>L ?PI (\<lambda>tail. f (tail(i := head)))"
  interpret tail: finite_product_sigma_finite M I
    by standard fact
  have f_measurable:
      "f \<in> borel_measurable (PiM (insert i I) M)"
    using f_integrable by simp
  have head_tail_measurable:
      "case_prod (\<lambda>head tail. f (tail(i := head)))
        \<in> borel_measurable (M i \<Otimes>\<^sub>M ?PI)"
  proof -
    have swap_measurable:
        "(\<lambda>(head, tail). (tail, head))
          \<in> measurable (M i \<Otimes>\<^sub>M ?PI) (?PI \<Otimes>\<^sub>M M i)"
      by (rule measurable_pair_swap')
    have update_measurable:
        "(\<lambda>(tail, head). tail(i := head))
          \<in> measurable (?PI \<Otimes>\<^sub>M M i)
            (PiM (insert i I) M)"
      by (rule measurable_add_dim)
    have swapped_update_measurable:
        "(\<lambda>(head, tail). tail(i := head))
        \<in> measurable (M i \<Otimes>\<^sub>M ?PI)
          (PiM (insert i I) M)"
      using measurable_compose[OF swap_measurable update_measurable]
      by (simp only: comp_def split_beta' fst_conv snd_conv)
    have composed:
        "f \<circ> (\<lambda>(head, tail). tail(i := head))
          \<in> borel_measurable (M i \<Otimes>\<^sub>M ?PI)"
      by (rule measurable_comp[OF swapped_update_measurable f_measurable])
    show ?thesis
      using composed by (simp only: comp_def split_beta')
  qed
  have H_measurable: "?H \<in> borel_measurable (M i)"
    by (rule tail.borel_measurable_lebesgue_integral[OF
          head_tail_measurable])
  have folded:
      "integral\<^sup>L (PiM (insert i I) M) f =
        (\<integral>head_coordinates. (\<integral>tail_coordinates.
          f (merge {i} I (head_coordinates, tail_coordinates)) \<partial>?PI)
          \<partial>PiM {i} M)"
  proof -
    have raw:
        "integral\<^sup>L (PiM ({i} \<union> I) M) f =
          (\<integral>head_coordinates. (\<integral>tail_coordinates.
            f (merge {i} I (head_coordinates, tail_coordinates)) \<partial>?PI)
            \<partial>PiM {i} M)"
      by (rule product_integral_fold[OF _ _ _])
        (use finite_I i_notin f_integrable in auto)
    show ?thesis
      using raw by simp
  qed
  have inner_merge:
      "(\<integral>tail_coordinates.
          f (merge {i} I (head_coordinates, tail_coordinates)) \<partial>?PI) =
        ?H (head_coordinates i)"
    if head_space: "head_coordinates \<in> space (PiM {i} M)"
    for head_coordinates
  proof -
    have pointwise:
        "f (merge {i} I (head_coordinates, tail_coordinates)) =
          f (tail_coordinates(i := head_coordinates i))"
      if tail_space: "tail_coordinates \<in> space ?PI"
      for tail_coordinates
    proof -
      have merged:
          "merge {i} I (head_coordinates, tail_coordinates) =
            tail_coordinates(i := head_coordinates i)"
        using head_space tail_space i_notin
        by (auto simp: merge_def space_PiM PiE_iff extensional_def
            fun_eq_iff)
      show ?thesis
        by (simp only: merged)
    qed
    show ?thesis
      apply (rule Bochner_Integration.integral_cong[OF refl])
      by (rule pointwise)
  qed
  have outer_rewrite:
      "(\<integral>head_coordinates. (\<integral>tail_coordinates.
          f (merge {i} I (head_coordinates, tail_coordinates)) \<partial>?PI)
          \<partial>PiM {i} M) =
        (\<integral>head_coordinates. ?H (head_coordinates i)
          \<partial>PiM {i} M)"
    by (rule Bochner_Integration.integral_cong[OF refl]) (rule inner_merge)
  have singleton:
      "(\<integral>head_coordinates. ?H (head_coordinates i)
          \<partial>PiM {i} M) =
        integral\<^sup>L (M i) ?H"
    by (rule product_integral_singleton[OF H_measurable])
  show ?thesis
    using folded outer_rewrite singleton by simp
qed

end

end
