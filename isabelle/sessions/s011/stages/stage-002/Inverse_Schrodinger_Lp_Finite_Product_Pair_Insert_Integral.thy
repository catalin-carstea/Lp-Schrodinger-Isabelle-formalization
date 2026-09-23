theory Inverse_Schrodinger_Lp_Finite_Product_Pair_Insert_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Pair_Head_Middle_Swap_Integral"
begin

section \<open>Two inserted finite-product families as interleaved heads and tails\<close>

context product_sigma_finite
begin

theorem slp_distr_product_insert_head:
  assumes finite_I: "finite I"
    and i_notin: "i \<notin> I"
  shows
    "distr (M i \<Otimes>\<^sub>M PiM I M) (PiM (insert i I) M)
        (\<lambda>(head, tail). tail(i := head)) =
      PiM (insert i I) M"
proof -
  let ?H = "PiM {i} M"
  let ?T = "PiM I M"
  let ?F = "PiM (insert i I) M"
  let ?S = "M i \<Otimes>\<^sub>M ?T"
  let ?P = "?H \<Otimes>\<^sub>M ?T"
  let ?embed = "\<lambda>(head, tail). ((\<lambda>j\<in>{i}. head), tail)"
  let ?update = "\<lambda>(head, tail). tail(i := head)"
  have tail_sigma: "sigma_finite_measure ?T"
    by (rule sigma_finite[OF finite_I])
  have head_embed_measurable:
      "(\<lambda>head. \<lambda>j\<in>{i}. head) \<in> measurable (M i) ?H"
    by (rule measurable_restrict) simp
  have tail_id_measurable:
      "(id :: ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a))
        \<in> measurable ?T ?T"
    by measurable
  have embed_measurable: "?embed \<in> measurable ?S ?P"
    using measurable_Pair[OF
      measurable_compose[OF measurable_fst head_embed_measurable]
      measurable_snd]
    by (simp only: comp_def split_beta')
  have head_distr:
      "distr (M i) ?H (\<lambda>head. \<lambda>j\<in>{i}. head) = ?H"
    by (rule distr_component)
  have tail_distr: "distr ?T ?T id = ?T"
    unfolding id_def by (rule distr_id)
  have product_components:
      "distr ?S ?P ?embed = ?P"
  proof -
    have raw:
        "distr (M i) ?H (\<lambda>head. \<lambda>j\<in>{i}. head)
            \<Otimes>\<^sub>M distr ?T ?T id =
          distr ?S ?P
            (\<lambda>(head, tail). ((\<lambda>j\<in>{i}. head), id tail))"
      by (rule pair_measure_distr[OF
            head_embed_measurable tail_id_measurable])
        (use tail_sigma tail_distr in simp)
    show ?thesis
      using raw head_distr tail_distr
      by (simp only: id_apply)
  qed
  have merge_measurable:
      "merge {i} I \<in> measurable ?P ?F"
    using measurable_merge[of "{i}" I M]
    by simp
  have merged_distr:
      "distr ?P ?F (merge {i} I) = ?F"
  proof -
    have raw:
        "distr ?P (PiM ({i} \<union> I) M) (merge {i} I) =
          PiM ({i} \<union> I) M"
      by (rule distr_merge) (use finite_I i_notin in auto)
    show ?thesis
      using raw by simp
  qed
  have composite_distr:
      "distr (distr ?S ?P ?embed) ?F (merge {i} I) =
        distr ?S ?F ((merge {i} I) \<circ> ?embed)"
    by (rule distr_distr[OF merge_measurable embed_measurable])
  have composed_eq:
      "distr ?S ?F ((merge {i} I) \<circ> ?embed) = ?F"
    using composite_distr product_components merged_distr by simp
  have maps_equal:
      "(merge {i} I \<circ> ?embed) coordinates = ?update coordinates"
    if coordinates_space: "coordinates \<in> space ?S"
    for coordinates
  proof -
    obtain head tail where coordinates: "coordinates = (head, tail)"
      by (cases coordinates)
    have tail_space: "tail \<in> space ?T"
      using coordinates_space unfolding coordinates
      by (simp only: space_pair_measure mem_Times_iff prod.sel)
    show ?thesis
      unfolding coordinates comp_def split_beta'
      using tail_space i_notin
      by (auto simp: merge_def space_PiM PiE_iff extensional_def
          fun_eq_iff)
  qed
  have same_distr:
      "distr ?S ?F ((merge {i} I) \<circ> ?embed) =
        distr ?S ?F ?update"
    by (rule distr_cong) (use maps_equal in auto)
  show ?thesis
    using composed_eq same_distr by simp
qed

theorem slp_integral_inserted_pair_heads_tails:
  fixes f :: "(('i \<Rightarrow> 'a) \<times> ('i \<Rightarrow> 'a)) \<Rightarrow>
    'b::{banach, second_countable_topology}"
  assumes finite_I: "finite I"
    and i_notin: "i \<notin> I"
    and f_integrable:
      "integrable
        ((PiM (insert i I) M) \<Otimes>\<^sub>M (PiM (insert i I) M)) f"
  shows
    "integral\<^sup>L
        ((PiM (insert i I) M) \<Otimes>\<^sub>M (PiM (insert i I) M)) f =
      integral\<^sup>L
        ((M i \<Otimes>\<^sub>M M i) \<Otimes>\<^sub>M
          ((PiM I M) \<Otimes>\<^sub>M (PiM I M)))
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          f (pos_tail(i := pos_head), neg_tail(i := neg_head)))"
proof -
  let ?T = "PiM I M"
  let ?F = "PiM (insert i I) M"
  let ?S = "M i \<Otimes>\<^sub>M ?T"
  let ?U = "?F \<Otimes>\<^sub>M ?F"
  let ?V = "?S \<Otimes>\<^sub>M ?S"
  let ?update = "\<lambda>(head, tail). tail(i := head)"
  let ?pair_update = "\<lambda>(positive, negative).
    (?update positive, ?update negative)"
  let ?g = "\<lambda>((pos_head, pos_tail), (neg_head, neg_tail)).
    f (pos_tail(i := pos_head), neg_tail(i := neg_head))"
  have F_sigma: "sigma_finite_measure ?F"
    by (rule sigma_finite) (use finite_I in simp)
  have swap_measurable:
      "(\<lambda>(head, tail). (tail, head))
        \<in> measurable ?S (?T \<Otimes>\<^sub>M M i)"
    by (rule measurable_pair_swap')
  have add_measurable:
      "(\<lambda>(tail, head). tail(i := head))
        \<in> measurable (?T \<Otimes>\<^sub>M M i) ?F"
    by (rule measurable_add_dim)
  have update_measurable: "?update \<in> measurable ?S ?F"
    using measurable_compose[OF swap_measurable add_measurable]
    by (simp only: comp_def split_beta' fst_conv snd_conv)
  have fst_measurable:
      "(fst :: (('a \<times> ('i \<Rightarrow> 'a)) \<times>
          ('a \<times> ('i \<Rightarrow> 'a))) \<Rightarrow>
          ('a \<times> ('i \<Rightarrow> 'a)))
        \<in> measurable ?V ?S"
    by measurable
  have snd_measurable:
      "(snd :: (('a \<times> ('i \<Rightarrow> 'a)) \<times>
          ('a \<times> ('i \<Rightarrow> 'a))) \<Rightarrow>
          ('a \<times> ('i \<Rightarrow> 'a)))
        \<in> measurable ?V ?S"
    by measurable
  have positive_measurable:
      "?update \<circ> fst \<in> measurable ?V ?F"
    by (rule measurable_comp[OF fst_measurable update_measurable])
  have negative_measurable:
      "?update \<circ> snd \<in> measurable ?V ?F"
    by (rule measurable_comp[OF snd_measurable update_measurable])
  have positive_direct:
      "(\<lambda>coordinates. ?update (fst coordinates))
        \<in> measurable ?V ?F"
    using positive_measurable by (simp only: comp_def)
  have negative_direct:
      "(\<lambda>coordinates. ?update (snd coordinates))
        \<in> measurable ?V ?F"
    using negative_measurable by (simp only: comp_def)
  have pair_update_measurable:
      "?pair_update \<in> measurable ?V ?U"
  proof -
    have raw:
        "(\<lambda>coordinates.
          (?update (fst coordinates), ?update (snd coordinates)))
          \<in> measurable ?V ?U"
      by (rule measurable_Pair[OF
            positive_direct negative_direct])
    show ?thesis
      using raw by (simp only: comp_apply split_beta')
  qed
  have single_distribution:
      "distr ?S ?F ?update = ?F"
    by (rule slp_distr_product_insert_head[OF finite_I i_notin])
  have pair_distribution:
      "distr ?V ?U ?pair_update = ?U"
  proof -
    have raw:
        "distr ?S ?F ?update \<Otimes>\<^sub>M distr ?S ?F ?update =
          distr ?V ?U
            (\<lambda>(positive, negative).
              (?update positive, ?update negative))"
      by (rule pair_measure_distr[OF
            update_measurable update_measurable])
        (use F_sigma single_distribution in simp)
    show ?thesis
      using raw single_distribution by (simp only: split_beta')
  qed
  have f_measurable: "f \<in> borel_measurable ?U"
    using f_integrable by simp
  have g_integrable: "integrable ?V ?g"
  proof -
    have distr_integrable:
        "integrable (distr ?V ?U ?pair_update) f"
      using pair_distribution f_integrable by simp
    have raw:
        "integrable ?V (\<lambda>coordinates. f (?pair_update coordinates))"
      by (rule integrable_distr[OF
            pair_update_measurable distr_integrable])
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have source_to_grouped:
      "integral\<^sup>L ?U f = integral\<^sup>L ?V ?g"
  proof -
    note transported = integral_distr[OF
      pair_update_measurable f_measurable]
    show ?thesis
      using transported pair_distribution
      by (simp only: comp_def split_beta')
  qed
  have grouped_to_interleaved:
      "integral\<^sup>L ?V ?g =
        integral\<^sup>L
          ((M i \<Otimes>\<^sub>M M i) \<Otimes>\<^sub>M (?T \<Otimes>\<^sub>M ?T))
          (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
            ?g ((pos_head, pos_tail), (neg_head, neg_tail)))"
    by (rule slp_integral_inserted_pair_head_middle_swap[OF
          finite_I g_integrable])
  have interleaved_integrand:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          ?g ((pos_head, pos_tail), (neg_head, neg_tail))) =
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          f (pos_tail(i := pos_head), neg_tail(i := neg_head)))"
    by (rule ext) (auto split: prod.split)
  have grouped_to_target:
      "integral\<^sup>L ?V ?g =
        integral\<^sup>L
          ((M i \<Otimes>\<^sub>M M i) \<Otimes>\<^sub>M (?T \<Otimes>\<^sub>M ?T))
          (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
            f (pos_tail(i := pos_head), neg_tail(i := neg_head)))"
    using grouped_to_interleaved unfolding interleaved_integrand .
  show ?thesis
    using source_to_grouped grouped_to_target by simp
qed

end


end
