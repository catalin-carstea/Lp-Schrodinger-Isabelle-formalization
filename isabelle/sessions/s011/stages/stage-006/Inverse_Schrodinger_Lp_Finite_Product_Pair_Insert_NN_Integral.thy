theory Inverse_Schrodinger_Lp_Finite_Product_Pair_Insert_NN_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Pair_Insert_Integral"
begin

section \<open>Nonnegative integrals over two inserted finite-product families\<close>

context product_sigma_finite
begin

theorem slp_nn_integral_inserted_pair_heads_tails:
  fixes f :: "(('i \<Rightarrow> 'a) \<times> ('i \<Rightarrow> 'a)) \<Rightarrow> ennreal"
  assumes finite_I: "finite I"
    and i_notin: "i \<notin> I"
    and f_measurable:
      "f \<in> borel_measurable
        ((PiM (insert i I) M) \<Otimes>\<^sub>M (PiM (insert i I) M))"
  shows
    "nn_integral
        ((PiM (insert i I) M) \<Otimes>\<^sub>M (PiM (insert i I) M)) f =
      nn_integral
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
  let ?H = "(M i \<Otimes>\<^sub>M M i) \<Otimes>\<^sub>M (?T \<Otimes>\<^sub>M ?T)"
  let ?update = "\<lambda>(head, tail). tail(i := head)"
  let ?pair_update = "\<lambda>(positive, negative).
    (?update positive, ?update negative)"
  let ?middle = "\<lambda>((pos_head, pos_tail), (neg_head, neg_tail)).
    ((pos_head, neg_head), (pos_tail, neg_tail))"
  let ?interleaved_update =
    "\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
      (pos_tail(i := pos_head), neg_tail(i := neg_head))"
  let ?h = "\<lambda>coordinates. f (?interleaved_update coordinates)"
  have F_sigma: "sigma_finite_measure ?F"
    by (rule sigma_finite) (use finite_I in simp)
  have T_sigma: "sigma_finite_measure ?T"
    by (rule sigma_finite[OF finite_I])
  have i_sigma: "sigma_finite_measure (M i)"
    by (rule sigma_finite_measures)
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
  have pair_update_measurable:
      "?pair_update \<in> measurable ?V ?U"
  proof -
    have raw:
        "(\<lambda>coordinates.
          (?update (fst coordinates), ?update (snd coordinates)))
          \<in> measurable ?V ?U"
      by (rule measurable_Pair)
        (use update_measurable in measurable)
    show ?thesis
      using raw by (simp only: split_beta')
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
  have insert_union: "insert i I = I \<union> {i}"
    by simp
  have pos_tail_projection:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). pos_tail)
        \<in> measurable ?H ?T"
  proof -
    have first:
        "snd \<in> measurable ?H (?T \<Otimes>\<^sub>M ?T)"
      by (rule measurable_snd)
    have second:
        "fst \<in> measurable (?T \<Otimes>\<^sub>M ?T) ?T"
      by (rule measurable_fst)
    have raw: "(\<lambda>x. fst (snd x)) \<in> measurable ?H ?T"
      by (rule measurable_compose[OF first second])
    show ?thesis
      using raw by (simp only: comp_def split_beta')
  qed
  have neg_tail_projection:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). neg_tail)
        \<in> measurable ?H ?T"
  proof -
    have first:
        "snd \<in> measurable ?H (?T \<Otimes>\<^sub>M ?T)"
      by (rule measurable_snd)
    have second:
        "snd \<in> measurable (?T \<Otimes>\<^sub>M ?T) ?T"
      by (rule measurable_snd)
    have raw: "(\<lambda>x. snd (snd x)) \<in> measurable ?H ?T"
      by (rule measurable_compose[OF first second])
    show ?thesis
      using raw by (simp only: comp_def split_beta')
  qed
  have pos_head_projection:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). pos_head)
        \<in> measurable ?H (M i)"
  proof -
    have first:
        "fst \<in> measurable ?H (M i \<Otimes>\<^sub>M M i)"
      by (rule measurable_fst)
    have second:
        "fst \<in> measurable (M i \<Otimes>\<^sub>M M i) (M i)"
      by (rule measurable_fst)
    have raw: "(\<lambda>x. fst (fst x)) \<in> measurable ?H (M i)"
      by (rule measurable_compose[OF first second])
    show ?thesis
      using raw by (simp only: comp_def split_beta')
  qed
  have neg_head_projection:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). neg_head)
        \<in> measurable ?H (M i)"
  proof -
    have first:
        "fst \<in> measurable ?H (M i \<Otimes>\<^sub>M M i)"
      by (rule measurable_fst)
    have second:
        "snd \<in> measurable (M i \<Otimes>\<^sub>M M i) (M i)"
      by (rule measurable_snd)
    have raw: "(\<lambda>x. snd (fst x)) \<in> measurable ?H (M i)"
      by (rule measurable_compose[OF first second])
    show ?thesis
      using raw by (simp only: comp_def split_beta')
  qed
  have pos_full:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
        pos_tail(i := pos_head)) \<in> measurable ?H ?F"
  proof -
    note raw = measurable_fun_upd[
      where I="insert i I" and J=I and i=i and M=M
        and f="\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). pos_tail"
        and h="\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). pos_head",
      OF insert_union pos_tail_projection pos_head_projection]
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have neg_full:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
        neg_tail(i := neg_head)) \<in> measurable ?H ?F"
  proof -
    note raw = measurable_fun_upd[
      where I="insert i I" and J=I and i=i and M=M
        and f="\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). neg_tail"
        and h="\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). neg_head",
      OF insert_union neg_tail_projection neg_head_projection]
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have interleaved_update_measurable:
      "?interleaved_update \<in> measurable ?H ?U"
  proof -
    note raw = measurable_Pair[OF pos_full neg_full]
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have h_measurable: "?h \<in> borel_measurable ?H"
    using measurable_compose[OF interleaved_update_measurable f_measurable]
    by (simp only: comp_def)
  have middle_measurable: "?middle \<in> measurable ?V ?H"
  proof -
    have raw:
        "(\<lambda>x. ((fst (fst x), fst (snd x)),
          (snd (fst x), snd (snd x)))) \<in> measurable ?V ?H"
      by measurable
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have middle_distribution:
      "distr ?V ?H ?middle = ?H"
    by (rule slp_distr_four_factor_middle_swap[OF
          i_sigma i_sigma T_sigma T_sigma])
  have f_on_distribution:
      "f \<in> borel_measurable (distr ?V ?U ?pair_update)"
    using f_measurable pair_distribution by simp
  have update_transport:
      "nn_integral ?U f =
        nn_integral ?V (\<lambda>coordinates. f (?pair_update coordinates))"
  proof -
    note raw = nn_integral_distr[OF pair_update_measurable
      f_on_distribution]
    show ?thesis
      using raw pair_distribution by simp
  qed
  have h_on_distribution:
      "?h \<in> borel_measurable (distr ?V ?H ?middle)"
    using h_measurable middle_distribution by simp
  have middle_transport:
      "nn_integral ?H ?h =
        nn_integral ?V (\<lambda>coordinates. ?h (?middle coordinates))"
  proof -
    note raw = nn_integral_distr[OF middle_measurable h_on_distribution]
    show ?thesis
      using raw middle_distribution by simp
  qed
  have transported_functions:
      "(\<lambda>coordinates. f (?pair_update coordinates)) =
        (\<lambda>coordinates. ?h (?middle coordinates))"
    by (rule ext) (auto split: prod.split)
  have update_to_middle:
      "nn_integral ?U f =
        nn_integral ?V (\<lambda>coordinates. ?h (?middle coordinates))"
    using update_transport by (simp only: transported_functions)
  have final_transport:
      "nn_integral ?U f = nn_integral ?H ?h"
    by (rule trans[OF update_to_middle middle_transport[symmetric]])
  show ?thesis
    using final_transport by (simp only: split_beta')
qed

end

end
