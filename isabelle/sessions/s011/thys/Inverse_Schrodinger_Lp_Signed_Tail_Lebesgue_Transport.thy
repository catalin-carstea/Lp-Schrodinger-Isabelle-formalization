theory Inverse_Schrodinger_Lp_Signed_Tail_Lebesgue_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Signed_Product_Lebesgue_Transport"
begin

section \<open>Merging the positive and negative signed tail coordinates\<close>

definition slp_signed_tail_reindex ::
    "(('i + 'j) \<times> bool) \<Rightarrow> (('i \<times> bool) + ('j \<times> bool))"
where
  "slp_signed_tail_reindex sb =
    (case sb of
      (Inl i, b) \<Rightarrow> Inl (i, b)
    | (Inr j, b) \<Rightarrow> Inr (j, b))"

definition slp_signed_tail_unreindex ::
    "(('i \<times> bool) + ('j \<times> bool)) \<Rightarrow> (('i + 'j) \<times> bool)"
where
  "slp_signed_tail_unreindex k =
    (case k of
      Inl (i, b) \<Rightarrow> (Inl i, b)
    | Inr (j, b) \<Rightarrow> (Inr j, b))"

lemma slp_signed_tail_unreindex_reindex:
  "slp_signed_tail_unreindex (slp_signed_tail_reindex k) = k"
  by (simp add: slp_signed_tail_reindex_def
      slp_signed_tail_unreindex_def split: sum.splits prod.splits)

lemma slp_signed_tail_reindex_unreindex:
  "slp_signed_tail_reindex (slp_signed_tail_unreindex k) = k"
  by (simp add: slp_signed_tail_reindex_def
      slp_signed_tail_unreindex_def split: sum.splits prod.splits)

lemma slp_signed_tail_reindex_bij:
  "bij (slp_signed_tail_reindex ::
    (('i + 'j) \<times> bool) \<Rightarrow> (('i \<times> bool) + ('j \<times> bool)))"
proof (rule bijI)
  show "inj (slp_signed_tail_reindex ::
      (('i + 'j) \<times> bool) \<Rightarrow> (('i \<times> bool) + ('j \<times> bool)))"
  proof (rule injI)
    fix x y :: "('i + 'j) \<times> bool"
    assume equal: "slp_signed_tail_reindex x = slp_signed_tail_reindex y"
    have "slp_signed_tail_unreindex (slp_signed_tail_reindex x) =
        slp_signed_tail_unreindex (slp_signed_tail_reindex y)"
      by (simp only: equal)
    then show "x = y"
      by (simp only: slp_signed_tail_unreindex_reindex)
  qed
  show "surj (slp_signed_tail_reindex ::
      (('i + 'j) \<times> bool) \<Rightarrow> (('i \<times> bool) + ('j \<times> bool)))"
  proof (rule surjI[where f = slp_signed_tail_unreindex])
    fix k :: "('i \<times> bool) + ('j \<times> bool)"
    show "slp_signed_tail_reindex (slp_signed_tail_unreindex k) = k"
      by (rule slp_signed_tail_reindex_unreindex)
  qed
qed

definition slp_signed_tail_merge ::
    "(real^('i::finite \<times> bool)) \<times> (real^('j::finite \<times> bool))
      \<Rightarrow> real^(('i + 'j) \<times> bool)"
where
  "slp_signed_tail_merge =
    (\<lambda>x. \<chi> sb. x $ slp_signed_tail_reindex sb) \<circ>
      slp_cartesian_sum_merge"

theorem slp_signed_tail_merge_distr_lborel:
  "distr
      ((lborel :: (real^('i::finite \<times> bool)) measure) \<Otimes>\<^sub>M
        (lborel :: (real^('j::finite \<times> bool)) measure))
      (lborel :: (real^(('i + 'j) \<times> bool)) measure)
      slp_signed_tail_merge =
    (lborel :: (real^(('i + 'j) \<times> bool)) measure)"
proof -
  let ?S =
    "(lborel :: (real^('i \<times> bool)) measure) \<Otimes>\<^sub>M
      (lborel :: (real^('j \<times> bool)) measure)"
  let ?F = "slp_cartesian_sum_merge ::
    ((real^('i \<times> bool)) \<times> (real^('j \<times> bool))) \<Rightarrow>
      real^(('i \<times> bool) + ('j \<times> bool))"
  let ?R = "\<lambda>x::real^(('i \<times> bool) + ('j \<times> bool)).
    \<chi> sb. x $ slp_signed_tail_reindex sb"
  have F_measurable:
    "?F \<in> measurable ?S
      (lborel :: (real^(('i \<times> bool) + ('j \<times> bool))) measure)"
    by (rule slp_cartesian_sum_merge_measurable)
  have R_measurable:
    "?R \<in> measurable
      (lborel :: (real^(('i \<times> bool) + ('j \<times> bool))) measure)
      borel"
    using slp_cartesian_coordinate_reindex_measurable[
      of slp_signed_tail_reindex]
    by (simp only: measurable_lborel2)
  have merged:
    "distr ?S
        (lborel :: (real^(('i \<times> bool) + ('j \<times> bool))) measure)
        ?F =
      (lborel :: (real^(('i \<times> bool) + ('j \<times> bool))) measure)"
    by (rule slp_cartesian_sum_merge_distr_lborel)
  have reindexed:
    "distr
        (lborel :: (real^(('i \<times> bool) + ('j \<times> bool))) measure)
        borel ?R =
      (lborel :: (real^(('i + 'j) \<times> bool)) measure)"
    by (rule slp_lborel_cartesian_coordinate_reindex)
      (rule slp_signed_tail_reindex_bij)
  have target_change:
    "distr ?S (lborel :: (real^(('i + 'j) \<times> bool)) measure)
        slp_signed_tail_merge =
      distr ?S borel slp_signed_tail_merge"
  proof (rule distr_cong)
    show "?S = ?S"
      by (rule refl)
    show "sets (lborel :: (real^(('i + 'j) \<times> bool)) measure) =
        sets borel"
      by (rule sets_lborel)
    show "slp_signed_tail_merge x = slp_signed_tail_merge x"
      for x :: "(real^('i \<times> bool)) \<times> (real^('j \<times> bool))"
      by (rule refl)
  qed
  have "distr ?S (lborel :: (real^(('i + 'j) \<times> bool)) measure)
      slp_signed_tail_merge =
    distr ?S borel slp_signed_tail_merge"
    by (rule target_change)
  also have "... = distr ?S borel (?R \<circ> ?F)"
    by (simp only: slp_signed_tail_merge_def)
  also have "... = distr
      (distr ?S
        (lborel :: (real^(('i \<times> bool) + ('j \<times> bool))) measure) ?F)
      borel ?R"
    by (rule distr_distr[OF R_measurable F_measurable, symmetric])
  also have "... = distr
      (lborel :: (real^(('i \<times> bool) + ('j \<times> bool))) measure)
      borel ?R"
    by (simp only: merged)
  also have "... = (lborel :: (real^(('i + 'j) \<times> bool)) measure)"
    by (rule reindexed)
  finally show ?thesis .
qed

end
