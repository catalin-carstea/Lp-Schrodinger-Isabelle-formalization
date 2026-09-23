theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Pack"
begin

section \<open>Lebesgue transport for solved-center active coordinates\<close>

definition slp_mixed_center_finite_raw_tail_pack ::
    "(((((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point) \<times>
        ((slp_point^'j::finite) \<times> (slp_point^'j)))) \<Rightarrow>
      real^(((unit + ('i + 'i)) + ('j + 'j)) \<times> bool)"
where
  "slp_mixed_center_finite_raw_tail_pack =
    slp_signed_tail_merge \<circ>
      (\<lambda>x.
        (slp_qone_inner_active_pack (fst x),
          slp_point_family_pair_signed_tail_pack (snd x)))"

definition slp_mixed_center_finite_raw_pack ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow>
      real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool)"
where
  "slp_mixed_center_finite_raw_pack =
    slp_signed_product_to_cartesian \<circ>
      (\<lambda>coordinates.
        (slp_complex_coordinate_pack
            (slp_point_as_complex (fst coordinates)),
          slp_mixed_center_finite_raw_tail_pack (snd coordinates)))"

lemma slp_mixed_center_finite_raw_tail_pack_apply:
  fixes left ::
    "((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point"
    and right :: "(slp_point^'j::finite) \<times> (slp_point^'j)"
  shows
    "slp_mixed_center_finite_raw_tail_pack (left, right) $ (k, b) =
      (case k of
        Inl i \<Rightarrow> slp_qone_inner_active_pack left $ (i, b)
      | Inr j \<Rightarrow>
          slp_point_family_pair_signed_tail_pack right $ (j, b))"
  by (cases k)
    (simp_all only: slp_mixed_center_finite_raw_tail_pack_def
      slp_signed_tail_merge_def slp_cartesian_sum_merge_def
      slp_signed_tail_reindex_def comp_apply vec_lambda_beta
      fst_conv snd_conv prod.sel case_prod_beta sum.case)

lemma slp_mixed_center_finite_raw_pack_apply:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_raw_pack coordinates $ (k, b) =
      (case k of
        Inl _ \<Rightarrow> slp_complex_coordinate_pack
          (slp_point_as_complex (fst coordinates)) $ b
      | Inr tail \<Rightarrow>
          slp_mixed_center_finite_raw_tail_pack (snd coordinates) $ (tail, b))"
  by (cases k)
    (simp_all only: slp_mixed_center_finite_raw_pack_def
      slp_signed_product_to_cartesian_def comp_apply vec_lambda_beta
      prod.sel sum.case)

definition slp_mixed_center_finite_active_reindex ::
    "(unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j))) \<Rightarrow>
      unit + ((unit + ('i + 'i)) + ('j + 'j))"
where
  "slp_mixed_center_finite_active_reindex k =
    (case k of
      Inl u \<Rightarrow> Inl u
    | Inr tail \<Rightarrow> (case tail of
        Inl left \<Rightarrow> (case left of
            Inl side \<Rightarrow> Inr (Inl (Inr side))
          | Inr terminal \<Rightarrow> Inr (Inl (Inl terminal)))
      | Inr right \<Rightarrow> Inr (Inr right)))"

definition slp_mixed_center_finite_active_unreindex ::
    "unit + ((unit + ('i::finite + 'i)) + ('j::finite + 'j)) \<Rightarrow>
      unit + ((('i + 'i) + unit) + ('j + 'j))"
where
  "slp_mixed_center_finite_active_unreindex k =
    (case k of
      Inl u \<Rightarrow> Inl u
    | Inr tail \<Rightarrow> (case tail of
        Inl left \<Rightarrow> (case left of
            Inl terminal \<Rightarrow> Inr (Inl (Inr terminal))
          | Inr side \<Rightarrow> Inr (Inl (Inl side)))
      | Inr right \<Rightarrow> Inr (Inr right)))"

lemma slp_mixed_center_finite_active_unreindex_reindex:
  "slp_mixed_center_finite_active_unreindex
      (slp_mixed_center_finite_active_reindex k) = k"
  by (simp add: slp_mixed_center_finite_active_reindex_def
      slp_mixed_center_finite_active_unreindex_def split: sum.splits)

lemma slp_mixed_center_finite_active_reindex_unreindex:
  "slp_mixed_center_finite_active_reindex
      (slp_mixed_center_finite_active_unreindex k) = k"
  by (simp add: slp_mixed_center_finite_active_reindex_def
      slp_mixed_center_finite_active_unreindex_def split: sum.splits)

lemma slp_mixed_center_finite_active_reindex_bij:
  "bij (slp_mixed_center_finite_active_reindex ::
    (unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j))) \<Rightarrow>
      unit + ((unit + ('i + 'i)) + ('j + 'j)))"
proof (rule bijI)
  show "inj (slp_mixed_center_finite_active_reindex ::
      (unit + ((('i + 'i) + unit) + ('j + 'j))) \<Rightarrow>
        unit + ((unit + ('i + 'i)) + ('j + 'j)))"
  proof (rule injI)
    fix x y :: "unit + ((('i + 'i) + unit) + ('j + 'j))"
    assume equal:
      "slp_mixed_center_finite_active_reindex x =
        slp_mixed_center_finite_active_reindex y"
    have "slp_mixed_center_finite_active_unreindex
          (slp_mixed_center_finite_active_reindex x) =
        slp_mixed_center_finite_active_unreindex
          (slp_mixed_center_finite_active_reindex y)"
      by (simp only: equal)
    then show "x = y"
      by (simp only: slp_mixed_center_finite_active_unreindex_reindex)
  qed
  show "surj (slp_mixed_center_finite_active_reindex ::
      (unit + ((('i + 'i) + unit) + ('j + 'j))) \<Rightarrow>
        unit + ((unit + ('i + 'i)) + ('j + 'j)))"
  proof (rule surjI[where f = slp_mixed_center_finite_active_unreindex])
    fix k :: "unit + ((unit + ('i + 'i)) + ('j + 'j))"
    show "slp_mixed_center_finite_active_reindex
        (slp_mixed_center_finite_active_unreindex k) = k"
      by (rule slp_mixed_center_finite_active_reindex_unreindex)
  qed
qed

definition slp_mixed_center_finite_active_permute ::
    "real^((unit + ((unit + ('i::finite + 'i)) + ('j::finite + 'j))) \<times> bool)
      \<Rightarrow>
      real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)"
where
  "slp_mixed_center_finite_active_permute x =
    (\<chi> kb. x $
      (slp_mixed_center_finite_active_reindex (fst kb), snd kb))"

lemma slp_mixed_center_finite_raw_tail_pack_measurable:
  "(slp_mixed_center_finite_raw_tail_pack ::
      (((((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point) \<times>
        ((slp_point^'j::finite) \<times> (slp_point^'j)))) \<Rightarrow>
        real^(((unit + ('i + 'i)) + ('j + 'j)) \<times> bool))
    \<in> measurable lborel lborel"
proof -
  let ?S =
    "((((lborel :: (slp_point^'i) measure) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
        (lborel :: slp_point measure)) \<Otimes>\<^sub>M
      ((lborel :: (slp_point^'j) measure) \<Otimes>\<^sub>M lborel))"
  have left:
    "(\<lambda>x. slp_qone_inner_active_pack (fst x))
      \<in> measurable ?S
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)"
    using measurable_compose[
      OF measurable_fst slp_qone_inner_active_pack_measurable]
    .
  have right:
    "(\<lambda>x. slp_point_family_pair_signed_tail_pack (snd x))
      \<in> measurable ?S
        (lborel :: (real^(('j + 'j) \<times> bool)) measure)"
    using measurable_compose[
      OF measurable_snd slp_point_family_pair_signed_tail_pack_measurable]
    .
  have paired:
    "(\<lambda>x.
        (slp_qone_inner_active_pack (fst x),
          slp_point_family_pair_signed_tail_pack (snd x)))
      \<in> measurable ?S
        ((lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)
          \<Otimes>\<^sub>M
        (lborel :: (real^(('j + 'j) \<times> bool)) measure))"
    by (rule measurable_Pair[OF left right])
  have composed:
    "(slp_signed_tail_merge \<circ>
        (\<lambda>x.
          (slp_qone_inner_active_pack (fst x),
            slp_point_family_pair_signed_tail_pack (snd x))))
      \<in> measurable ?S lborel"
    using measurable_compose[
      OF paired slp_signed_tail_merge_measurable]
    by (simp only: comp_def)
  show ?thesis
    using composed
    by (simp only: slp_mixed_center_finite_raw_tail_pack_def lborel_prod)
qed

theorem slp_mixed_center_finite_raw_tail_pack_distr_lborel:
  "distr lborel
      (lborel ::
        (real^(((unit + ('i::finite + 'i)) + ('j::finite + 'j)) \<times> bool))
          measure)
      slp_mixed_center_finite_raw_tail_pack =
    (lborel ::
      (real^(((unit + ('i + 'i)) + ('j + 'j)) \<times> bool)) measure)"
proof -
  let ?S =
    "((((lborel :: (slp_point^'i) measure) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
        (lborel :: slp_point measure)) \<Otimes>\<^sub>M
      ((lborel :: (slp_point^'j) measure) \<Otimes>\<^sub>M lborel))"
  let ?T =
    "(lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure) \<Otimes>\<^sub>M
      (lborel :: (real^(('j + 'j) \<times> bool)) measure)"
  let ?U =
    "lborel ::
      (real^(((unit + ('i + 'i)) + ('j + 'j)) \<times> bool)) measure"
  let ?F = "\<lambda>x.
    (slp_qone_inner_active_pack (fst x),
      slp_point_family_pair_signed_tail_pack (snd x))"
  have F_measurable: "?F \<in> measurable ?S ?T"
    by (rule measurable_Pair)
      (rule measurable_compose[
          OF measurable_fst slp_qone_inner_active_pack_measurable],
       rule measurable_compose[
          OF measurable_snd
             slp_point_family_pair_signed_tail_pack_measurable])
  have F_eq:
    "?F = (\<lambda>(left, right).
      (slp_qone_inner_active_pack left,
        slp_point_family_pair_signed_tail_pack right))"
    by (rule ext) (simp only: case_prod_beta prod.sel)
  have generic:
    "distr ?S ?T
        (\<lambda>(left, right).
          (slp_qone_inner_active_pack left,
            slp_point_family_pair_signed_tail_pack right)) = ?T"
    by (rule slp_distr_pair_map_eq[
          OF slp_qone_inner_active_pack_measurable
             slp_point_family_pair_signed_tail_pack_measurable
             slp_qone_inner_active_pack_distr_lborel
             slp_point_family_pair_signed_tail_pack_distr_lborel])
      standard
  have F_distr: "distr ?S ?T ?F = ?T"
    using generic
    by (simp only: F_eq)
  have composed:
    "distr ?S ?U (slp_signed_tail_merge \<circ> ?F) =
      distr (distr ?S ?T ?F) ?U slp_signed_tail_merge"
    by (rule distr_distr[
          OF slp_signed_tail_merge_measurable F_measurable, symmetric])
  have result:
    "distr ?S ?U (slp_signed_tail_merge \<circ> ?F) = ?U"
  proof -
    have "distr ?S ?U (slp_signed_tail_merge \<circ> ?F) =
        distr (distr ?S ?T ?F) ?U slp_signed_tail_merge"
      by (rule composed)
    also have "... = distr ?T ?U slp_signed_tail_merge"
      by (simp only: F_distr)
    also have "... = ?U"
      by (rule slp_signed_tail_merge_distr_lborel)
    finally show ?thesis .
  qed
  show ?thesis
    using result
    by (simp only: slp_mixed_center_finite_raw_tail_pack_def lborel_prod)
qed

lemma slp_mixed_center_finite_raw_pack_measurable:
  "(slp_mixed_center_finite_raw_pack ::
      ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow>
        real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool))
    \<in> measurable lborel lborel"
proof -
  let ?S =
    "(lborel :: slp_point measure) \<Otimes>\<^sub>M
      (lborel ::
        (((((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
          ((slp_point^'j) \<times> (slp_point^'j)))) measure)"
  have root:
    "(\<lambda>coordinates.
        slp_complex_coordinate_pack
          (slp_point_as_complex (fst coordinates)))
      \<in> measurable ?S (lborel :: (real^bool) measure)"
    using measurable_compose[OF measurable_fst slp_point_boolean_map_measurable]
    .
  have tail:
    "(\<lambda>coordinates.
        slp_mixed_center_finite_raw_tail_pack (snd coordinates))
      \<in> measurable ?S
        (lborel ::
          (real^(((unit + ('i + 'i)) + ('j + 'j)) \<times> bool)) measure)"
    using measurable_compose[
      OF measurable_snd slp_mixed_center_finite_raw_tail_pack_measurable]
    .
  have paired:
    "(\<lambda>coordinates.
        (slp_complex_coordinate_pack
            (slp_point_as_complex (fst coordinates)),
          slp_mixed_center_finite_raw_tail_pack (snd coordinates)))
      \<in> measurable ?S (lborel \<Otimes>\<^sub>M lborel)"
    by (rule measurable_Pair[OF root tail])
  have merge_measurable:
    "(slp_signed_product_to_cartesian ::
        ((real^bool) \<times>
          (real^(((unit + ('i + 'i)) + ('j + 'j)) \<times> bool))) \<Rightarrow>
        real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool))
      \<in> measurable (lborel \<Otimes>\<^sub>M lborel) lborel"
    using slp_signed_product_to_cartesian_measurable[
      where 'i = "(unit + ('i + 'i)) + ('j + 'j)"]
    by (simp only: lborel_prod)
  have composed:
    "(slp_signed_product_to_cartesian \<circ>
        (\<lambda>coordinates.
          (slp_complex_coordinate_pack
              (slp_point_as_complex (fst coordinates)),
            slp_mixed_center_finite_raw_tail_pack (snd coordinates))))
      \<in> measurable ?S lborel"
    using measurable_compose[
      OF paired merge_measurable]
    by (simp only: comp_def)
  show ?thesis
    using composed
    by (simp only: slp_mixed_center_finite_raw_pack_def lborel_prod)
qed

theorem slp_mixed_center_finite_raw_pack_distr_lborel:
  "distr lborel
      (lborel ::
        (real^((unit + ((unit + ('i::finite + 'i)) + ('j::finite + 'j)))
          \<times> bool)) measure)
      slp_mixed_center_finite_raw_pack =
    (lborel ::
      (real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool)) measure)"
proof -
  let ?S =
    "(lborel :: slp_point measure) \<Otimes>\<^sub>M
      (lborel ::
        (((((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
          ((slp_point^'j) \<times> (slp_point^'j)))) measure)"
  let ?T =
    "(lborel :: (real^bool) measure) \<Otimes>\<^sub>M
      (lborel ::
        (real^(((unit + ('i + 'i)) + ('j + 'j)) \<times> bool)) measure)"
  let ?U =
    "lborel ::
      (real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool)) measure"
  let ?F = "\<lambda>coordinates.
    (slp_complex_coordinate_pack
        (slp_point_as_complex (fst coordinates)),
      slp_mixed_center_finite_raw_tail_pack (snd coordinates))"
  have F_measurable: "?F \<in> measurable ?S ?T"
    by (rule measurable_Pair)
      (rule measurable_compose[OF measurable_fst
          slp_point_boolean_map_measurable],
       rule measurable_compose[OF measurable_snd
          slp_mixed_center_finite_raw_tail_pack_measurable])
  have F_eq:
    "?F = (\<lambda>(root, tail).
      (slp_complex_coordinate_pack (slp_point_as_complex root),
        slp_mixed_center_finite_raw_tail_pack tail))"
    by (rule ext) (simp only: case_prod_beta prod.sel)
  have generic:
    "distr ?S ?T
        (\<lambda>(root, tail).
          (slp_complex_coordinate_pack (slp_point_as_complex root),
            slp_mixed_center_finite_raw_tail_pack tail)) = ?T"
    by (rule slp_distr_pair_map_eq[
          OF slp_point_boolean_map_measurable
             slp_mixed_center_finite_raw_tail_pack_measurable
             slp_point_boolean_distr_lborel
             slp_mixed_center_finite_raw_tail_pack_distr_lborel])
      standard
  have F_distr: "distr ?S ?T ?F = ?T"
    using generic
    by (simp only: F_eq)
  have merge_measurable:
    "(slp_signed_product_to_cartesian ::
        ((real^bool) \<times>
          (real^(((unit + ('i + 'i)) + ('j + 'j)) \<times> bool))) \<Rightarrow>
        real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool))
      \<in> measurable ?T ?U"
    using slp_signed_product_to_cartesian_measurable[
      where 'i = "(unit + ('i + 'i)) + ('j + 'j)"]
    by (simp only: lborel_prod)
  have merge_distr:
    "distr ?T ?U slp_signed_product_to_cartesian = ?U"
    using slp_signed_product_to_cartesian_distr_lborel[
      where 'i = "(unit + ('i + 'i)) + ('j + 'j)"]
    by (simp only: lborel_prod)
  have composed:
    "distr ?S ?U (slp_signed_product_to_cartesian \<circ> ?F) =
      distr (distr ?S ?T ?F) ?U slp_signed_product_to_cartesian"
    by (rule distr_distr[
          OF merge_measurable F_measurable,
          symmetric])
  have result:
    "distr ?S ?U (slp_signed_product_to_cartesian \<circ> ?F) = ?U"
  proof -
    have "distr ?S ?U (slp_signed_product_to_cartesian \<circ> ?F) =
        distr (distr ?S ?T ?F) ?U slp_signed_product_to_cartesian"
      by (rule composed)
    also have "... = distr ?T ?U slp_signed_product_to_cartesian"
      by (simp only: F_distr)
    also have "... = ?U"
      by (rule merge_distr)
    finally show ?thesis .
  qed
  show ?thesis
    using result
    by (simp only: slp_mixed_center_finite_raw_pack_def lborel_prod)
qed

lemma slp_mixed_center_finite_active_signed_reindex_bij:
  "bij (\<lambda>kb.
    (slp_mixed_center_finite_active_reindex (fst kb), snd kb) ::
      (unit + ((unit + ('i::finite + 'i)) + ('j::finite + 'j))) \<times> bool)"
  using slp_mixed_center_finite_active_reindex_bij[
    where 'i = 'i and 'j = 'j]
  unfolding bij_def inj_on_def surj_def
  by auto

lemma slp_mixed_center_finite_active_permute_measurable:
  "(slp_mixed_center_finite_active_permute ::
      real^((unit + ((unit + ('i::finite + 'i)) + ('j::finite + 'j))) \<times> bool)
        \<Rightarrow>
      real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
    \<in> measurable lborel lborel"
proof -
  have borel:
    "(slp_mixed_center_finite_active_permute ::
        real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool)
          \<Rightarrow>
        real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
      \<in> measurable borel borel"
    unfolding slp_mixed_center_finite_active_permute_def
    by (rule slp_cartesian_coordinate_reindex_measurable)
  show ?thesis
    using borel
    by (simp only: measurable_lborel1 measurable_lborel2)
qed

theorem slp_mixed_center_finite_active_permute_distr_lborel:
  "distr
      (lborel ::
        (real^((unit + ((unit + ('i::finite + 'i)) + ('j::finite + 'j)))
          \<times> bool)) measure)
      (lborel ::
        (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
          measure)
      slp_mixed_center_finite_active_permute =
    (lborel ::
      (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)) measure)"
proof -
  have reindex:
    "distr
        (lborel ::
          (real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool))
            measure)
        borel
        (\<lambda>x. \<chi> kb. x $
          (slp_mixed_center_finite_active_reindex (fst kb), snd kb)) =
      (lborel ::
        (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
          measure)"
    by (rule slp_lborel_cartesian_coordinate_reindex)
      (rule slp_mixed_center_finite_active_signed_reindex_bij)
  have target_change:
    "distr
        (lborel ::
          (real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool))
            measure)
        (lborel ::
          (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
            measure)
        slp_mixed_center_finite_active_permute =
      distr
        (lborel ::
          (real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool))
            measure)
        borel slp_mixed_center_finite_active_permute"
  proof (rule distr_cong)
    show "(lborel ::
        (real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool))
          measure) = lborel"
      by (rule refl)
    show "sets (lborel ::
        (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
          measure) = sets borel"
      by (rule sets_lborel)
    show "slp_mixed_center_finite_active_permute x =
        slp_mixed_center_finite_active_permute x"
      for x ::
        "real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool)"
      by (rule refl)
  qed
  have permuted:
    "distr
        (lborel ::
          (real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool))
            measure)
        borel slp_mixed_center_finite_active_permute =
      (lborel ::
        (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
          measure)"
    unfolding slp_mixed_center_finite_active_permute_def
    by (rule reindex)
  show ?thesis
    by (rule trans[OF target_change permuted])
qed

lemma slp_mixed_center_finite_active_pack_as_permuted_raw:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_active_pack coordinates =
      slp_mixed_center_finite_active_permute
        (slp_mixed_center_finite_raw_pack coordinates)"
  unfolding vec_eq_iff
proof
  fix kb ::
    "(unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool"
  obtain k b where kb: "kb = (k, b)"
    by (cases kb)
  have raw_tail_apply:
    "slp_mixed_center_finite_raw_tail_pack (snd coordinates) $ (tail, flag) =
      (case tail of
        Inl i \<Rightarrow>
          slp_qone_inner_active_pack (fst (snd coordinates)) $ (i, flag)
      | Inr j \<Rightarrow>
          slp_point_family_pair_signed_tail_pack (snd (snd coordinates)) $
            (j, flag))"
    for tail flag
  proof -
    have raw:
      "slp_mixed_center_finite_raw_tail_pack
          (fst (snd coordinates), snd (snd coordinates)) $ (tail, flag) =
        (case tail of
          Inl i \<Rightarrow>
            slp_qone_inner_active_pack (fst (snd coordinates)) $ (i, flag)
        | Inr j \<Rightarrow>
            slp_point_family_pair_signed_tail_pack (snd (snd coordinates)) $
              (j, flag))"
      by (rule slp_mixed_center_finite_raw_tail_pack_apply)
    show ?thesis
      using raw by (simp only: prod.collapse)
  qed
  have qone_pack:
    "slp_qone_inner_active_pack (fst (snd coordinates)) =
      slp_complex_family_pack
        (\<lambda>j. case j of
          Inl _ \<Rightarrow>
            slp_point_as_complex (snd (fst (snd coordinates)))
        | Inr (Inl i) \<Rightarrow>
            slp_point_as_complex
              (fst (fst (fst (snd coordinates))) $ i)
        | Inr (Inr i) \<Rightarrow>
            slp_point_as_complex
              (snd (fst (fst (snd coordinates))) $ i))"
  proof -
    have raw:
      "slp_qone_inner_active_pack
          ((fst (fst (fst (snd coordinates))),
              snd (fst (fst (snd coordinates)))),
            snd (fst (snd coordinates))) =
        slp_complex_family_pack
          (\<lambda>j. case j of
            Inl _ \<Rightarrow>
              slp_point_as_complex (snd (fst (snd coordinates)))
          | Inr (Inl i) \<Rightarrow>
              slp_point_as_complex
                (fst (fst (fst (snd coordinates))) $ i)
          | Inr (Inr i) \<Rightarrow>
              slp_point_as_complex
                (snd (fst (fst (snd coordinates))) $ i))"
      by (rule slp_qone_inner_active_pack_as_complex_family)
    show ?thesis
      using raw by (simp only: prod.collapse)
  qed
  have right_pack:
    "slp_point_family_pair_signed_tail_pack (snd (snd coordinates)) =
      slp_complex_family_pack
        (\<lambda>j. case j of
          Inl i \<Rightarrow>
            slp_point_as_complex (fst (snd (snd coordinates)) $ i)
        | Inr i \<Rightarrow>
            slp_point_as_complex (snd (snd (snd coordinates)) $ i))"
  proof -
    have raw:
      "slp_point_family_pair_signed_tail_pack
          (fst (snd (snd coordinates)), snd (snd (snd coordinates))) =
        slp_complex_family_pack
          (\<lambda>j. case j of
            Inl i \<Rightarrow>
              slp_point_as_complex (fst (snd (snd coordinates)) $ i)
          | Inr i \<Rightarrow>
              slp_point_as_complex (snd (snd (snd coordinates)) $ i))"
      by (rule slp_point_family_pair_signed_tail_pack_as_complex_family)
    show ?thesis
      using raw by (simp only: prod.collapse)
  qed
  show "slp_mixed_center_finite_active_pack coordinates $ kb =
      slp_mixed_center_finite_active_permute
        (slp_mixed_center_finite_raw_pack coordinates) $ kb"
  proof (cases k)
    case (Inl u)
    then show ?thesis
      by (cases b)
        (simp_all only: kb slp_mixed_center_finite_active_pack_def
          slp_mixed_center_finite_active_permute_def
          slp_mixed_center_finite_active_reindex_def
          slp_mixed_center_finite_raw_pack_apply
          slp_complex_family_pack_def slp_complex_coordinate_pack_def
          vec_lambda_beta prod.sel sum.case bool.distinct refl
          if_True if_False complex.sel)
  next
    case (Inr tail)
    note k_case = Inr
    show ?thesis
    proof (cases tail)
      case (Inl left)
      note tail_case = Inl
      show ?thesis
      proof (cases left)
        case (Inl side)
        show ?thesis
          using k_case tail_case Inl
          by (cases side; cases b)
            (simp_all only: kb slp_mixed_center_finite_active_pack_def
              slp_mixed_center_finite_active_permute_def
              slp_mixed_center_finite_active_reindex_def
              slp_mixed_center_finite_raw_pack_apply
              raw_tail_apply
              qone_pack
              slp_complex_family_pack_def
              slp_complex_coordinate_pack_def vec_lambda_beta prod.sel
              sum.case bool.distinct refl if_True if_False complex.sel)
      next
        case (Inr terminal)
        show ?thesis
          using k_case tail_case Inr
          by (cases b)
            (simp_all only: kb slp_mixed_center_finite_active_pack_def
                slp_mixed_center_finite_active_permute_def
                slp_mixed_center_finite_active_reindex_def
                slp_mixed_center_finite_raw_pack_apply
                raw_tail_apply
                qone_pack
                slp_complex_family_pack_def
                slp_complex_coordinate_pack_def vec_lambda_beta prod.sel
                sum.case bool.distinct refl if_True if_False complex.sel)
      qed
    next
      case (Inr right)
      show ?thesis
        using k_case Inr
        by (cases right; cases b)
          (simp_all only: kb slp_mixed_center_finite_active_pack_def
            slp_mixed_center_finite_active_permute_def
            slp_mixed_center_finite_active_reindex_def
            slp_mixed_center_finite_raw_pack_apply
            raw_tail_apply
            right_pack
            slp_complex_family_pack_def
            slp_complex_coordinate_pack_def vec_lambda_beta prod.sel
            sum.case bool.distinct refl if_True if_False complex.sel)
    qed
  qed
qed

lemma slp_mixed_center_finite_active_pack_measurable:
  "(slp_mixed_center_finite_active_pack ::
      ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow>
        real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
    \<in> measurable lborel lborel"
proof -
  have composed:
    "(slp_mixed_center_finite_active_permute \<circ>
        slp_mixed_center_finite_raw_pack ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow>
        real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
      \<in> measurable lborel lborel"
    using measurable_compose[
      OF slp_mixed_center_finite_raw_pack_measurable
         slp_mixed_center_finite_active_permute_measurable]
    by (simp only: comp_def)
  have pack_eq:
    "(slp_mixed_center_finite_active_pack ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow>
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)) =
      slp_mixed_center_finite_active_permute \<circ>
        slp_mixed_center_finite_raw_pack"
    by (rule ext)
      (simp only: comp_apply
        slp_mixed_center_finite_active_pack_as_permuted_raw)
  show ?thesis
    using composed
    by (simp only: pack_eq)
qed

theorem slp_mixed_center_finite_active_pack_distr_lborel:
  "distr lborel
      (lborel ::
        (real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
          \<times> bool)) measure)
      slp_mixed_center_finite_active_pack =
    (lborel ::
      (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)) measure)"
proof -
  let ?T =
    "lborel ::
      (real^((unit + ((unit + ('i + 'i)) + ('j + 'j))) \<times> bool)) measure"
  let ?U =
    "lborel ::
      (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)) measure"
  have composed:
    "distr lborel ?U
        (slp_mixed_center_finite_active_permute \<circ>
          slp_mixed_center_finite_raw_pack) =
      distr
        (distr lborel ?T slp_mixed_center_finite_raw_pack)
        ?U slp_mixed_center_finite_active_permute"
    by (rule distr_distr[
          OF slp_mixed_center_finite_active_permute_measurable
             slp_mixed_center_finite_raw_pack_measurable,
          symmetric])
  have result:
    "distr lborel ?U
        (slp_mixed_center_finite_active_permute \<circ>
          slp_mixed_center_finite_raw_pack) = ?U"
  proof -
    have "distr lborel ?U
        (slp_mixed_center_finite_active_permute \<circ>
          slp_mixed_center_finite_raw_pack) =
      distr
        (distr lborel ?T slp_mixed_center_finite_raw_pack)
        ?U slp_mixed_center_finite_active_permute"
      by (rule composed)
    also have "... = distr ?T ?U slp_mixed_center_finite_active_permute"
      by (simp only: slp_mixed_center_finite_raw_pack_distr_lborel)
    also have "... = ?U"
      by (rule slp_mixed_center_finite_active_permute_distr_lborel)
    finally show ?thesis .
  qed
  have pack_eq:
    "(slp_mixed_center_finite_active_pack ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow>
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)) =
      slp_mixed_center_finite_active_permute \<circ>
        slp_mixed_center_finite_raw_pack"
    by (rule ext)
      (simp only: comp_apply
        slp_mixed_center_finite_active_pack_as_permuted_raw)
  show ?thesis
    using result
    by (simp only: pack_eq)
qed

end
