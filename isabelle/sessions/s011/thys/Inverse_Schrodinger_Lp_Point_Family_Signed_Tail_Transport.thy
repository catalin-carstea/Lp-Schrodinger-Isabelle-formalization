theory Inverse_Schrodinger_Lp_Point_Family_Signed_Tail_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Point_Family_Pair_Transport"
begin

section \<open>Direct transport from two planar families to signed tails\<close>

definition slp_point_family_pair_signed_tail_pack ::
    "((slp_point^'i::finite) \<times> (slp_point^'i)) \<Rightarrow>
      real^(('i + 'i) \<times> bool)"
where
  "slp_point_family_pair_signed_tail_pack =
    slp_signed_tail_merge \<circ>
      (\<lambda>x.
        (slp_point_family_boolean_flat_pack (fst x),
          slp_point_family_boolean_flat_pack (snd x)))"

lemma slp_point_family_pair_flat_pack_measurable:
  "(\<lambda>x.
      (slp_point_family_boolean_flat_pack (fst x),
        slp_point_family_boolean_flat_pack (snd x)) ::
      (real^('i::finite \<times> bool)) \<times> (real^('i \<times> bool)))
    \<in> measurable
      ((lborel :: (slp_point^'i) measure) \<Otimes>\<^sub>M lborel)
      ((lborel :: (real^('i \<times> bool)) measure) \<Otimes>\<^sub>M lborel)"
proof -
  let ?M =
    "(lborel :: (slp_point^'i) measure) \<Otimes>\<^sub>M
      (lborel :: (slp_point^'i) measure)"
  have positive:
    "(\<lambda>x. slp_point_family_boolean_flat_pack (fst x))
      \<in> measurable ?M (lborel :: (real^('i \<times> bool)) measure)"
    using measurable_compose[
      OF measurable_fst slp_point_family_boolean_flat_pack_measurable] .
  have negative:
    "(\<lambda>x. slp_point_family_boolean_flat_pack (snd x))
      \<in> measurable ?M (lborel :: (real^('i \<times> bool)) measure)"
    using measurable_compose[
      OF measurable_snd slp_point_family_boolean_flat_pack_measurable] .
  show ?thesis
    by (rule measurable_Pair[OF positive negative])
qed

lemma slp_signed_tail_merge_measurable:
  "(slp_signed_tail_merge ::
      (real^('i::finite \<times> bool)) \<times> (real^('j::finite \<times> bool))
        \<Rightarrow> real^(('i + 'j) \<times> bool))
    \<in> measurable (lborel \<Otimes>\<^sub>M lborel) lborel"
proof -
  let ?R = "\<lambda>x::real^(('i \<times> bool) + ('j \<times> bool)).
    \<chi> sb. x $ slp_signed_tail_reindex sb"
  have reindex_borel: "?R \<in> measurable borel borel"
    by (rule slp_cartesian_coordinate_reindex_measurable)
  have reindex_lborel: "?R \<in> measurable lborel lborel"
    using reindex_borel
    by (simp only: measurable_lborel1 measurable_lborel2)
  have composed:
    "(\<lambda>x. ?R (slp_cartesian_sum_merge x))
      \<in> measurable (lborel \<Otimes>\<^sub>M lborel) lborel"
    using measurable_compose[
      OF slp_cartesian_sum_merge_measurable reindex_lborel] .
  show ?thesis
    using composed
    by (simp only: slp_signed_tail_merge_def comp_def)
qed

lemma slp_point_family_pair_signed_tail_pack_measurable:
  "(slp_point_family_pair_signed_tail_pack ::
      ((slp_point^'i::finite) \<times> (slp_point^'i)) \<Rightarrow>
        real^(('i + 'i) \<times> bool))
    \<in> measurable (lborel \<Otimes>\<^sub>M lborel) lborel"
proof -
  have composed:
    "(\<lambda>x::(slp_point^'i) \<times> (slp_point^'i). slp_signed_tail_merge
        (slp_point_family_boolean_flat_pack (fst x),
          slp_point_family_boolean_flat_pack (snd x)))
      \<in> measurable (lborel \<Otimes>\<^sub>M lborel) lborel"
    using measurable_compose[
      OF slp_point_family_pair_flat_pack_measurable
         slp_signed_tail_merge_measurable] .
  show ?thesis
    using composed
    by (simp only: slp_point_family_pair_signed_tail_pack_def comp_def)
qed

theorem slp_point_family_pair_signed_tail_pack_distr_lborel:
  "distr
      ((lborel :: (slp_point^'i::finite) measure) \<Otimes>\<^sub>M
        (lborel :: (slp_point^'i) measure))
      (lborel :: (real^(('i + 'i) \<times> bool)) measure)
      slp_point_family_pair_signed_tail_pack =
    (lborel :: (real^(('i + 'i) \<times> bool)) measure)"
proof -
  let ?S =
    "(lborel :: (slp_point^'i) measure) \<Otimes>\<^sub>M
      (lborel :: (slp_point^'i) measure)"
  let ?T =
    "(lborel :: (real^('i \<times> bool)) measure) \<Otimes>\<^sub>M
      (lborel :: (real^('i \<times> bool)) measure)"
  let ?F = "\<lambda>x.
    (slp_point_family_boolean_flat_pack (fst x),
      slp_point_family_boolean_flat_pack (snd x))"
  have composed:
    "distr ?S (lborel :: (real^(('i + 'i) \<times> bool)) measure)
        (slp_signed_tail_merge \<circ> ?F) =
      distr (distr ?S ?T ?F)
        (lborel :: (real^(('i + 'i) \<times> bool)) measure)
        slp_signed_tail_merge"
    by (rule distr_distr[
          OF slp_signed_tail_merge_measurable
             slp_point_family_pair_flat_pack_measurable, symmetric])
  have F_eq:
    "?F = (\<lambda>(positive, negative).
      (slp_point_family_boolean_flat_pack positive,
        slp_point_family_boolean_flat_pack negative))"
    apply (rule ext)
    subgoal for x
      by (cases x) simp
    done
  have pair_pattern_transport:
    "distr ?S ?T
        (\<lambda>(positive, negative).
          (slp_point_family_boolean_flat_pack positive,
            slp_point_family_boolean_flat_pack negative)) = ?T"
    by (rule slp_point_family_pair_flat_pack_distr_lborel)
  have pair_transport: "distr ?S ?T ?F = ?T"
    using pair_pattern_transport
    by (simp only: F_eq)
  have merge_transport:
    "distr ?T (lborel :: (real^(('i + 'i) \<times> bool)) measure)
        slp_signed_tail_merge =
      (lborel :: (real^(('i + 'i) \<times> bool)) measure)"
    by (rule slp_signed_tail_merge_distr_lborel)
  have composite_transport:
    "distr ?S (lborel :: (real^(('i + 'i) \<times> bool)) measure)
        (slp_signed_tail_merge \<circ> ?F) =
      (lborel :: (real^(('i + 'i) \<times> bool)) measure)"
  proof -
    have "distr ?S (lborel :: (real^(('i + 'i) \<times> bool)) measure)
        (slp_signed_tail_merge \<circ> ?F) =
      distr (distr ?S ?T ?F)
        (lborel :: (real^(('i + 'i) \<times> bool)) measure)
        slp_signed_tail_merge"
      by (rule composed)
    also have "... = distr ?T
        (lborel :: (real^(('i + 'i) \<times> bool)) measure)
        slp_signed_tail_merge"
      by (simp only: pair_transport)
    also have "... =
        (lborel :: (real^(('i + 'i) \<times> bool)) measure)"
      by (rule merge_transport)
    finally show ?thesis .
  qed
  show ?thesis
    using composite_transport
    by (simp only: slp_point_family_pair_signed_tail_pack_def)
qed

end
