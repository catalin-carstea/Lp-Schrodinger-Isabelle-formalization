theory Inverse_Schrodinger_Lp_Qone_Inner_Active_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Product_Swap_Transport"
begin

section \<open>Inner finite QONE coordinates as the active vector\<close>

definition slp_qone_inner_component_pack ::
    "(((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow>
      (real^(('i + 'i) \<times> bool)) \<times> (real^bool)"
where
  "slp_qone_inner_component_pack =
    (\<lambda>(tails, terminal).
      (slp_point_family_pair_signed_tail_pack tails,
        slp_complex_coordinate_pack (slp_point_as_complex terminal)))"

definition slp_qone_inner_swapped_pack ::
    "(((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow>
      (real^bool) \<times> (real^(('i + 'i) \<times> bool))"
where
  "slp_qone_inner_swapped_pack =
    (\<lambda>(tails, terminal).
      (slp_complex_coordinate_pack (slp_point_as_complex terminal),
        slp_point_family_pair_signed_tail_pack tails))"

definition slp_qone_inner_active_pack ::
    "(((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow>
      real^((unit + ('i + 'i)) \<times> bool)"
where
  "slp_qone_inner_active_pack =
    slp_qone_active_merge \<circ> slp_qone_inner_swapped_pack"

lemma slp_qone_inner_component_pack_measurable:
  "(slp_qone_inner_component_pack ::
      (((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow>
        (real^(('i + 'i) \<times> bool)) \<times> (real^bool))
    \<in> measurable ((lborel \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel)
      (lborel \<Otimes>\<^sub>M lborel)"
proof -
  let ?M =
    "((lborel :: (slp_point^'i) measure) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
      (lborel :: slp_point measure)"
  have tails:
    "(\<lambda>x. slp_point_family_pair_signed_tail_pack (fst x))
      \<in> measurable ?M
        (lborel :: (real^(('i + 'i) \<times> bool)) measure)"
    using measurable_compose[
      OF measurable_fst
         slp_point_family_pair_signed_tail_pack_measurable] .
  have terminal:
    "(\<lambda>x. slp_complex_coordinate_pack
        (slp_point_as_complex (snd x)))
      \<in> measurable ?M (lborel :: (real^bool) measure)"
    using measurable_compose[OF measurable_snd slp_point_boolean_map_measurable] .
  have paired:
    "(\<lambda>x.
      (slp_point_family_pair_signed_tail_pack (fst x),
        slp_complex_coordinate_pack (slp_point_as_complex (snd x))))
      \<in> measurable ?M
        ((lborel :: (real^(('i + 'i) \<times> bool)) measure) \<Otimes>\<^sub>M
          (lborel :: (real^bool) measure))"
    by (rule measurable_Pair[OF tails terminal])
  show ?thesis
    using paired
    by (simp only: slp_qone_inner_component_pack_def measurable_split_conv)
qed

theorem slp_qone_inner_component_pack_distr_lborel:
  "distr
      (((lborel :: (slp_point^'i::finite) measure) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
      ((lborel :: (real^(('i + 'i) \<times> bool)) measure) \<Otimes>\<^sub>M
        (lborel :: (real^bool) measure))
      slp_qone_inner_component_pack =
    (lborel :: (real^(('i + 'i) \<times> bool)) measure) \<Otimes>\<^sub>M
      (lborel :: (real^bool) measure)"
proof -
  have target_sigma: "sigma_finite_measure (lborel :: (real^bool) measure)"
    by standard
  show ?thesis
    unfolding slp_qone_inner_component_pack_def
    by (rule slp_distr_pair_map_eq[
          OF slp_point_family_pair_signed_tail_pack_measurable
             slp_point_boolean_map_measurable
             slp_point_family_pair_signed_tail_pack_distr_lborel
             slp_point_boolean_distr_lborel
             target_sigma])
qed

lemma slp_qone_inner_swapped_pack_measurable:
  "(slp_qone_inner_swapped_pack ::
      (((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow>
        (real^bool) \<times> (real^(('i + 'i) \<times> bool)))
    \<in> measurable ((lborel \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel)
      (lborel \<Otimes>\<^sub>M lborel)"
proof -
  let ?swap = "\<lambda>(x::real^(('i + 'i) \<times> bool), y::real^bool). (y, x)"
  have composed:
    "(?swap \<circ> slp_qone_inner_component_pack ::
      (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow>
        (real^bool) \<times> (real^(('i + 'i) \<times> bool)))
      \<in> measurable ((lborel \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel)
        (lborel \<Otimes>\<^sub>M lborel)"
    by (rule measurable_comp[
          OF slp_qone_inner_component_pack_measurable measurable_pair_swap'])
  have pack_eq:
    "?swap \<circ> slp_qone_inner_component_pack =
      (slp_qone_inner_swapped_pack ::
        (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow>
          (real^bool) \<times> (real^(('i + 'i) \<times> bool)))"
    apply (rule ext)
    subgoal for x
      by (cases x) (simp only: slp_qone_inner_component_pack_def
          slp_qone_inner_swapped_pack_def comp_apply case_prod_beta
          prod.sel)
    done
  show ?thesis
    using composed
    by (simp only: pack_eq)
qed

theorem slp_qone_inner_swapped_pack_distr_lborel:
  "distr
      (((lborel :: (slp_point^'i::finite) measure) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^(('i + 'i) \<times> bool)) measure))
      slp_qone_inner_swapped_pack =
    (lborel :: (real^bool) measure) \<Otimes>\<^sub>M
      (lborel :: (real^(('i + 'i) \<times> bool)) measure)"
proof -
  let ?S =
    "((lborel :: (slp_point^'i) measure) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
      (lborel :: slp_point measure)"
  let ?T =
    "(lborel :: (real^(('i + 'i) \<times> bool)) measure) \<Otimes>\<^sub>M
      (lborel :: (real^bool) measure)"
  let ?U =
    "(lborel :: (real^bool) measure) \<Otimes>\<^sub>M
      (lborel :: (real^(('i + 'i) \<times> bool)) measure)"
  let ?swap = "\<lambda>(x::real^(('i + 'i) \<times> bool), y::real^bool). (y, x)"
  have composed:
    "distr ?S ?U (?swap \<circ> slp_qone_inner_component_pack) =
      distr (distr ?S ?T slp_qone_inner_component_pack) ?U ?swap"
    by (rule distr_distr[
          OF measurable_pair_swap'
             slp_qone_inner_component_pack_measurable, symmetric])
  have component:
    "distr ?S ?T slp_qone_inner_component_pack = ?T"
    by (rule slp_qone_inner_component_pack_distr_lborel)
  have swapped: "distr ?T ?U ?swap = ?U"
    by (rule slp_pair_swap_distr; standard)
  have composite_transport:
    "distr ?S ?U (?swap \<circ> slp_qone_inner_component_pack) = ?U"
  proof -
    have "distr ?S ?U (?swap \<circ> slp_qone_inner_component_pack) =
        distr (distr ?S ?T slp_qone_inner_component_pack) ?U ?swap"
      by (rule composed)
    also have "... = distr ?T ?U ?swap"
      by (simp only: component)
    also have "... = ?U"
      by (rule swapped)
    finally show ?thesis .
  qed
  have pack_eq:
    "?swap \<circ> slp_qone_inner_component_pack =
      (slp_qone_inner_swapped_pack ::
        (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow>
          (real^bool) \<times> (real^(('i + 'i) \<times> bool)))"
    apply (rule ext)
    subgoal for x
      by (cases x) (simp only: slp_qone_inner_component_pack_def
          slp_qone_inner_swapped_pack_def comp_apply case_prod_beta
          prod.sel)
    done
  show ?thesis
    using composite_transport
    by (simp only: pack_eq)
qed

lemma slp_qone_inner_active_pack_measurable:
  "(slp_qone_inner_active_pack ::
      (((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point) \<Rightarrow>
        real^((unit + ('i + 'i)) \<times> bool))
    \<in> measurable ((lborel \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel) lborel"
  unfolding slp_qone_inner_active_pack_def
  by (rule measurable_comp[
        OF slp_qone_inner_swapped_pack_measurable
           slp_qone_active_merge_measurable])

theorem slp_qone_inner_active_pack_distr_lborel:
  "distr
      (((lborel :: (slp_point^'i::finite) measure) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))
      (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)
      slp_qone_inner_active_pack =
    (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)"
proof -
  let ?S =
    "((lborel :: (slp_point^'i) measure) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
      (lborel :: slp_point measure)"
  let ?T =
    "(lborel :: (real^bool) measure) \<Otimes>\<^sub>M
      (lborel :: (real^(('i + 'i) \<times> bool)) measure)"
  let ?U = "lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure"
  have composed:
    "distr ?S ?U (slp_qone_active_merge \<circ> slp_qone_inner_swapped_pack) =
      distr (distr ?S ?T slp_qone_inner_swapped_pack) ?U
        slp_qone_active_merge"
    by (rule distr_distr[
          OF slp_qone_active_merge_measurable
             slp_qone_inner_swapped_pack_measurable, symmetric])
  have swapped:
    "distr ?S ?T slp_qone_inner_swapped_pack = ?T"
    by (rule slp_qone_inner_swapped_pack_distr_lborel)
  have merged: "distr ?T ?U slp_qone_active_merge = ?U"
    by (rule slp_qone_active_merge_distr_lborel)
  show ?thesis
  proof -
    have "distr ?S ?U
        (slp_qone_active_merge \<circ> slp_qone_inner_swapped_pack) =
      distr (distr ?S ?T slp_qone_inner_swapped_pack) ?U
        slp_qone_active_merge"
      by (rule composed)
    also have "... = distr ?T ?U slp_qone_active_merge"
      by (simp only: swapped)
    also have "... = ?U"
      by (rule merged)
    finally show ?thesis
      by (simp only: slp_qone_inner_active_pack_def)
  qed
qed

end
