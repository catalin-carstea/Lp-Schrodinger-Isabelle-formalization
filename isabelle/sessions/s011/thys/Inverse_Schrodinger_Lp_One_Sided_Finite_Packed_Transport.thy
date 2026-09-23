theory Inverse_Schrodinger_Lp_One_Sided_Finite_Packed_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Qone_Finite_Packed_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Coordinate_Inverse_Measurable"
begin

section \<open>Literal finite one-sided coordinate transport\<close>

lemma slp_point_family_boolean_flat_pack_as_complex_family:
  fixes points :: "slp_point^'i::finite"
  shows "slp_point_family_boolean_flat_pack points =
    slp_complex_family_pack
      (\<lambda>i. slp_point_as_complex (points $ i))"
  unfolding vec_eq_iff
proof
  fix ib :: "'i::finite \<times> bool"
  obtain i b where ib: "ib = (i, b)"
    by (cases ib)
  show "slp_point_family_boolean_flat_pack points $ ib =
      slp_complex_family_pack
        (\<lambda>i. slp_point_as_complex (points $ i)) $ ib"
    by (cases b)
      (simp_all only: ib slp_point_family_boolean_flat_pack_def
        slp_nested_boolean_family_flatten_def
        slp_point_family_boolean_nested_pack_def
        slp_complex_family_pack_def slp_complex_coordinate_pack_def
        comp_apply vec_lambda_beta prod.sel bool.distinct refl
        if_True if_False)
qed

lemma slp_point_family_pair_signed_tail_pack_as_complex_family:
  fixes positive negative :: "slp_point^'i::finite"
  shows "slp_point_family_pair_signed_tail_pack (positive, negative) =
    slp_complex_family_pack
      (\<lambda>j. case j of
        Inl i \<Rightarrow> slp_point_as_complex (positive $ i)
      | Inr i \<Rightarrow> slp_point_as_complex (negative $ i))"
  unfolding vec_eq_iff
proof
  fix jb :: "('i::finite + 'i) \<times> bool"
  obtain j b where jb: "jb = (j, b)"
    by (cases jb)
  show "slp_point_family_pair_signed_tail_pack (positive, negative) $ jb =
      slp_complex_family_pack
        (\<lambda>j. case j of
          Inl i \<Rightarrow> slp_point_as_complex (positive $ i)
        | Inr i \<Rightarrow> slp_point_as_complex (negative $ i)) $ jb"
    by (cases j; cases b)
      (simp_all only: jb slp_point_family_pair_signed_tail_pack_def
        slp_signed_tail_merge_def slp_cartesian_sum_merge_def
        slp_signed_tail_reindex_def
        slp_point_family_boolean_flat_pack_as_complex_family
        slp_complex_family_pack_def comp_apply vec_lambda_beta
        fst_conv snd_conv prod.sel case_prod_beta sum.case if_True if_False)
qed

lemma slp_qone_inner_active_pack_as_complex_family:
  fixes positive negative :: "slp_point^'i::finite"
    and terminal :: slp_point
  shows "slp_qone_inner_active_pack ((positive, negative), terminal) =
    slp_complex_family_pack
      (\<lambda>j. case j of
        Inl _ \<Rightarrow> slp_point_as_complex terminal
      | Inr (Inl i) \<Rightarrow> slp_point_as_complex (positive $ i)
      | Inr (Inr i) \<Rightarrow> slp_point_as_complex (negative $ i))"
  unfolding vec_eq_iff
proof
  fix jb :: "(unit + ('i::finite + 'i)) \<times> bool"
  obtain j b where jb: "jb = (j, b)"
    by (cases jb)
  have tails:
    "slp_point_family_pair_signed_tail_pack (positive, negative) =
      slp_complex_family_pack
        (\<lambda>j. case j of
          Inl i \<Rightarrow> slp_point_as_complex (positive $ i)
        | Inr i \<Rightarrow> slp_point_as_complex (negative $ i))"
    by (rule slp_point_family_pair_signed_tail_pack_as_complex_family)
  show "slp_qone_inner_active_pack ((positive, negative), terminal) $ jb =
      slp_complex_family_pack
        (\<lambda>j. case j of
          Inl _ \<Rightarrow> slp_point_as_complex terminal
        | Inr (Inl i) \<Rightarrow> slp_point_as_complex (positive $ i)
        | Inr (Inr i) \<Rightarrow> slp_point_as_complex (negative $ i)) $ jb"
  proof (cases j)
    case (Inl u)
    then show ?thesis
      by (cases u; cases b)
        (simp_all only: jb slp_qone_inner_active_pack_def
          slp_qone_inner_swapped_pack_def slp_qone_active_merge_def
          slp_signed_product_to_cartesian_def slp_complex_family_pack_def
          slp_complex_coordinate_pack_def comp_apply vec_lambda_beta
          fst_conv snd_conv prod.sel case_prod_beta sum.case
          bool.distinct refl if_True if_False)
  next
    case (Inr tail)
    then show ?thesis
      by (cases tail; cases b)
        (simp_all only: jb slp_qone_inner_active_pack_def
          slp_qone_inner_swapped_pack_def slp_qone_active_merge_def
          slp_signed_product_to_cartesian_def slp_complex_family_pack_def
          comp_apply vec_lambda_beta fst_conv snd_conv prod.sel case_prod_beta
          sum.case bool.distinct refl tails if_True if_False)
  qed
qed

lemma slp_qone_finite_stage_pack_eq_one_sided:
  "(slp_qone_finite_stage_pack ::
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow>
        (real^bool) \<times> (real^((unit + ('i + 'i)) \<times> bool))) =
    slp_one_sided_finite_to_packed_coordinates"
proof (rule ext)
  fix coordinates :: "'i slp_left_branch_finite_coordinates"
  obtain root inner where coordinates: "coordinates = (root, inner)"
    by (cases coordinates) simp
  obtain tails terminal where inner: "inner = (tails, terminal)"
    by (cases inner) simp
  obtain positive negative where tails: "tails = (positive, negative)"
    by (cases tails) simp
  have active:
    "slp_qone_inner_active_pack ((positive, negative), terminal) =
      slp_complex_family_pack
        (\<lambda>j. case j of
          Inl _ \<Rightarrow> slp_point_as_complex terminal
        | Inr (Inl i) \<Rightarrow> slp_point_as_complex (positive $ i)
        | Inr (Inr i) \<Rightarrow> slp_point_as_complex (negative $ i))"
    by (rule slp_qone_inner_active_pack_as_complex_family)
  show "slp_qone_finite_stage_pack coordinates =
      slp_one_sided_finite_to_packed_coordinates coordinates"
    using active
    by (simp only: coordinates inner tails
        slp_qone_finite_stage_pack_def
        slp_one_sided_finite_to_packed_coordinates_def Let_def
        case_prod_beta fst_conv snd_conv)
qed

theorem slp_one_sided_finite_to_packed_coordinates_distr_lborel:
  "distr
      (lborel :: ('i::finite slp_left_branch_finite_coordinates) measure)
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))
      slp_one_sided_finite_to_packed_coordinates =
    (lborel :: (real^bool) measure) \<Otimes>\<^sub>M
      (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)"
  using slp_qone_finite_stage_pack_distr_lborel[where 'i = 'i]
  by (simp only: slp_qone_finite_stage_pack_eq_one_sided lborel_prod)

end
