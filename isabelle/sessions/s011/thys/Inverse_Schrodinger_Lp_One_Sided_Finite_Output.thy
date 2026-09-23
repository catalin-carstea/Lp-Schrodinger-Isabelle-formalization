theory Inverse_Schrodinger_Lp_One_Sided_Finite_Output
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Integral_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Packed"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Residual_Identity"
begin

section \<open>The finite manuscript output in packed coordinates\<close>

lemma slp_point_as_complex_add:
  "slp_point_as_complex (x + y) =
    slp_point_as_complex x + slp_point_as_complex y"
  by (rule complex_eqI)
    (simp_all only: slp_point_as_complex_def complex.sel
      vector_add_component plus_complex.sel)

lemma slp_point_as_complex_diff:
  "slp_point_as_complex (x - y) =
    slp_point_as_complex x - slp_point_as_complex y"
  by (rule complex_eqI)
    (simp_all only: slp_point_as_complex_def complex.sel
      vector_minus_component minus_complex.sel)

lemma slp_point_as_complex_zero:
  "slp_point_as_complex 0 = 0"
  by (rule complex_eqI)
    (simp_all only: slp_point_as_complex_def complex.sel
      zero_index zero_complex.sel)

lemma slp_point_as_complex_sum_list:
  "slp_point_as_complex (sum_list xs) =
    sum_list (map slp_point_as_complex xs)"
  by (induction xs)
    (simp_all only: sum_list.Nil sum_list.Cons list.map(1) list.map(2)
      slp_point_as_complex_zero slp_point_as_complex_add)

lemma slp_finite_branch_pair_summand_as_complex:
  fixes pos neg :: "slp_point^'i::finite"
  shows
    "slp_point_as_complex \<circ>
        ((\<lambda>pair. fst pair - snd pair) \<circ>
          (\<lambda>k. (pos $ from_nat_into UNIV k,
            neg $ from_nat_into UNIV k))) =
      (\<lambda>k. slp_point_as_complex
        (pos $ from_nat_into UNIV k - neg $ from_nat_into UNIV k))"
  by (rule ext)
    (simp only: comp_apply fst_conv snd_conv)

lemma slp_finite_branch_pair_list_output_as_complex:
  fixes pos neg :: "slp_point^'i::finite"
  shows
    "slp_point_as_complex
        (slp_left_branch_output
          (slp_finite_branch_pair_list (\<lambda>i. pos $ i) (\<lambda>i. neg $ i))
          terminal) =
      slp_point_as_complex terminal +
        (\<Sum>i\<in>UNIV.
          slp_point_as_complex (pos $ i) - slp_point_as_complex (neg $ i))"
  unfolding slp_left_branch_output_def slp_finite_branch_pair_list_def
    slp_branch_increment_def slp_point_as_complex_add
    slp_point_as_complex_diff slp_point_as_complex_sum_list
  apply (simp only: map_map interv_sum_list_conv_sum_set_nat set_upt
      atLeast0LessThan)
  apply (subst slp_finite_branch_pair_summand_as_complex)
  apply (subst sum.card_from_nat_into[
        where A = "UNIV :: 'i set"
          and h = "\<lambda>i. slp_point_as_complex (pos $ i - neg $ i)"])
  by (simp only: card_UNIV slp_point_as_complex_diff)

theorem slp_one_sided_finite_packed_output_point:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "slp_one_sided_packed_output_point
        (snd (slp_one_sided_finite_to_packed_coordinates coordinates)) =
      slp_left_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))"
proof -
  let ?pos = "fst (fst (snd coordinates))"
  let ?neg = "snd (fst (snd coordinates))"
  let ?terminal = "snd (snd coordinates)"
  have family_equality:
      "(\<lambda>j :: unit + ('i + 'i).
          case j of
            Inl _ \<Rightarrow> slp_point_as_complex ?terminal
          | Inr (Inl i) \<Rightarrow> slp_point_as_complex (?pos $ i)
          | Inr (Inr i) \<Rightarrow> slp_point_as_complex (?neg $ i)) =
        slp_one_sided_branch_family
          (\<lambda>i. slp_point_as_complex (?pos $ i))
          (\<lambda>i. slp_point_as_complex (?neg $ i))
          (slp_point_as_complex ?terminal)"
    unfolding slp_one_sided_branch_family_def
    by (rule ext) (simp only: sum.case split: sum.splits)
  have packed_complex:
      "slp_point_as_complex
          (slp_one_sided_packed_output_point
            (snd (slp_one_sided_finite_to_packed_coordinates coordinates))) =
        slp_point_as_complex ?terminal +
          (\<Sum>i\<in>UNIV.
            slp_point_as_complex (?pos $ i) -
              slp_point_as_complex (?neg $ i))"
    unfolding slp_one_sided_packed_output_point_def
      slp_one_sided_finite_to_packed_coordinates_def Let_def
    by (simp only: fst_conv snd_conv slp_point_as_complex_complex_as_point
        slp_complex_family_unpack_pack sum.case)
      (simp only: family_equality slp_one_sided_branch_output_identity)
  have finite_complex:
      "slp_point_as_complex
          (slp_left_branch_output
            (slp_finite_branch_pair_list (\<lambda>i. ?pos $ i)
              (\<lambda>i. ?neg $ i)) ?terminal) =
        slp_point_as_complex ?terminal +
          (\<Sum>i\<in>UNIV.
            slp_point_as_complex (?pos $ i) -
              slp_point_as_complex (?neg $ i))"
    by (rule slp_finite_branch_pair_list_output_as_complex)
  have complex_equality:
      "slp_point_as_complex
          (slp_one_sided_packed_output_point
            (snd (slp_one_sided_finite_to_packed_coordinates coordinates))) =
        slp_point_as_complex
          (slp_left_branch_output
            (slp_finite_branch_pair_list (\<lambda>i. ?pos $ i)
              (\<lambda>i. ?neg $ i)) ?terminal)"
    by (simp only: packed_complex finite_complex)
  show ?thesis
    using arg_cong[OF complex_equality, where f = slp_complex_as_point]
    by (simp only: slp_complex_as_point_point_as_complex)
qed

end
