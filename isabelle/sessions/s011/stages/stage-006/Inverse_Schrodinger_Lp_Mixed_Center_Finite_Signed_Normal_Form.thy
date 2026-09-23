theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Signed_Normal_Form
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Residual"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Residual_Identity"
begin

section \<open>Combined signed normal form for a finite mixed branch\<close>

definition slp_mixed_combined_sign ::
    "(unit + (unit + ((('i::finite + 'i) + unit) +
      ('j::finite + 'j)))) \<Rightarrow> real"
where
  "slp_mixed_combined_sign k =
    (case k of
      Inl _ \<Rightarrow> 1
    | Inr tail \<Rightarrow> (case tail of
        Inl _ \<Rightarrow> -1
      | Inr branches \<Rightarrow> (case branches of
          Inl left \<Rightarrow> (case left of
              Inl side \<Rightarrow> (case side of
                  Inl _ \<Rightarrow> 1
                | Inr _ \<Rightarrow> -1)
            | Inr _ \<Rightarrow> 1)
        | Inr side \<Rightarrow> (case side of
              Inl _ \<Rightarrow> 1
            | Inr _ \<Rightarrow> -1))))"

definition slp_mixed_combined_family ::
    "complex \<Rightarrow>
      ('i::finite \<Rightarrow> complex) \<Rightarrow> ('i \<Rightarrow> complex) \<Rightarrow>
      complex \<Rightarrow>
      ('j::finite \<Rightarrow> complex) \<Rightarrow> ('j \<Rightarrow> complex) \<Rightarrow>
      complex \<Rightarrow>
      (unit + (unit + ((('i + 'i) + unit) + ('j + 'j))) \<Rightarrow> complex)"
where
  "slp_mixed_combined_family origin left_positive left_negative
      left_terminal right_positive right_negative right_terminal k =
    (case k of
      Inl _ \<Rightarrow> right_terminal
    | Inr tail \<Rightarrow> (case tail of
        Inl _ \<Rightarrow> origin
      | Inr branches \<Rightarrow> (case branches of
          Inl left \<Rightarrow> (case left of
              Inl side \<Rightarrow> (case side of
                  Inl i \<Rightarrow> left_positive i
                | Inr i \<Rightarrow> left_negative i)
            | Inr _ \<Rightarrow> left_terminal)
        | Inr side \<Rightarrow> (case side of
              Inl j \<Rightarrow> right_positive j
            | Inr j \<Rightarrow> right_negative j))))"

lemma slp_mixed_combined_sign_values:
  fixes k :: "unit + (unit + ((('i::finite + 'i) + unit) +
    ('j::finite + 'j)))"
  shows "slp_mixed_combined_sign k = -1 \<or>
    slp_mixed_combined_sign k = 1"
  by (cases k)
    (simp_all add: slp_mixed_combined_sign_def split: sum.splits)

lemma slp_mixed_combined_signed_sum:
  "(\<Sum>k\<in>(UNIV :: (unit + (unit + ((('i::finite + 'i) + unit) +
      ('j::finite + 'j)))) set). slp_mixed_combined_sign k) = 1"
  by (simp add: slp_sum_UNIV_sum_type slp_mixed_combined_sign_def)

lemma slp_mixed_combined_output_identity:
  fixes left_positive left_negative :: "'i::finite \<Rightarrow> complex"
    and right_positive right_negative :: "'j::finite \<Rightarrow> complex"
  shows
    "slp_signed_output slp_mixed_combined_sign
        (slp_mixed_combined_family origin left_positive left_negative
          left_terminal right_positive right_negative right_terminal) =
      - origin +
        (\<Sum>i\<in>UNIV. left_positive i - left_negative i) +
        left_terminal +
        (\<Sum>j\<in>UNIV. right_positive j - right_negative j) +
        right_terminal"
  unfolding slp_signed_output_def
  by (simp add: slp_sum_UNIV_sum_type_add slp_mixed_combined_sign_def
      slp_mixed_combined_family_def sum_negf sum_subtractf algebra_simps)

theorem slp_mixed_combined_residual_identity:
  fixes left_positive left_negative :: "'i::finite \<Rightarrow> complex"
    and right_positive right_negative :: "'j::finite \<Rightarrow> complex"
  shows
    "slp_signed_residual slp_mixed_combined_sign
        (slp_mixed_combined_family origin left_positive left_negative
          left_terminal right_positive right_negative right_terminal) =
      Re (-(origin ^ 2) +
        (\<Sum>i\<in>UNIV. (left_positive i) ^ 2 - (left_negative i) ^ 2) +
        left_terminal ^ 2 +
        (\<Sum>j\<in>UNIV. (right_positive j) ^ 2 - (right_negative j) ^ 2) +
        right_terminal ^ 2 -
        (- origin +
          (\<Sum>i\<in>UNIV. left_positive i - left_negative i) +
          left_terminal +
          (\<Sum>j\<in>UNIV. right_positive j - right_negative j) +
          right_terminal) ^ 2)"
proof -
  note combined_output = slp_mixed_combined_output_identity[
    where origin = origin and left_positive = left_positive
      and left_negative = left_negative and left_terminal = left_terminal
      and right_positive = right_positive
      and right_negative = right_negative and right_terminal = right_terminal]
  show ?thesis
    unfolding slp_signed_residual_def
    apply (subst combined_output)
    by (simp add: slp_sum_UNIV_sum_type_add slp_mixed_combined_sign_def
        slp_mixed_combined_family_def sum_negf sum_subtractf algebra_simps)
qed

end
