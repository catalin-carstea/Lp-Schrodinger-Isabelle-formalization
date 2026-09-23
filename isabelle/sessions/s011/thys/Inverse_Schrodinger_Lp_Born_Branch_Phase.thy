theory Inverse_Schrodinger_Lp_Born_Branch_Phase
  imports Inverse_Schrodinger_Lp_Born_Branch_Outputs
begin

section \<open>Finite Born-branch phase splitting\<close>

definition slp_point_quadratic_value :: "slp_point \<Rightarrow> real" where
  "slp_point_quadratic_value z =
    (z $ (0 :: 2)) ^ 2 - (z $ (1 :: 2)) ^ 2"

definition slp_branch_phase ::
    "slp_point \<Rightarrow> (slp_point \<times> slp_point) list \<Rightarrow>
      slp_point \<Rightarrow> real" where
  "slp_branch_phase center pairs terminal =
    sum_list (map (\<lambda>pair.
      slp_center_phase center (fst pair) -
      slp_center_phase center (snd pair)) pairs) +
    slp_center_phase center terminal"

definition slp_left_branch_phase ::
    "slp_point \<Rightarrow> (slp_point \<times> slp_point) list \<Rightarrow>
      slp_point \<Rightarrow> real" where
  "slp_left_branch_phase center pairs terminal =
    slp_branch_phase center pairs terminal"

definition slp_right_branch_phase ::
    "slp_point \<Rightarrow> (slp_point \<times> slp_point) list \<Rightarrow>
      slp_point \<Rightarrow> real" where
  "slp_right_branch_phase center pairs terminal =
    slp_branch_phase center pairs terminal"

definition slp_branch_residual ::
    "(slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow> real" where
  "slp_branch_residual pairs terminal =
    sum_list (map (\<lambda>pair.
      slp_point_quadratic_value (fst pair) -
      slp_point_quadratic_value (snd pair)) pairs) +
    slp_point_quadratic_value terminal -
    slp_point_quadratic_value (slp_left_branch_output pairs terminal)"

definition slp_left_branch_residual ::
    "(slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow> real" where
  "slp_left_branch_residual pairs terminal =
    slp_branch_residual pairs terminal"

definition slp_right_branch_residual ::
    "(slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow> real" where
  "slp_right_branch_residual pairs terminal =
    slp_branch_residual pairs terminal"

lemma slp_center_phase_three_signed:
  "slp_center_phase center pos_point - slp_center_phase center neg_point +
      slp_center_phase center terminal =
    slp_center_phase center (pos_point - neg_point + terminal) +
      slp_point_quadratic_value pos_point -
      slp_point_quadratic_value neg_point +
      slp_point_quadratic_value terminal -
      slp_point_quadratic_value (pos_point - neg_point + terminal)"
  unfolding slp_center_phase_def slp_point_quadratic_value_def
  by (simp add: power2_eq_square algebra_simps)

lemma slp_branch_phase_split:
  "slp_branch_phase center pairs terminal =
    slp_center_phase center (slp_left_branch_output pairs terminal) +
      slp_branch_residual pairs terminal"
proof (induction pairs)
  case Nil
  then show ?case
    by (simp add: slp_branch_phase_def slp_branch_residual_def)
next
  case (Cons pair pairs)
  then show ?case
    using slp_center_phase_three_signed[of center "fst pair" "snd pair"
        "slp_left_branch_output pairs terminal"]
    by (simp add: slp_branch_phase_def slp_branch_residual_def
        slp_branch_increment_def algebra_simps)
qed

theorem slp_left_branch_phase_split:
  "slp_left_branch_phase center pairs terminal =
    slp_center_phase center (slp_left_branch_output pairs terminal) +
      slp_left_branch_residual pairs terminal"
  by (simp add: slp_left_branch_phase_def slp_left_branch_residual_def
      slp_branch_phase_split)

theorem slp_right_branch_phase_split:
  "slp_right_branch_phase center pairs terminal =
    slp_center_phase center (slp_right_branch_output pairs terminal) +
      slp_right_branch_residual pairs terminal"
  by (simp add: slp_right_branch_phase_def slp_right_branch_residual_def
      slp_left_branch_output_eq_right[symmetric] slp_branch_phase_split)

end
