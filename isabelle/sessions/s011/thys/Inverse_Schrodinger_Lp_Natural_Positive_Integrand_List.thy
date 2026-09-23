theory Inverse_Schrodinger_Lp_Natural_Positive_Integrand_List
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Natural_Branch_Pair_List"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Output"
begin

section \<open>Natural-coordinate positive integrand in recursive list form\<close>

theorem slp_left_branch_positive_natural_integrand_list:
  fixes branch_dummy :: "'i::finite itself"
  shows
    "slp_left_branch_positive_kernel_joint R cutoff potential terminal_value
        ((origin, (((\<chi> i. pos_natural (to_nat_on UNIV i)),
          (\<chi> j. neg_natural (to_nat_on UNIV j))), terminal)) ::
            'i slp_left_branch_finite_coordinates) *
      ennreal (norm (output_factor
        (slp_one_sided_packed_output_point
          (snd (slp_one_sided_finite_to_packed_coordinates
            ((origin, (((\<chi> i. pos_natural (to_nat_on UNIV i)),
              (\<chi> j. neg_natural (to_nat_on UNIV j))), terminal)) ::
                'i slp_left_branch_finite_coordinates)))))) =
    slp_left_branch_positive_kernel_list R cutoff potential terminal_value
        (map (\<lambda>k. (pos_natural k, neg_natural k)) [0..<CARD('i)])
        origin terminal *
      ennreal (norm (output_factor
        (slp_left_branch_output
          (map (\<lambda>k. (pos_natural k, neg_natural k)) [0..<CARD('i)])
          terminal)))"
proof -
  have pos_family:
      "(($) (\<chi> i::'i. pos_natural (to_nat_on UNIV i))) =
        (\<lambda>i::'i. pos_natural (to_nat_on UNIV i))"
    by (rule ext) (simp only: vec_lambda_beta)
  have neg_family:
      "(($) (\<chi> i::'i. neg_natural (to_nat_on UNIV i))) =
        (\<lambda>i::'i. neg_natural (to_nat_on UNIV i))"
    by (rule ext) (simp only: vec_lambda_beta)
  have pair_list:
      "slp_finite_branch_pair_list
          (\<lambda>i::'i. pos_natural (to_nat_on UNIV i))
          (\<lambda>i::'i. neg_natural (to_nat_on UNIV i)) =
        map (\<lambda>k. (pos_natural k, neg_natural k)) [0..<CARD('i)]"
    by (rule slp_finite_branch_pair_list_natural_coordinates)
  show ?thesis
    unfolding slp_left_branch_positive_kernel_joint_def
      slp_left_branch_positive_kernel_finite_def
    apply (subst slp_one_sided_finite_packed_output_point)
    apply (simp only: fst_conv snd_conv pos_family neg_family pair_list)
    done
qed

end
