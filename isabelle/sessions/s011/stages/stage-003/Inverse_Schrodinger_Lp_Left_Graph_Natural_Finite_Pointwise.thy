theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Finite_Pointwise
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Branch_Natural_Finite_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Coordinate_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Natural_Branch_Pair_List"
begin

section \<open>Pointwise natural-to-finite graph transport\<close>

theorem slp_left_branch_oscillatory_graph_kernel_natural_to_finite_pointwise:
  fixes branch_dummy :: "'i::finite itself"
  shows
    "slp_left_branch_oscillatory_graph_kernel_natural CARD('i) tau center
        cutoff potential terminal_value origin
        ((pos_natural, neg_natural), terminal) =
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential terminal_value origin
        (((\<chi> i::'i. pos_natural (to_nat_on UNIV i)),
          (\<chi> i::'i. neg_natural (to_nat_on UNIV i))), terminal)"
proof -
  have natural_list:
      "map (\<lambda>k.
          (slp_left_branch_natural_value CARD('i) pos_natural k,
           slp_left_branch_natural_value CARD('i) neg_natural k))
          [0..<CARD('i)] =
        map (\<lambda>k. (pos_natural k, neg_natural k)) [0..<CARD('i)]"
  proof (rule map_cong)
    show "[0..<CARD('i)] = [0..<CARD('i)]"
      by (rule refl)
    fix k
    assume "k \<in> set [0..<CARD('i)]"
    then have "k < CARD('i)"
      by simp
    then show
      "(slp_left_branch_natural_value CARD('i) pos_natural k,
        slp_left_branch_natural_value CARD('i) neg_natural k) =
       (pos_natural k, neg_natural k)"
      unfolding slp_left_branch_natural_value_def
      by simp
  qed
  have pair_list:
      "slp_finite_branch_pair_list
          (\<lambda>i::'i. pos_natural (to_nat_on UNIV i))
          (\<lambda>i::'i. neg_natural (to_nat_on UNIV i)) =
        map (\<lambda>k. (pos_natural k, neg_natural k)) [0..<CARD('i)]"
    by (rule slp_finite_branch_pair_list_natural_coordinates)
  have pos_family:
      "(($) (\<chi> i::'i. pos_natural (to_nat_on UNIV i))) =
        (\<lambda>i::'i. pos_natural (to_nat_on UNIV i))"
    by (rule ext) (simp only: vec_lambda_beta)
  have neg_family:
      "(($) (\<chi> i::'i. neg_natural (to_nat_on UNIV i))) =
        (\<lambda>i::'i. neg_natural (to_nat_on UNIV i))"
    by (rule ext) (simp only: vec_lambda_beta)
  have finite_list:
      "slp_finite_branch_pair_list
          (($) (\<chi> i::'i. pos_natural (to_nat_on UNIV i)))
          (($) (\<chi> i::'i. neg_natural (to_nat_on UNIV i))) =
        map (\<lambda>k. (pos_natural k, neg_natural k)) [0..<CARD('i)]"
    apply (subst pos_family)
    apply (subst neg_family)
    apply (rule pair_list)
    done
  show ?thesis
    unfolding slp_left_branch_oscillatory_graph_kernel_natural_def
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_def
    apply (simp only: fst_conv snd_conv)
    apply (rule arg_cong[where f="\<lambda>pairs.
      slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
        terminal_value pairs origin terminal"])
    apply (subst natural_list)
    apply (subst pos_family)
    apply (subst neg_family)
    apply (rule pair_list[symmetric])
    done
qed

end
