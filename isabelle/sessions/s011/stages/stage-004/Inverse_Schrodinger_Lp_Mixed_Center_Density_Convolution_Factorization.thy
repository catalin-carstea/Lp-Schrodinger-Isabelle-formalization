theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Convolution_Factorization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Lp_Translate"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density"
begin

section \<open>Convolution form of each mixed center-density fiber\<close>

theorem slp_mixed_center_density_convolution_factorization:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    and right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    and left_terminal_measurable[measurable]:
      "left_terminal_weight \<in> borel_measurable lborel"
    and right_terminal_measurable[measurable]:
      "right_terminal_weight \<in> borel_measurable lborel"
  shows
    "slp_mixed_center_density R cutoff left_potential right_potential
        left_terminal_weight right_terminal_weight left_order right_order
        root_weight center =
      (\<integral>\<^sup>+ root.
        ennreal (Real_Vector_Spaces.norm (root_weight root)) *
        slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            left_terminal_weight left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              right_terminal_weight right_order root (root + offset))
          center
        \<partial>lborel)"
proof -
  note [measurable] =
    slp_left_positive_output_density_joint_measurable[
      OF cutoff_measurable left_potential_measurable
        left_terminal_measurable]
    slp_right_positive_output_density_joint_measurable[
      OF cutoff_measurable right_potential_measurable
        right_terminal_measurable]
  have fiber:
      "(\<integral>\<^sup>+ left_output.
        ennreal (Real_Vector_Spaces.norm (root_weight root)) *
        slp_left_positive_output_density R cutoff left_potential
          left_terminal_weight left_order root left_output *
        slp_right_positive_output_density R cutoff right_potential
          right_terminal_weight right_order root
          (center + root - left_output)
        \<partial>lborel) =
      ennreal (Real_Vector_Spaces.norm (root_weight root)) *
      slp_positive_ennreal_convolution
        (slp_left_positive_output_density R cutoff left_potential
          left_terminal_weight left_order root)
        (\<lambda>offset.
          slp_right_positive_output_density R cutoff right_potential
            right_terminal_weight right_order root (root + offset))
        center"
    for root :: slp_point
    unfolding slp_positive_ennreal_convolution_def
    apply (simp only: mult.assoc)
    apply (subst nn_integral_cmult)
     apply measurable
    apply (rule arg_cong[
      where f="\<lambda>value.
        ennreal (Real_Vector_Spaces.norm (root_weight root)) * value"])
    apply (rule nn_integral_cong)
    apply (simp add: algebra_simps)
    done
  show ?thesis
    unfolding slp_mixed_center_density_def
    by (rule nn_integral_cong, rule fiber)
qed

end
