theory Inverse_Schrodinger_Lp_Mixed_Center_Density
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Fixed_One_Sided_Cancellations"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Output_Density_Measurable"
begin

section \<open>Positive mixed density at the global center\<close>

definition slp_mixed_center_density ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_mixed_center_density R cutoff left_potential right_potential
      left_terminal_weight right_terminal_weight left_order right_order
      root_weight center =
    (\<integral>\<^sup>+ root. \<integral>\<^sup>+ left_output.
      ennreal (Real_Vector_Spaces.norm (root_weight root)) *
      slp_left_positive_output_density R cutoff left_potential
        left_terminal_weight left_order root left_output *
      slp_right_positive_output_density R cutoff right_potential
        right_terminal_weight right_order root
          (center + root - left_output)
      \<partial>lborel \<partial>lborel)"

theorem slp_mixed_center_density_measurable:
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
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
  shows
    "slp_mixed_center_density R cutoff left_potential right_potential
        left_terminal_weight right_terminal_weight left_order right_order
        root_weight \<in> borel_measurable lborel"
proof -
  note [measurable] =
    slp_left_positive_output_density_joint_measurable[
      OF cutoff_measurable left_potential_measurable
        left_terminal_measurable]
    slp_right_positive_output_density_joint_measurable[
      OF cutoff_measurable right_potential_measurable
        right_terminal_measurable]
  show ?thesis
    unfolding slp_mixed_center_density_def by measurable
qed

end
