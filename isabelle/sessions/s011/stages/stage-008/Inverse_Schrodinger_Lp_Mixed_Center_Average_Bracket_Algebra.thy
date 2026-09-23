theory Inverse_Schrodinger_Lp_Mixed_Center_Average_Bracket_Algebra
  imports "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Cauchy_Difference_Global_Decay"
begin

section \<open>The exact mixed center-average bracket\<close>

definition slp_mixed_center_average_bracket ::
  "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
    (slp_point \<Rightarrow> complex) \<Rightarrow>
    (slp_point \<Rightarrow> complex) \<Rightarrow>
    slp_point \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_mixed_center_average_bracket tau phi left_terminal right_terminal
      center left_output right_output =
    left_terminal left_output * right_terminal right_output *
        slp_center_average tau phi center -
      left_terminal left_output *
        slp_center_average tau
          (\<lambda>x. phi x * right_terminal x) center -
      right_terminal right_output *
        slp_center_average tau
          (\<lambda>x. phi x * left_terminal x) center +
      slp_center_average tau
        (\<lambda>x. phi x * (left_terminal x * right_terminal x)) center"

theorem slp_mixed_center_average_bracket_decomposition:
  "slp_mixed_center_average_bracket tau phi left_terminal right_terminal
      center left_output right_output =
    phi center * (left_terminal left_output - left_terminal center) *
        (right_terminal right_output - right_terminal center) +
      left_terminal left_output * right_terminal right_output *
        (slp_center_average tau phi center - phi center) -
      left_terminal left_output *
        (slp_center_average tau
            (\<lambda>x. phi x * right_terminal x) center -
          phi center * right_terminal center) -
      right_terminal right_output *
        (slp_center_average tau
            (\<lambda>x. phi x * left_terminal x) center -
          phi center * left_terminal center) +
      (slp_center_average tau
          (\<lambda>x. phi x * (left_terminal x * right_terminal x)) center -
        phi center * (left_terminal center * right_terminal center))"
  unfolding slp_mixed_center_average_bracket_def
  by (simp add: algebra_simps)

end
