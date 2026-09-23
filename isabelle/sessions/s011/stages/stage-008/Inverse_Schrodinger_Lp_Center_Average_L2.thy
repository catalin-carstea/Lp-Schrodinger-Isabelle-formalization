theory Inverse_Schrodinger_Lp_Center_Average_L2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Center_Error_L2"
begin

section \<open>Planar L2 membership of the undamped physical center average\<close>

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_center_average_l2_l1_l2:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes tau: "0 < tau"
    and f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
  shows "aim_complex_lp_on_plane 2 (slp_center_average tau f)"
proof -
  have error_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>c. slp_center_average tau f c - f c)"
    by (rule slp_center_average_error_l2_l1_l2[OF
          tau f_integrable f_l2])
  have sum_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>c. (slp_center_average tau f c - f c) + f c)"
    by (rule aim_complex_lp_on_plane_add[OF
          zero_less_numeral error_l2 f_l2])
  show ?thesis
    using sum_l2 by simp
qed

end

end
