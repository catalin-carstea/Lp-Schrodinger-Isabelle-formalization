theory Inverse_Schrodinger_Lp_Hormander_Fourier_Interface_Bridge
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Cauchy_Terminal_Smooth_Error_Integral_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_L1"
    "Paper_ISLP_Hormander_Euclidean_L2_Fourier_Plancherel.Hormander_Euclidean_L2_Fourier_Plancherel_Interface"
begin

section \<open>Exact project bridge for the frozen planar Fourier interface\<close>

lemma slp_hormander_fourier_l2_on_plane_iff:
  "hormander_fourier_l2_on_plane f \<longleftrightarrow>
    aim_complex_lp_on_plane 2 f"
  unfolding hormander_fourier_l2_on_plane_def
    aim_complex_lp_on_plane_def
  by (simp only: powr_numeral norm_ge_zero)

lemma slp_hormander_fourier_l1_transform_eq:
  "hormander_fourier_l1_transform f = slp_fourier_transform f"
  unfolding hormander_fourier_l1_transform_def
    slp_fourier_transform_def hormander_fourier_phase_def
    slp_fourier_phase_def
  by (rule refl)

end
