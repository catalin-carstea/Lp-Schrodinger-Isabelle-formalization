theory Inverse_Schrodinger_Lp_Fourier_L2_Selected_Realization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Hormander_Fourier_Interface_Bridge"
begin

section \<open>A selected representative-level planar L2 Fourier realization\<close>

definition slp_fourier_l2_realization ::
  "((slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> complex) \<Rightarrow> bool"
where
  "slp_fourier_l2_realization fourier_l2 \<longleftrightarrow>
    (\<forall>f. aim_complex_lp_on_plane 2 f \<longrightarrow>
      aim_complex_lp_on_plane 2 (fourier_l2 f)) \<and>
    (\<forall>f. aim_complex_lp_on_plane 2 f \<and> integrable lborel f
      \<longrightarrow> (AE xi in lborel.
        fourier_l2 f xi = slp_fourier_transform f xi)) \<and>
    (\<forall>f. aim_complex_lp_on_plane 2 f \<longrightarrow>
      integral\<^sup>L lborel (\<lambda>xi. cmod (fourier_l2 f xi) ^ 2) =
        (2 * pi) ^ 2 * integral\<^sup>L lborel (\<lambda>x. cmod (f x) ^ 2)) \<and>
    (\<forall>f. aim_complex_lp_on_plane 2 f \<longrightarrow>
      (AE x in lborel.
        fourier_l2 (fourier_l2 f) x =
          of_real ((2 * pi) ^ 2) * f (-x)))"

definition slp_fourier_l2_transform ::
  "(slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_fourier_l2_transform =
    (SOME fourier_l2. slp_fourier_l2_realization fourier_l2)"

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_fourier_l2_transform_realization:
  "slp_fourier_l2_realization slp_fourier_l2_transform"
proof -
  have realization_exists:
      "\<exists>fourier_l2. slp_fourier_l2_realization fourier_l2"
    using hormander_euclidean_l2_fourier_plancherel
    unfolding hormander_euclidean_l2_fourier_plancherel_claim_def
      slp_fourier_l2_realization_def
    by (simp only: slp_hormander_fourier_l2_on_plane_iff
        slp_hormander_fourier_l1_transform_eq)
  show ?thesis
    unfolding slp_fourier_l2_transform_def
    by (rule someI_ex[OF realization_exists])
qed

end

end
