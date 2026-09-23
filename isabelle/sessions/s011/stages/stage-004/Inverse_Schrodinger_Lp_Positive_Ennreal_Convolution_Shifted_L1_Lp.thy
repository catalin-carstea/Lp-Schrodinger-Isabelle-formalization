theory Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Shifted_L1_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Convolution_Factorization"
begin

section \<open>Shifted positive extended-real endpoint Young theorem\<close>

theorem slp_positive_ennreal_convolution_shifted_L1_Lp:
  fixes F G :: "slp_point \<Rightarrow> ennreal"
    and t conjugate_t :: real
    and shift :: slp_point
  assumes t_lower: "1 < t"
    and conjugate_lower: "1 < conjugate_t"
    and conjugate: "1 / t + 1 / conjugate_t = 1"
    and F_lp: "slp_positive_ennreal_lp_on_plane 1 F"
    and G_lp: "slp_positive_ennreal_lp_on_plane t G"
  shows shifted_convolution_lp:
    "slp_positive_ennreal_lp_on_plane t
      (slp_positive_ennreal_convolution F (\<lambda>x. G (shift + x)))"
    and shifted_convolution_power_bound:
    "integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_positive_ennreal_convolution F
              (\<lambda>x. G (shift + x)) output) powr t)
      \<le> enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel) powr t *
        integral\<^sup>L lborel (\<lambda>x. enn2real (G x) powr t)"
proof -
  note translated = slp_positive_ennreal_lp_translate[OF G_lp, of shift]
  note endpoint = slp_positive_ennreal_convolution_L1_Lp[OF
      t_lower conjugate_lower conjugate F_lp translated(1)]
  show
    "slp_positive_ennreal_lp_on_plane t
      (slp_positive_ennreal_convolution F (\<lambda>x. G (shift + x)))"
    by (rule endpoint(1))
  show
    "integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_positive_ennreal_convolution F
              (\<lambda>x. G (shift + x)) output) powr t)
      \<le> enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel) powr t *
        integral\<^sup>L lborel (\<lambda>x. enn2real (G x) powr t)"
    using endpoint(2) translated(2) by simp
qed

end
