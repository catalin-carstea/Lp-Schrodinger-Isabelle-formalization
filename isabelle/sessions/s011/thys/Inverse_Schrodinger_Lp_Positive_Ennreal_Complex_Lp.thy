theory Inverse_Schrodinger_Lp_Positive_Ennreal_Complex_Lp
  imports Inverse_Schrodinger_Lp_Positive_Ennreal_Lp
begin

section \<open>Complex realization of positive ennreal (L^p) data\<close>

lemma slp_positive_ennreal_lp_to_complex:
  assumes F_lp: "slp_positive_ennreal_lp_on_plane p F"
  shows
    "aim_complex_lp_on_plane p
      (\<lambda>x. of_real (enn2real (F x)) :: complex)"
proof -
  have F_measurable: "F \<in> borel_measurable lborel"
    and F_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr p)"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have complex_measurable:
      "(\<lambda>x. of_real (enn2real (F x)) :: complex)
        \<in> borel_measurable lborel"
    using F_measurable by measurable
  have complex_power_integrable:
      "integrable lborel
        (\<lambda>x. norm (of_real (enn2real (F x)) :: complex) powr p)"
    using F_power_integrable by simp
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using complex_measurable complex_power_integrable by blast
qed

end
