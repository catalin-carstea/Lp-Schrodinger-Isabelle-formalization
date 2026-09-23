theory Inverse_Schrodinger_Lp_Weighted_NN_Integral
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Step_HLS
begin

section \<open>Weighted nonnegative-integral Cauchy--Schwarz estimate\<close>

lemma slp_nn_integral_weighted_cauchy_schwarz:
  fixes weight datum :: "'a \<Rightarrow> ennreal"
  assumes [measurable]:
    "weight \<in> borel_measurable M"
    "datum \<in> borel_measurable M"
  shows
    "(\<integral>\<^sup>+x. weight x * datum x \<partial>M)\<^sup>2 \<le>
      (\<integral>\<^sup>+x. weight x \<partial>M) *
      (\<integral>\<^sup>+x. weight x * datum x ^ 2 \<partial>M)"
proof -
  have datum_density:
      "datum \<in> borel_measurable (density M weight)"
    using assms by simp
  have density_mass:
      "emeasure (density M weight) (space M) =
        (\<integral>\<^sup>+x. weight x \<partial>M)"
    by (subst emeasure_density)
       (auto intro!: nn_integral_cong_AE)
  note cs = Cauchy_Schwarz_nn_integral[
    of "\<lambda>_. 1" "density M weight" datum]
  show ?thesis
    using cs datum_density assms density_mass
    by (simp add: nn_integral_density)
qed

end
