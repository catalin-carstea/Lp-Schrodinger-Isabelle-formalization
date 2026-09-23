theory Inverse_Schrodinger_Lp_Local_L1_Integrability
  imports Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Below_Two
begin

section \<open>Ordinary local integrability on bounded planar sets\<close>

lemma slp_complex_lp_on_one_iff_set_integrable:
  "slp_complex_lp_on 1 X f \<longleftrightarrow> set_integrable lborel X f"
proof -
  let ?g = "slp_restrict_field X f"
  have restrict_eq:
    "(\<lambda>x. indicator X x *\<^sub>R f x) = ?g"
    by (rule ext) (simp add: indicator_def slp_restrict_field_def)
  show ?thesis
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
      set_integrable_def restrict_eq
    by (auto simp: integrable_norm_iff)
qed

theorem aim_complex_lp_on_plane_set_integrable_bounded:
  assumes p_at_least_one: "1 \<le> p"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and f_lp: "aim_complex_lp_on_plane p f"
  shows "set_integrable lborel X f"
proof -
  have local_p: "slp_complex_lp_on p X f"
    by (rule aim_complex_lp_on_plane_restrict)
       (use p_at_least_one X_measurable f_lp in auto)
  have local_one: "slp_complex_lp_on 1 X f"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          _ p_at_least_one X_measurable X_bounded local_p]) simp
  then show ?thesis
    using slp_complex_lp_on_one_iff_set_integrable by blast
qed

end
