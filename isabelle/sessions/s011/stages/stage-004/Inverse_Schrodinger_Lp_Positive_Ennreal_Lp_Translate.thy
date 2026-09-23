theory Inverse_Schrodinger_Lp_Positive_Ennreal_Lp_Translate
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_L1_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Block_Real_Representatives"
begin

section \<open>Translation of positive finite extended-real Lp data\<close>

lemma slp_positive_ennreal_lp_translate:
  fixes F :: "slp_point \<Rightarrow> ennreal"
    and p :: real
    and shift :: slp_point
  assumes F_lp: "slp_positive_ennreal_lp_on_plane p F"
  shows translated_lp:
      "slp_positive_ennreal_lp_on_plane p (\<lambda>x. F (shift + x))"
    and translated_power:
      "integral\<^sup>L lborel
          (\<lambda>x. enn2real (F (shift + x)) powr p) =
        integral\<^sup>L lborel (\<lambda>x. enn2real (F x) powr p)"
proof -
  have F_measurable[measurable]: "F \<in> borel_measurable lborel"
    and F_finite: "AE x in lborel. F x < top"
    and F_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr p)"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have translated_measurable:
      "(\<lambda>x. F (shift + x)) \<in> borel_measurable lborel"
    by measurable
  have finite_predicate:
      "Measurable.pred lborel (\<lambda>x. F x < top)"
    by measurable
  have translated_finite:
      "AE x in lborel. F (shift + x) < top"
    by (rule slp_AE_translate[OF finite_predicate F_finite])
  have translated_integrable:
      "integrable lborel (\<lambda>x. enn2real (F (shift + x)) powr p)"
    by (rule slp_lborel_integrable_translate[OF F_power_integrable])
  show "slp_positive_ennreal_lp_on_plane p (\<lambda>x. F (shift + x))"
    unfolding slp_positive_ennreal_lp_on_plane_def
    using translated_measurable translated_finite translated_integrable
    by blast
  show "integral\<^sup>L lborel
        (\<lambda>x. enn2real (F (shift + x)) powr p) =
      integral\<^sup>L lborel (\<lambda>x. enn2real (F x) powr p)"
    by (rule slp_lborel_integral_translate[OF F_power_integrable])
qed

end
