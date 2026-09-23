theory Inverse_Schrodinger_Lp_Integral_Affine_Output_Power_Transport
  imports
    Inverse_Schrodinger_Lp_Integral_Minkowski_Power_Pair
    Inverse_Schrodinger_Lp_Quadratic_RL_Affine
begin

section \<open>Real affine transport for output powers\<close>

lemma slp_integral_affine_output_power_transport:
  fixes weight :: "(slp_point \<times> slp_point) \<Rightarrow> real"
    and inner_density :: "slp_point \<Rightarrow> slp_point \<Rightarrow> real"
  assumes inner_power_integrable:
      "\<And>origin. integrable lborel
        (\<lambda>inner_output. inner_density origin inner_output powr a)"
    and joint_integrable:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: (slp_point \<times> slp_point) measure))
        (\<lambda>(output, pair).
          weight pair *
            inner_density (snd pair)
              (output - fst pair + snd pair) powr a)"
  shows
    "integral\<^sup>L lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>pair.
            weight pair *
              inner_density (snd pair)
                (output - fst pair + snd pair) powr a)) =
      integral\<^sup>L lborel
        (\<lambda>pair.
          weight pair *
            integral\<^sup>L lborel
              (\<lambda>inner_output.
                inner_density (snd pair) inner_output powr a))"
proof -
  let ?F = "\<lambda>output pair.
    weight pair *
      inner_density (snd pair)
        (output - fst pair + snd pair) powr a"
  have fubini:
      "integral\<^sup>L lborel
          (\<lambda>output. integral\<^sup>L lborel (\<lambda>pair. ?F output pair)) =
        integral\<^sup>L lborel
          (\<lambda>pair. integral\<^sup>L lborel (\<lambda>output. ?F output pair))"
    using lborel_pair.Fubini_integral[OF joint_integrable, symmetric]
    by simp
  have translate_power:
      "integral\<^sup>L lborel
          (\<lambda>output.
            inner_density (snd pair)
              (output - fst pair + snd pair) powr a) =
        integral\<^sup>L lborel
          (\<lambda>inner_output.
            inner_density (snd pair) inner_output powr a)"
    for pair
  proof -
    have translated:
        "integral\<^sup>L lborel
            (\<lambda>output.
              inner_density (snd pair)
                ((- fst pair + snd pair) + output) powr a) =
          integral\<^sup>L lborel
            (\<lambda>inner_output.
              inner_density (snd pair) inner_output powr a)"
      by (rule slp_lborel_integral_translate[OF
            inner_power_integrable])
    show ?thesis
      using translated by (simp add: algebra_simps)
  qed
  have factor_and_translate:
      "integral\<^sup>L lborel (\<lambda>output. ?F output pair) =
        weight pair *
          integral\<^sup>L lborel
            (\<lambda>inner_output.
              inner_density (snd pair) inner_output powr a)"
    for pair
    by (simp only: Bochner_Integration.integral_mult_right_zero
          translate_power)
  show ?thesis
    using fubini by (simp only: factor_and_translate)
qed

end
