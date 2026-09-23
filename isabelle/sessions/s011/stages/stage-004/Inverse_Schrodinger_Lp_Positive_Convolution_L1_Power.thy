theory Inverse_Schrodinger_Lp_Positive_Convolution_L1_Power
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Integral_Minkowski_Power_Plane_AE"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Quadratic_RL_Affine"
begin

section \<open>Positive endpoint Young inequality in power form\<close>

lemma slp_positive_convolution_L1_power_bound:
  fixes f g :: "slp_point \<Rightarrow> real"
    and t conjugate_t :: real
  assumes t_lower: "1 < t"
    and conjugate_lower: "1 < conjugate_t"
    and conjugate: "1 / t + 1 / conjugate_t = 1"
    and f_measurable[measurable]: "f \<in> borel_measurable lborel"
    and g_measurable[measurable]: "g \<in> borel_measurable lborel"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and g_nonnegative: "\<And>x. 0 \<le> g x"
    and f_integrable: "integrable lborel f"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. g x powr t)"
  shows target_integrable:
    "integrable lborel
      (\<lambda>output.
        (integral\<^sup>L lborel (\<lambda>root. f root * g (output - root)))
          powr t)"
    and target_bound:
    "integral\<^sup>L lborel
        (\<lambda>output.
          (integral\<^sup>L lborel (\<lambda>root. f root * g (output - root)))
            powr t)
      \<le> (integral\<^sup>L lborel f) powr (t / conjugate_t) *
        ((integral\<^sup>L lborel (\<lambda>x. g x powr t)) *
          integral\<^sup>L lborel f)"
proof -
  let ?datum = "\<lambda>root output. g (output - root)"
  let ?L = "integral\<^sup>L lborel (\<lambda>x. g x powr t)"
  have datum_joint_measurable:
      "case_prod ?datum \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have datum_nonnegative: "0 \<le> ?datum root out" for root out
    by (rule g_nonnegative)
  have datum_power_integrable:
      "integrable lborel (\<lambda>output. ?datum root output powr t)"
    for root
  proof -
    have translated:
        "integrable lborel (\<lambda>output. g ((- root) + output) powr t)"
      by (rule slp_lborel_integrable_translate[OF g_power_integrable])
    show ?thesis using translated by simp
  qed
  have datum_power_exact:
      "integral\<^sup>L lborel (\<lambda>output. ?datum root output powr t) = ?L"
    for root
  proof -
    have translated:
        "integral\<^sup>L lborel (\<lambda>output. g ((- root) + output) powr t) =
          ?L"
      by (rule slp_lborel_integral_translate[OF g_power_integrable])
    show ?thesis using translated by simp
  qed
  have L_nonnegative: "0 \<le> ?L"
    by (rule integral_nonneg_AE) simp
  have source_integrable:
      "integrable lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>root. f root * ?datum root output powr t))"
    by (rule slp_weighted_source_power_bound_plane(3)[OF
          f_measurable datum_joint_measurable f_nonnegative datum_nonnegative
          f_integrable datum_power_integrable])
      (use datum_power_exact L_nonnegative in auto)
  have fiber_integrable_AE:
      "AE output in lborel. integrable lborel
        (\<lambda>root. f root * ?datum root output powr t)"
    by (rule slp_weighted_source_power_bound_plane(2)[OF
          f_measurable datum_joint_measurable f_nonnegative datum_nonnegative
          f_integrable datum_power_integrable])
      (use datum_power_exact L_nonnegative in auto)
  have source_bound:
      "integral\<^sup>L lborel
          (\<lambda>output. integral\<^sup>L lborel
            (\<lambda>root. f root * ?datum root output powr t))
        \<le> ?L * integral\<^sup>L lborel f"
    by (rule slp_weighted_source_power_bound_plane(4)[OF
          f_measurable datum_joint_measurable f_nonnegative datum_nonnegative
          f_integrable datum_power_integrable])
      (use datum_power_exact L_nonnegative in auto)
  have minkowski_integrable:
      "integrable lborel
        (\<lambda>output.
          (integral\<^sup>L lborel
            (\<lambda>root. f root * ?datum root output)) powr t)"
    by (rule slp_integral_minkowski_power_plane_AE(1)[OF
          t_lower conjugate_lower conjugate f_measurable
          datum_joint_measurable f_nonnegative datum_nonnegative f_integrable
          fiber_integrable_AE source_integrable])
  have minkowski_bound:
      "integral\<^sup>L lborel
          (\<lambda>output.
            (integral\<^sup>L lborel
              (\<lambda>root. f root * ?datum root output)) powr t)
        \<le> (integral\<^sup>L lborel f) powr (t / conjugate_t) *
          integral\<^sup>L lborel
            (\<lambda>output. integral\<^sup>L lborel
              (\<lambda>root. f root * ?datum root output powr t))"
    by (rule slp_integral_minkowski_power_plane_AE(2)[OF
          t_lower conjugate_lower conjugate f_measurable
          datum_joint_measurable f_nonnegative datum_nonnegative f_integrable
          fiber_integrable_AE source_integrable])
  have scale_nonnegative:
      "0 \<le> (integral\<^sup>L lborel f) powr (t / conjugate_t)"
    by simp
  have scaled_source:
      "(integral\<^sup>L lborel f) powr (t / conjugate_t) *
          integral\<^sup>L lborel
            (\<lambda>output. integral\<^sup>L lborel
              (\<lambda>root. f root * ?datum root output powr t))
        \<le> (integral\<^sup>L lborel f) powr (t / conjugate_t) *
          (?L * integral\<^sup>L lborel f)"
    by (rule mult_left_mono[OF source_bound scale_nonnegative])
  show "integrable lborel
      (\<lambda>output.
        (integral\<^sup>L lborel (\<lambda>root. f root * g (output - root)))
          powr t)"
    by (rule minkowski_integrable)
  show "integral\<^sup>L lborel
        (\<lambda>output.
          (integral\<^sup>L lborel (\<lambda>root. f root * g (output - root)))
            powr t)
      \<le> (integral\<^sup>L lborel f) powr (t / conjugate_t) *
        ((integral\<^sup>L lborel (\<lambda>x. g x powr t)) *
          integral\<^sup>L lborel f)"
    using minkowski_bound scaled_source by linarith
qed

end
