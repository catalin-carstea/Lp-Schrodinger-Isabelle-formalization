theory Inverse_Schrodinger_Lp_Leading_Functional
  imports Inverse_Schrodinger_Lp_Center_Average_Pairing
begin

section \<open>The center-averaged leading functional\<close>

definition slp_leading_functional ::
  "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
    (slp_point \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_leading_functional tau phi Q =
    integral\<^sup>L lborel
      (\<lambda>c. phi c * slp_center_average tau Q c)"

definition slp_nested_leading_functional ::
  "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
    (slp_point \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_nested_leading_functional tau phi Q =
    of_real (tau / pi) *
      integral\<^sup>L lborel
        (\<lambda>c. phi c *
          integral\<^sup>L lborel
            (\<lambda>z. Q z * slp_center_kernel tau c z))"

lemma slp_nested_leading_functional_eq:
  "slp_nested_leading_functional tau phi Q =
    slp_leading_functional tau phi Q"
proof -
  have inner_commute:
    "integral\<^sup>L lborel
        (\<lambda>z. Q z * slp_center_kernel tau c z) =
      integral\<^sup>L lborel
        (\<lambda>z. slp_center_kernel tau c z * Q z)" for c
    by (rule Bochner_Integration.integral_cong[OF refl])
      (simp add: mult.commute)
  show ?thesis
    unfolding slp_nested_leading_functional_def
      slp_leading_functional_def slp_center_average_def
    by (simp only: inner_commute)
      (simp add: algebra_simps)
qed

theorem slp_leading_functional_transpose:
  fixes phi Q :: "slp_point \<Rightarrow> complex"
  assumes phi_integrable: "integrable lborel phi"
    and Q_integrable: "integrable lborel Q"
  shows
    "slp_leading_functional tau phi Q =
      integral\<^sup>L lborel
        (\<lambda>z. Q z * slp_center_average tau phi z)"
  unfolding slp_leading_functional_def
  by (rule slp_center_average_bilinear_transpose[
      OF phi_integrable Q_integrable])

theorem slp_leading_functional_convergence:
  fixes phi Q :: "slp_point \<Rightarrow> complex"
  assumes Q_integrable: "integrable lborel Q"
    and phi_integrable: "integrable lborel phi"
    and phi_bounded: "bounded (range phi)"
    and uniform_convergence:
      "uniform_limit UNIV
        (\<lambda>tau. slp_center_average tau phi) phi at_top"
  shows
    "((\<lambda>tau. slp_leading_functional tau phi Q)
      \<longlongrightarrow>
        integral\<^sup>L lborel (\<lambda>z. Q z * phi z)) at_top"
proof -
  have functional_identity:
    "(\<lambda>tau. slp_leading_functional tau phi Q) =
      (\<lambda>tau. integral\<^sup>L lborel
        (\<lambda>z. Q z * slp_center_average tau phi z))"
    by (rule ext)
      (rule slp_leading_functional_transpose[
        OF phi_integrable Q_integrable])
  show ?thesis
    unfolding functional_identity
    by (rule slp_center_average_pairing_convergence[
        OF Q_integrable phi_integrable phi_bounded uniform_convergence])
qed

corollary slp_nested_leading_functional_convergence:
  fixes phi Q :: "slp_point \<Rightarrow> complex"
  assumes Q_integrable: "integrable lborel Q"
    and phi_integrable: "integrable lborel phi"
    and phi_bounded: "bounded (range phi)"
    and uniform_convergence:
      "uniform_limit UNIV
        (\<lambda>tau. slp_center_average tau phi) phi at_top"
  shows
    "((\<lambda>tau. slp_nested_leading_functional tau phi Q)
      \<longlongrightarrow>
        integral\<^sup>L lborel (\<lambda>z. Q z * phi z)) at_top"
  unfolding slp_nested_leading_functional_eq
  by (rule slp_leading_functional_convergence[
      OF Q_integrable phi_integrable phi_bounded uniform_convergence])

end
