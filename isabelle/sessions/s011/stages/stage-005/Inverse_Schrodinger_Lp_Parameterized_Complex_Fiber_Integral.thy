theory Inverse_Schrodinger_Lp_Parameterized_Complex_Fiber_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Complex_Kernel_Lp_Domination"
begin

section \<open>Guarded parameterized complex fiber integrals\<close>

definition slp_parameterized_complex_fiber_integral ::
    "('a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> complex) \<Rightarrow>
      'a \<Rightarrow> complex"
where
  "slp_parameterized_complex_fiber_integral integrand center =
    integral\<^sup>L lborel (integrand center)"

definition slp_parameterized_complex_absolute_fiber_mass ::
    "('a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> complex) \<Rightarrow>
      'a \<Rightarrow> ennreal"
where
  "slp_parameterized_complex_absolute_fiber_mass integrand center =
    (\<integral>\<^sup>+ fiber.
      norm_class.norm (integrand center fiber) \<partial>lborel)"

theorem slp_parameterized_complex_fiber_integral_measurable_and_bound:
  fixes integrand ::
    "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> complex"
  assumes integrand_measurable:
      "case_prod integrand \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and fiber_integrable:
      "AE center in lborel. integrable lborel (integrand center)"
  shows
    "(\<lambda>center. slp_parameterized_complex_fiber_integral integrand center)
        \<in> borel_measurable lborel"
    and
    "AE center in lborel.
      ennreal (norm_class.norm
        (slp_parameterized_complex_fiber_integral integrand center)) \<le>
      slp_parameterized_complex_absolute_fiber_mass integrand center"
proof -
  show
      "(\<lambda>center. slp_parameterized_complex_fiber_integral integrand center)
        \<in> borel_measurable lborel"
    unfolding slp_parameterized_complex_fiber_integral_def
    by (rule lborel.borel_measurable_lebesgue_integral[OF integrand_measurable])
  from fiber_integrable show
      "AE center in lborel.
        ennreal (norm_class.norm
          (slp_parameterized_complex_fiber_integral integrand center)) \<le>
        slp_parameterized_complex_absolute_fiber_mass integrand center"
  proof eventually_elim
    fix center
    assume center_integrable: "integrable lborel (integrand center)"
    show
        "ennreal (norm_class.norm
          (slp_parameterized_complex_fiber_integral integrand center)) \<le>
        slp_parameterized_complex_absolute_fiber_mass integrand center"
      unfolding slp_parameterized_complex_fiber_integral_def
        slp_parameterized_complex_absolute_fiber_mass_def
      by (rule Bochner_Integration.integral_norm_bound_ennreal[OF
            center_integrable])
  qed
qed

end
