theory Evans_Compact_Smooth_L1_Density_Interface
  imports
    "Paper_ISLP_Hormander_Quadratic_Stationary_Phase.Hormander_Quadratic_Stationary_Phase_Interface"
begin

section \<open>Compact-smooth density in complex L1\<close>

definition evans_compact_smooth_l1_density_claim ::
  "'n::finite itself \<Rightarrow> bool"
where
  "evans_compact_smooth_l1_density_claim dimension_type \<longleftrightarrow>
    (\<forall>(F :: real^'n \<Rightarrow> complex).
      integrable lborel F \<longrightarrow>
      (\<forall>epsilon > 0.
        \<exists>u.
          hormander_compact_smooth_amplitude u \<and>
          integral\<^sup>L lborel (\<lambda>x. norm (F x - u x)) < epsilon))"

text \<open>
  This is the finite-dimensional complex-valued L1-density consequence of
  Evans's standard-mollifier construction and Properties of mollifiers,
  Appendix C.5, Theorem 7.  One first truncates an L1 function to a large
  ball and then mollifies.  Compact support of the mollifier preserves compact
  support up to a fixed enlargement, while local L1 convergence becomes global
  because both the truncated function and its small-scale mollifications vanish
  outside one bounded set.  The complex statement follows by applying the
  real result to the real and imaginary parts.

  The imported Hoermander theory supplies only the already frozen amplitude
  predicate used by the intended consumer.  Its stationary-phase locale
  assumption is not used or inherited as a premise of this density claim.
\<close>

locale evans_compact_smooth_l1_density =
  fixes dimension_type :: "'n::finite itself"
  assumes evans_compact_smooth_l1_density:
    "evans_compact_smooth_l1_density_claim dimension_type"

end
