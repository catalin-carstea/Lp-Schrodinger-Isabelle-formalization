theory Evans_Compact_Smooth_Lp_Density_Interface
  imports
    "Paper_ISLP_Hormander_Quadratic_Stationary_Phase.Hormander_Quadratic_Stationary_Phase_Interface"
begin

section \<open>Compact-smooth density in finite complex Lp\<close>

definition evans_compact_smooth_lp_density_claim ::
  "'n::finite itself \<Rightarrow> bool"
where
  "evans_compact_smooth_lp_density_claim dimension_type \<longleftrightarrow>
    (\<forall>q (F :: real^'n \<Rightarrow> complex) epsilon.
      1 \<le> q \<and>
      F \<in> borel_measurable lborel \<and>
      integrable lborel (\<lambda>x. norm (F x) powr q) \<and>
      0 < epsilon
      \<longrightarrow>
      (\<exists>u.
        hormander_compact_smooth_amplitude u \<and>
        (integral\<^sup>L lborel
          (\<lambda>x. norm (F x - u x) powr q)) powr (1 / q) < epsilon))"

text \<open>
  This is the finite-dimensional complex-valued finite-Lp density consequence
  of Evans's standard-mollifier construction and Properties of mollifiers,
  Appendix C.5, Theorem 7.  One first truncates an Lp function to a large ball
  and then mollifies.  Compact support of the mollifier preserves compact
  support up to a fixed enlargement, while local Lp convergence becomes global
  because both the truncated function and its small-scale mollifications vanish
  outside one bounded set.  The complex statement follows by using one common
  truncation radius and mollifier scale for the real and imaginary parts.

  The imported Hoermander theory supplies only the already frozen amplitude
  predicate used by the intended consumer.  Its stationary-phase locale
  assumption is not used or inherited as a premise of this density claim.
\<close>

locale evans_compact_smooth_lp_density =
  fixes dimension_type :: "'n::finite itself"
  assumes evans_compact_smooth_lp_density:
    "evans_compact_smooth_lp_density_claim dimension_type"

end
