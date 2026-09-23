theory AIM_Planar_Hardy_Littlewood_Sobolev_Interface
  imports "HOL-Analysis.Analysis"
begin

section \<open>Planar Hardy--Littlewood--Sobolev bound\<close>

type_synonym aim_planar_point = "real ^ 2"
type_synonym aim_planar_field = "aim_planar_point \<Rightarrow> complex"

definition aim_point_as_complex :: "aim_planar_point \<Rightarrow> complex" where
  "aim_point_as_complex x = Complex (x $ 0) (x $ 1)"

definition aim_complex_lp_on_plane ::
  "real \<Rightarrow> aim_planar_field \<Rightarrow> bool"
where
  "aim_complex_lp_on_plane p f \<longleftrightarrow>
    f \<in> borel_measurable lborel \<and>
    integrable lborel (\<lambda>x. norm (f x) powr p)"

definition aim_complex_lp_norm ::
  "real \<Rightarrow> aim_planar_field \<Rightarrow> real"
where
  "aim_complex_lp_norm p f =
    (integral\<^sup>L lborel (\<lambda>x. norm (f x) powr p)) powr (1 / p)"

definition aim_hls_target_exponent :: "real \<Rightarrow> real" where
  "aim_hls_target_exponent p = 2 * p / (2 - p)"

definition aim_planar_cauchy_integrand ::
  "aim_planar_field \<Rightarrow> aim_planar_point \<Rightarrow>
    aim_planar_point \<Rightarrow> complex"
where
  "aim_planar_cauchy_integrand f z y =
    f y * inverse (aim_point_as_complex z - aim_point_as_complex y)"

definition aim_planar_cauchy_transform ::
  "aim_planar_field \<Rightarrow> aim_planar_field"
where
  "aim_planar_cauchy_transform f z =
    inverse (of_real pi :: complex) *
      integral\<^sup>L lborel (aim_planar_cauchy_integrand f z)"

definition aim_planar_hls_cauchy_claim :: bool where
  "aim_planar_hls_cauchy_claim \<longleftrightarrow>
    (\<exists>C::real. 0 < C \<and>
      (\<forall>p f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
        \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (aim_planar_cauchy_transform f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (aim_planar_cauchy_transform f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f))"

text \<open>
  This is the representative-level, explicit-norm consequence of
  Astala--Iwaniec--Martin, Theorem 4.3.8.  The integral is Isabelle's
  totalized Bochner integral; at exceptional points where the ordinary
  singular integral is not defined it therefore selects zero.  The source
  theorem identifies the resulting almost-everywhere class in the target
  Lp space, so those exceptional values do not change the claimed norm.
\<close>

locale aim_planar_hls_cauchy =
  assumes aim_planar_hls_cauchy: aim_planar_hls_cauchy_claim

end
