theory AIM_Planar_Riesz_Potential_HLS_Interface
  imports
    "Paper_ISLP_AIM_Planar_Hardy_Littlewood_Sobolev.AIM_Planar_Hardy_Littlewood_Sobolev_Interface"
begin

section \<open>Positive planar Riesz-potential HLS bound\<close>

definition aim_real_lp_on_plane ::
  "real \<Rightarrow> (aim_planar_point \<Rightarrow> real) \<Rightarrow> bool"
where
  "aim_real_lp_on_plane p g \<longleftrightarrow>
    g \<in> borel_measurable lborel \<and>
    integrable lborel (\<lambda>x. abs (g x) powr p)"

definition aim_real_lp_norm ::
  "real \<Rightarrow> (aim_planar_point \<Rightarrow> real) \<Rightarrow> real"
where
  "aim_real_lp_norm p g =
    (integral\<^sup>L lborel (\<lambda>x. abs (g x) powr p)) powr (1 / p)"

definition aim_planar_riesz_integrand ::
  "aim_planar_field \<Rightarrow> aim_planar_point \<Rightarrow>
    aim_planar_point \<Rightarrow> real"
where
  "aim_planar_riesz_integrand f z y =
    norm (f y) *
      inverse (norm (aim_point_as_complex z - aim_point_as_complex y))"

definition aim_planar_riesz_potential ::
  "aim_planar_field \<Rightarrow> aim_planar_point \<Rightarrow> real"
where
  "aim_planar_riesz_potential f z =
    integral\<^sup>L lborel (aim_planar_riesz_integrand f z)"

definition aim_planar_riesz_hls_claim :: bool where
  "aim_planar_riesz_hls_claim \<longleftrightarrow>
    (\<exists>C::real. 0 < C \<and>
      (\<forall>p f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
        \<longrightarrow>
        (AE z in lborel. integrable lborel (aim_planar_riesz_integrand f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (aim_planar_riesz_potential f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (aim_planar_riesz_potential f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f))"

text \<open>
  This is the representative-level form of the positive Riesz-potential
  inequality displayed on Astala--Iwaniec--Martin printed page 110.  The
  potential has no Cauchy-transform normalization factor.  Isabelle's inverse
  and Bochner integral are totalized.  The claim records ordinary Bochner
  integrability of the positive singular integral at almost every output;
  only the remaining null exceptional set is assigned zero.
\<close>

locale aim_planar_riesz_hls =
  assumes aim_planar_riesz_hls: aim_planar_riesz_hls_claim

end
