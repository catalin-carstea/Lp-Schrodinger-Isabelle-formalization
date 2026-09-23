theory AIM_Planar_Beurling_Lp_Interface
  imports
    "Paper_ISLP_AIM_Planar_Hardy_Littlewood_Sobolev.AIM_Planar_Hardy_Littlewood_Sobolev_Interface"
begin

section \<open>The planar Beurling transform on explicit Lp representatives\<close>

definition aim_planar_beurling_truncation ::
  "aim_planar_field \<Rightarrow> real \<Rightarrow> aim_planar_point \<Rightarrow> complex"
where
  "aim_planar_beurling_truncation f epsilon z =
    - inverse (of_real pi :: complex) *
      integral\<^sup>L lborel
        (\<lambda>y. if epsilon <
              norm (aim_point_as_complex z - aim_point_as_complex y)
          then f y * inverse
            ((aim_point_as_complex z - aim_point_as_complex y)\<^sup>2)
          else 0)"

definition aim_planar_beurling_pv_exists ::
  "aim_planar_field \<Rightarrow> aim_planar_point \<Rightarrow> bool"
where
  "aim_planar_beurling_pv_exists f z \<longleftrightarrow>
    (\<exists>w::complex.
      ((\<lambda>epsilon::real.
          aim_planar_beurling_truncation f epsilon z) \<longlongrightarrow> w)
        (at_right 0))"

definition aim_planar_beurling_transform ::
  "aim_planar_field \<Rightarrow> aim_planar_field"
where
  "aim_planar_beurling_transform f z =
    (if aim_planar_beurling_pv_exists f z then
      Lim (at_right 0)
        (\<lambda>epsilon::real.
          aim_planar_beurling_truncation f epsilon z)
    else 0)"

definition aim_planar_beurling_lp_claim :: bool
where
  "aim_planar_beurling_lp_claim \<longleftrightarrow>
    (\<forall>p::real. 1 < p \<longrightarrow>
      (\<exists>S_p::real. 0 < S_p \<and>
        (\<forall>f. aim_complex_lp_on_plane p f \<longrightarrow>
          (AE z in lborel. aim_planar_beurling_pv_exists f z) \<and>
          aim_complex_lp_on_plane p (aim_planar_beurling_transform f) \<and>
          aim_complex_lp_norm p (aim_planar_beurling_transform f)
            \<le> S_p * aim_complex_lp_norm p f)))"

text \<open>
  This is the explicit-representative consequence of AIM Theorems 4.0.10 and
  4.5.3.  The principal-value limit is taken through positive truncation radii.
  At the null exceptional set where the limit fails, the formal representative
  is defined to be zero.  No sharp norm, endpoint, weighted, derivative, or
  manuscript conclusion is included.
\<close>

locale aim_planar_beurling_lp =
  assumes aim_planar_beurling_lp: aim_planar_beurling_lp_claim

end
