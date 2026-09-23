theory AIM_Planar_Cauchy_Test_Left_Inverse_Interface
  imports
    "Paper_Inverse_Schrodinger_Lp_Uniqueness.Inverse_Schrodinger_Lp_Setup"
    "Paper_ISLP_AIM_Planar_Hardy_Littlewood_Sobolev.AIM_Planar_Hardy_Littlewood_Sobolev_Interface"
begin

section \<open>Compact-smooth left inverse for the planar Cauchy transform\<close>

definition aim_planar_classical_dbar ::
  "slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "aim_planar_classical_dbar phi x =
    (slp_complex_partial_derivative phi 0 x +
      \<i> * slp_complex_partial_derivative phi 1 x) / 2"

definition aim_planar_cauchy_test_left_inverse_claim :: bool
where
  "aim_planar_cauchy_test_left_inverse_claim \<longleftrightarrow>
    (\<forall>phi. slp_test_function_on UNIV phi \<longrightarrow>
      aim_planar_cauchy_transform (aim_planar_classical_dbar phi) = phi)"

text \<open>
  This is only the `C o dbar = I` half of Astala--Iwaniec--Martin formula
  (4.8), restricted exactly to compactly supported smooth complex functions.
  The derivative convention and the normalized `1/pi`, `z-tau` Cauchy
  transform are explicit.  No right-inverse, Sobolev-input, norm, endpoint,
  Beurling, or manuscript conclusion is included.
\<close>

locale aim_planar_cauchy_test_left_inverse =
  assumes aim_planar_cauchy_test_left_inverse:
    aim_planar_cauchy_test_left_inverse_claim

end
