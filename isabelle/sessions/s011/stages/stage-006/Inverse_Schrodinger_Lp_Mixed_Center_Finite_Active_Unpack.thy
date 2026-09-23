theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Unpack
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Residual"
begin

section \<open>Finite coordinates from the active Cartesian carrier\<close>

definition slp_mixed_center_finite_active_unpack ::
    "real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) \<Rightarrow>
      ('i, 'j) slp_mixed_center_finite_coordinates"
where
  "slp_mixed_center_finite_active_unpack x =
    (let family = slp_complex_family_unpack x;
         value = slp_complex_as_point \<circ> family;
         left_positive =
           (\<chi> i. value (Inr (Inl (Inl (Inl i)))));
         left_negative =
           (\<chi> i. value (Inr (Inl (Inl (Inr i)))));
         left_terminal = value (Inr (Inl (Inr ())));
         right_positive =
           (\<chi> j. value (Inr (Inr (Inl j))));
         right_negative =
           (\<chi> j. value (Inr (Inr (Inr j))))
     in (value (Inl ()),
       (((left_positive, left_negative), left_terminal),
        (right_positive, right_negative))))"

theorem slp_mixed_center_finite_active_unpack_pack:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_active_unpack
        (slp_mixed_center_finite_active_pack coordinates) = coordinates"
  unfolding slp_mixed_center_finite_active_unpack_def
    slp_mixed_center_finite_active_pack_def Let_def comp_def
  by (simp only: slp_complex_family_unpack_pack sum.case
      slp_complex_as_point_point_as_complex vec_lambda_eta prod.collapse)

end
