theory Inverse_Schrodinger_Lp_Born_Left_Complex_Coordinate_Inverse
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Integrable"
begin

section \<open>Inverse from finite branch coordinates to the packed carrier\<close>

definition slp_complex_coordinate_pack :: "complex \<Rightarrow> real^bool"
where
  "slp_complex_coordinate_pack z =
    (\<chi> b. if b = False then Re z else Im z)"

lemma slp_complex_coordinate_unpack_pack [simp]:
  "slp_complex_coordinate_unpack (slp_complex_coordinate_pack z) = z"
  unfolding slp_complex_coordinate_unpack_def slp_complex_coordinate_pack_def
  by (simp add: complex_eq_iff)

lemma slp_complex_coordinate_pack_unpack [simp]:
  "slp_complex_coordinate_pack (slp_complex_coordinate_unpack x) = x"
  unfolding vec_eq_iff
proof
  fix b :: bool
  show "slp_complex_coordinate_pack (slp_complex_coordinate_unpack x) $ b =
      x $ b"
    by (cases b)
      (simp_all add: slp_complex_coordinate_pack_def
        slp_complex_coordinate_unpack_def)
qed

definition slp_one_sided_finite_to_packed_coordinates ::
    "'i::finite slp_left_branch_finite_coordinates \<Rightarrow>
      (real^bool) \<times>
        (real^((unit + ('i + 'i)) \<times> bool))"
where
  "slp_one_sided_finite_to_packed_coordinates coordinates =
    (let origin = fst coordinates;
         pos = fst (fst (snd coordinates));
         neg = snd (fst (snd coordinates));
         terminal = snd (snd coordinates)
     in (slp_complex_coordinate_pack (slp_point_as_complex origin),
       slp_complex_family_pack (\<lambda>j.
         case j of
           Inl _ \<Rightarrow> slp_point_as_complex terminal
         | Inr (Inl i) \<Rightarrow> slp_point_as_complex (pos $ i)
         | Inr (Inr i) \<Rightarrow> slp_point_as_complex (neg $ i))))"

lemma slp_one_sided_finite_to_packed_to_finite [simp]:
  "slp_one_sided_packed_to_finite_coordinates
      (slp_one_sided_finite_to_packed_coordinates coordinates) = coordinates"
  unfolding slp_one_sided_packed_to_finite_coordinates_def
    slp_one_sided_finite_to_packed_coordinates_def Let_def
  by (simp only: fst_conv snd_conv slp_complex_coordinate_unpack_pack
      slp_complex_family_unpack_pack sum.case
      slp_complex_as_point_point_as_complex vec_lambda_eta prod.collapse)

lemma slp_one_sided_packed_to_finite_to_packed [simp]:
  fixes root :: "real^bool"
    and branch :: "real^((unit + ('i::finite + 'i)) \<times> bool)"
  shows
    "slp_one_sided_finite_to_packed_coordinates
      (slp_one_sided_packed_to_finite_coordinates (root, branch)) =
      (root, branch)"
proof (rule prod_eqI)
  show
    "fst (slp_one_sided_finite_to_packed_coordinates
      (slp_one_sided_packed_to_finite_coordinates (root, branch))) =
      fst (root, branch)"
    unfolding slp_one_sided_finite_to_packed_coordinates_def Let_def
    by (simp only: fst_conv snd_conv
        slp_one_sided_packed_to_finite_root
        slp_complex_coordinate_pack_unpack)
  show
    "snd (slp_one_sided_finite_to_packed_coordinates
      (slp_one_sided_packed_to_finite_coordinates (root, branch))) =
      snd (root, branch)"
  proof -
    have family_identity:
      "(\<lambda>j. case j of
          Inl _ \<Rightarrow> slp_point_as_complex
            (snd (snd (slp_one_sided_packed_to_finite_coordinates
              (root, branch))))
        | Inr (Inl i) \<Rightarrow> slp_point_as_complex
            (fst (fst (snd (slp_one_sided_packed_to_finite_coordinates
              (root, branch)))) $ i)
        | Inr (Inr i) \<Rightarrow> slp_point_as_complex
            (snd (fst (snd (slp_one_sided_packed_to_finite_coordinates
              (root, branch)))) $ i)) =
        slp_complex_family_unpack branch"
    proof (rule ext)
      fix j
      show
        "(case j of
            Inl _ \<Rightarrow> slp_point_as_complex
              (snd (snd (slp_one_sided_packed_to_finite_coordinates
                (root, branch))))
          | Inr (Inl i) \<Rightarrow> slp_point_as_complex
              (fst (fst (snd (slp_one_sided_packed_to_finite_coordinates
                (root, branch)))) $ i)
          | Inr (Inr i) \<Rightarrow> slp_point_as_complex
              (snd (fst (snd (slp_one_sided_packed_to_finite_coordinates
                (root, branch)))) $ i)) =
          slp_complex_family_unpack branch j"
      proof (cases j)
        case (Inl u)
        then show ?thesis
          by (cases u)
            (simp only: sum.case
              slp_one_sided_packed_to_finite_terminal)
      next
        case (Inr tail)
        note j_eq = Inr
        show ?thesis
        proof (cases tail)
          case (Inl i)
          from j_eq Inl show ?thesis
            by (simp only: sum.case
                slp_one_sided_packed_to_finite_positive)
        next
          case (Inr i)
          from j_eq Inr show ?thesis
            by (simp only: sum.case
                slp_one_sided_packed_to_finite_negative)
        qed
      qed
    qed
    show ?thesis
      unfolding slp_one_sided_finite_to_packed_coordinates_def Let_def
      by (simp only: fst_conv snd_conv family_identity
          slp_complex_family_pack_unpack)
  qed
qed

theorem slp_one_sided_packed_to_finite_coordinates_bij:
  "bij (slp_one_sided_packed_to_finite_coordinates ::
    ((real^bool) \<times>
      (real^((unit + ('i::finite + 'i)) \<times> bool))) \<Rightarrow>
      'i slp_left_branch_finite_coordinates)"
proof (rule bijI)
  show "inj (slp_one_sided_packed_to_finite_coordinates ::
      ((real^bool) \<times>
        (real^((unit + ('i + 'i)) \<times> bool))) \<Rightarrow>
        'i slp_left_branch_finite_coordinates)"
  proof (rule injI)
    fix x y
    assume equal:
      "slp_one_sided_packed_to_finite_coordinates x =
        slp_one_sided_packed_to_finite_coordinates y"
    have inverse_equal:
      "slp_one_sided_finite_to_packed_coordinates
          (slp_one_sided_packed_to_finite_coordinates x) =
        slp_one_sided_finite_to_packed_coordinates
          (slp_one_sided_packed_to_finite_coordinates y)"
      by (simp only: equal)
    obtain x_root x_branch where x_pair: "x = (x_root, x_branch)"
      by (cases x) simp
    obtain y_root y_branch where y_pair: "y = (y_root, y_branch)"
      by (cases y) simp
    have x_inverse:
      "slp_one_sided_finite_to_packed_coordinates
          (slp_one_sided_packed_to_finite_coordinates x) = x"
      unfolding x_pair
      by (rule slp_one_sided_packed_to_finite_to_packed)
    have y_inverse:
      "slp_one_sided_finite_to_packed_coordinates
          (slp_one_sided_packed_to_finite_coordinates y) = y"
      unfolding y_pair
      by (rule slp_one_sided_packed_to_finite_to_packed)
    show "x = y"
      using x_inverse inverse_equal y_inverse by simp
  qed
  show "surj (slp_one_sided_packed_to_finite_coordinates ::
      ((real^bool) \<times>
        (real^((unit + ('i + 'i)) \<times> bool))) \<Rightarrow>
        'i slp_left_branch_finite_coordinates)"
    by (rule surjI[where f =
          slp_one_sided_finite_to_packed_coordinates])
      (rule slp_one_sided_finite_to_packed_to_finite)
qed

end
