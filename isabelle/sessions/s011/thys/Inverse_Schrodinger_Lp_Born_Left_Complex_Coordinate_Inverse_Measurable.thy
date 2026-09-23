theory Inverse_Schrodinger_Lp_Born_Left_Complex_Coordinate_Inverse_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Coordinate_Inverse"
begin

section \<open>Measurability of the finite-to-packed coordinate inverse\<close>

lemma slp_one_sided_finite_to_packed_coordinates_linear:
  "linear (slp_one_sided_finite_to_packed_coordinates ::
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow>
        (real^bool) \<times>
          (real^((unit + ('i + 'i)) \<times> bool)))"
proof (rule linearI)
  show "slp_one_sided_finite_to_packed_coordinates (x + y) =
      slp_one_sided_finite_to_packed_coordinates x +
        slp_one_sided_finite_to_packed_coordinates y"
    for x y :: "'i slp_left_branch_finite_coordinates"
  proof (rule prod_eqI)
    show "fst (slp_one_sided_finite_to_packed_coordinates (x + y)) =
        fst (slp_one_sided_finite_to_packed_coordinates x +
          slp_one_sided_finite_to_packed_coordinates y)"
      unfolding slp_one_sided_finite_to_packed_coordinates_def Let_def
        slp_complex_coordinate_pack_def slp_point_as_complex_def vec_eq_iff
      apply (rule allI)
      subgoal for b
        by (cases b) simp_all
      done
    show "snd (slp_one_sided_finite_to_packed_coordinates (x + y)) =
        snd (slp_one_sided_finite_to_packed_coordinates x +
          slp_one_sided_finite_to_packed_coordinates y)"
      unfolding slp_one_sided_finite_to_packed_coordinates_def Let_def
        slp_complex_family_pack_def slp_point_as_complex_def vec_eq_iff
      apply (rule allI)
      subgoal for jb
      proof -
        obtain j b where jb: "jb = (j, b)"
          by (cases jb)
        show ?thesis
          by (cases b; cases j)
            (simp_all add: jb fst_add snd_add snd_conv
              vector_add_component split: sum.splits)
      qed
      done
  qed
  show "slp_one_sided_finite_to_packed_coordinates (r *\<^sub>R x) =
      r *\<^sub>R slp_one_sided_finite_to_packed_coordinates x"
    for r and x :: "'i slp_left_branch_finite_coordinates"
  proof (rule prod_eqI)
    show "fst (slp_one_sided_finite_to_packed_coordinates (r *\<^sub>R x)) =
        fst (r *\<^sub>R slp_one_sided_finite_to_packed_coordinates x)"
      unfolding slp_one_sided_finite_to_packed_coordinates_def Let_def
        slp_complex_coordinate_pack_def slp_point_as_complex_def vec_eq_iff
      apply (rule allI)
      subgoal for b
        by (cases b) simp_all
      done
    show "snd (slp_one_sided_finite_to_packed_coordinates (r *\<^sub>R x)) =
        snd (r *\<^sub>R slp_one_sided_finite_to_packed_coordinates x)"
      unfolding slp_one_sided_finite_to_packed_coordinates_def Let_def
        slp_complex_family_pack_def slp_point_as_complex_def vec_eq_iff
      apply (intro allI)
      subgoal for jb
      proof -
        obtain j b where jb: "jb = (j, b)"
          by (cases jb)
        show ?thesis
          by (cases b; cases j)
            (simp_all add: jb fst_scaleR snd_scaleR snd_conv
              vector_scaleR_component split: sum.splits)
      qed
      done
  qed
qed

lemma slp_one_sided_finite_to_packed_coordinates_measurable:
  "(slp_one_sided_finite_to_packed_coordinates ::
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow>
        (real^bool) \<times>
          (real^((unit + ('i + 'i)) \<times> bool)))
    \<in> measurable lborel (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have bounded:
      "bounded_linear (slp_one_sided_finite_to_packed_coordinates ::
        'i slp_left_branch_finite_coordinates \<Rightarrow>
          (real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool)))"
    using slp_one_sided_finite_to_packed_coordinates_linear
    by (simp add: linear_conv_bounded_linear)
  have continuous:
      "continuous_on UNIV
        (slp_one_sided_finite_to_packed_coordinates ::
          'i slp_left_branch_finite_coordinates \<Rightarrow>
            (real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool)))"
    by (rule linear_continuous_on[OF bounded])
  have borel:
    "(slp_one_sided_finite_to_packed_coordinates ::
        'i slp_left_branch_finite_coordinates \<Rightarrow>
          (real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool)))
      \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF continuous])
  show ?thesis
    using borel
    by (simp only: lborel_prod measurable_lborel1 measurable_lborel2)
qed

end
