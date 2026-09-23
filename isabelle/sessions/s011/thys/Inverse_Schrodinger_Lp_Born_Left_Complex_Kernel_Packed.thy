theory Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_Packed
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_Measurable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Passive_Root_Decay"
begin

section \<open>Packed coordinates for the exact complex left-branch kernel\<close>

definition slp_complex_as_point :: "complex \<Rightarrow> slp_point"
where
  "slp_complex_as_point z = (\<chi> k. if k = 0 then Re z else Im z)"

lemma slp_point_as_complex_complex_as_point [simp]:
  "slp_point_as_complex (slp_complex_as_point z) = z"
proof -
  have one_ne_zero: "(1::2) \<noteq> 0"
    by simp
  have coordinate_zero:
      "slp_complex_as_point z $ (0::2) = Re z"
    unfolding slp_complex_as_point_def
    apply (subst vec_lambda_beta)
    apply (subst if_P)
     apply (rule refl)
    apply (rule refl)
    done
  have coordinate_one:
      "slp_complex_as_point z $ (1::2) = Im z"
    unfolding slp_complex_as_point_def
    apply (subst vec_lambda_beta)
    apply (subst if_not_P)
     apply (rule one_ne_zero)
    apply (rule refl)
    done
  show ?thesis
    unfolding slp_point_as_complex_def
    apply (subst coordinate_zero)
    apply (subst coordinate_one)
    apply (rule complex_surj)
    done
qed

lemma slp_complex_as_point_point_as_complex [simp]:
  "slp_complex_as_point (slp_point_as_complex x) = x"
  unfolding vec_eq_iff
proof
  fix k :: 2
  have two_is_zero: "(2::2) = 0"
    by simp
  have one_ne_zero: "(1::2) \<noteq> 0"
    by simp
  have k_cases: "k = 1 \<or> k = 2"
    by (rule exhaust_2)
  from k_cases show
      "slp_complex_as_point (slp_point_as_complex x) $ k = x $ k"
  proof
    assume k: "k = 1"
    show ?thesis
      apply (simp only: k)
      unfolding slp_complex_as_point_def
      apply (subst vec_lambda_beta)
      apply (subst if_not_P)
       apply (rule one_ne_zero)
      unfolding slp_point_as_complex_def
      apply (rule complex.sel(2))
      done
  next
    assume k: "k = 2"
    show ?thesis
      apply (simp only: k)
      unfolding slp_complex_as_point_def
      apply (subst vec_lambda_beta)
      apply (subst if_P)
       apply (rule two_is_zero)
      unfolding slp_point_as_complex_def
      apply (subst complex.sel(1))
      apply (subst two_is_zero)
      apply (rule refl)
      done
  qed
qed

lemma slp_complex_as_point_linear:
  "linear slp_complex_as_point"
proof (rule linearI)
  show "slp_complex_as_point (x + y) =
      slp_complex_as_point x + slp_complex_as_point y"
    for x y :: complex
    unfolding vec_eq_iff
  proof
    fix k :: 2
    have two_is_zero: "(2::2) = 0"
      by simp
    show "slp_complex_as_point (x + y) $ k =
        (slp_complex_as_point x + slp_complex_as_point y) $ k"
      using exhaust_2[of k]
      by (auto simp: slp_complex_as_point_def two_is_zero)
  qed
  show "slp_complex_as_point (r *\<^sub>R x) =
      r *\<^sub>R slp_complex_as_point x"
    for r and x :: complex
    unfolding vec_eq_iff
  proof
    fix k :: 2
    have two_is_zero: "(2::2) = 0"
      by simp
    show "slp_complex_as_point (r *\<^sub>R x) $ k =
        (r *\<^sub>R slp_complex_as_point x) $ k"
      using exhaust_2[of k]
      by (auto simp: slp_complex_as_point_def two_is_zero)
  qed
qed

lemma slp_complex_as_point_measurable [measurable]:
  "slp_complex_as_point \<in> borel_measurable borel"
proof -
  have bounded: "bounded_linear slp_complex_as_point"
    using slp_complex_as_point_linear
    by (simp add: linear_conv_bounded_linear)
  show ?thesis
    by (rule borel_measurable_continuous_onI)
      (rule linear_continuous_on[OF bounded])
qed

lemma slp_complex_as_point_continuous_on [continuous_intros]:
  "continuous_on S slp_complex_as_point"
proof -
  have bounded: "bounded_linear slp_complex_as_point"
    using slp_complex_as_point_linear
    by (simp add: linear_conv_bounded_linear)
  show ?thesis
    by (rule continuous_on_subset[OF linear_continuous_on[OF bounded]])
      (rule subset_UNIV)
qed

definition slp_one_sided_packed_to_finite_coordinates ::
    "((real^bool) \<times>
      (real^((unit + ('i::finite + 'i)) \<times> bool))) \<Rightarrow>
      'i slp_left_branch_finite_coordinates"
where
  "slp_one_sided_packed_to_finite_coordinates root_branch =
    (let root = fst root_branch;
         branch = snd root_branch;
         y = slp_complex_family_unpack branch
     in (slp_complex_as_point (slp_complex_coordinate_unpack root),
       (((\<chi> i. slp_complex_as_point (y (Inr (Inl i)))),
         (\<chi> i. slp_complex_as_point (y (Inr (Inr i))))),
        slp_complex_as_point (y (Inl ())))))"

lemma slp_one_sided_packed_to_finite_root:
  fixes root :: "real^bool"
    and branch :: "real^((unit + ('i::finite + 'i)) \<times> bool)"
  shows "slp_point_as_complex
      (fst (slp_one_sided_packed_to_finite_coordinates (root, branch))) =
    slp_complex_coordinate_unpack root"
  by (simp only: slp_one_sided_packed_to_finite_coordinates_def Let_def
      fst_conv snd_conv slp_point_as_complex_complex_as_point)

lemma slp_one_sided_packed_to_finite_positive:
  fixes root :: "real^bool"
    and branch :: "real^((unit + ('i::finite + 'i)) \<times> bool)"
    and i :: 'i
  shows "slp_point_as_complex
      (fst (fst (snd (slp_one_sided_packed_to_finite_coordinates
        (root, branch)))) $ i) =
    slp_complex_family_unpack branch (Inr (Inl i))"
  by (simp only: slp_one_sided_packed_to_finite_coordinates_def Let_def
      fst_conv snd_conv vec_lambda_beta
      slp_point_as_complex_complex_as_point)

lemma slp_one_sided_packed_to_finite_negative:
  fixes root :: "real^bool"
    and branch :: "real^((unit + ('i::finite + 'i)) \<times> bool)"
    and i :: 'i
  shows "slp_point_as_complex
      (snd (fst (snd (slp_one_sided_packed_to_finite_coordinates
        (root, branch)))) $ i) =
    slp_complex_family_unpack branch (Inr (Inr i))"
  by (simp only: slp_one_sided_packed_to_finite_coordinates_def Let_def
      fst_conv snd_conv vec_lambda_beta
      slp_point_as_complex_complex_as_point)

lemma slp_one_sided_packed_to_finite_terminal:
  fixes root :: "real^bool"
    and branch :: "real^((unit + ('i::finite + 'i)) \<times> bool)"
  shows "slp_point_as_complex
      (snd (snd (slp_one_sided_packed_to_finite_coordinates
        (root, branch)))) =
    slp_complex_family_unpack branch (Inl ())"
  by (simp only: slp_one_sided_packed_to_finite_coordinates_def Let_def
      fst_conv snd_conv slp_point_as_complex_complex_as_point)

lemma slp_one_sided_packed_to_finite_coordinates_measurable:
  "(slp_one_sided_packed_to_finite_coordinates ::
      ((real^bool) \<times>
        (real^((unit + ('i::finite + 'i)) \<times> bool))) \<Rightarrow>
        'i slp_left_branch_finite_coordinates)
    \<in> measurable (lborel \<Otimes>\<^sub>M lborel) lborel"
proof -
  have continuous:
      "continuous_on UNIV
        (slp_one_sided_packed_to_finite_coordinates ::
          ((real^bool) \<times>
            (real^((unit + ('i::finite + 'i)) \<times> bool))) \<Rightarrow>
            'i slp_left_branch_finite_coordinates)"
  proof -
    have root_continuous:
        "continuous_on UNIV
          (\<lambda>x :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))).
            slp_complex_as_point
              (Complex (fst x $ False) (fst x $ True)))"
    proof -
      have inner: "continuous_on UNIV
          (\<lambda>x :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))).
            Complex (fst x $ False) (fst x $ True))"
        by (intro continuous_intros)
      show ?thesis
        by (rule continuous_on_compose2[OF
              slp_complex_as_point_continuous_on inner])
          (rule subset_UNIV)
    qed
    have positive_continuous:
        "\<And>i. continuous_on UNIV
          (\<lambda>x :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))).
            slp_complex_as_point
              (Complex (snd x $ (Inr (Inl i), False))
                (snd x $ (Inr (Inl i), True))))"
    proof -
      fix i
      have inner: "continuous_on UNIV
          (\<lambda>x :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))).
            Complex (snd x $ (Inr (Inl i), False))
              (snd x $ (Inr (Inl i), True)))"
        by (intro continuous_intros)
      show "continuous_on UNIV
          (\<lambda>x :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))).
            slp_complex_as_point
              (Complex (snd x $ (Inr (Inl i), False))
                (snd x $ (Inr (Inl i), True))))"
        by (rule continuous_on_compose2[OF
              slp_complex_as_point_continuous_on inner])
          (rule subset_UNIV)
    qed
    have negative_continuous:
        "\<And>i. continuous_on UNIV
          (\<lambda>x :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))).
            slp_complex_as_point
              (Complex (snd x $ (Inr (Inr i), False))
                (snd x $ (Inr (Inr i), True))))"
    proof -
      fix i
      have inner: "continuous_on UNIV
          (\<lambda>x :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))).
            Complex (snd x $ (Inr (Inr i), False))
              (snd x $ (Inr (Inr i), True)))"
        by (intro continuous_intros)
      show "continuous_on UNIV
          (\<lambda>x :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))).
            slp_complex_as_point
              (Complex (snd x $ (Inr (Inr i), False))
                (snd x $ (Inr (Inr i), True))))"
        by (rule continuous_on_compose2[OF
              slp_complex_as_point_continuous_on inner])
          (rule subset_UNIV)
    qed
    have terminal_continuous:
        "continuous_on UNIV
          (\<lambda>x :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))).
            slp_complex_as_point
              (Complex (snd x $ (Inl (), False))
                (snd x $ (Inl (), True))))"
    proof -
      have inner: "continuous_on UNIV
          (\<lambda>x :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))).
            Complex (snd x $ (Inl (), False))
              (snd x $ (Inl (), True)))"
        by (intro continuous_intros)
      show ?thesis
        by (rule continuous_on_compose2[OF
              slp_complex_as_point_continuous_on inner])
          (rule subset_UNIV)
    qed
    show ?thesis
      unfolding slp_one_sided_packed_to_finite_coordinates_def Let_def
        slp_complex_coordinate_unpack_def slp_complex_family_unpack_def
      by (intro continuous_intros root_continuous positive_continuous
          negative_continuous terminal_continuous)
  qed
  have borel:
      "(slp_one_sided_packed_to_finite_coordinates ::
          ((real^bool) \<times>
            (real^((unit + ('i::finite + 'i)) \<times> bool))) \<Rightarrow>
            'i slp_left_branch_finite_coordinates)
        \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF continuous])
  show ?thesis
    using borel
    by (simp only: lborel_prod measurable_lborel1 measurable_lborel2)
qed

definition slp_left_branch_complex_kernel_packed ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      real^bool \<Rightarrow>
      real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> complex"
where
  "slp_left_branch_complex_kernel_packed cutoff potential terminal_value
      (root_coord :: real^bool)
      (branch_coord :: real^((unit + ('i::finite + 'i)) \<times> bool)) =
    slp_left_branch_complex_kernel_joint cutoff potential terminal_value
      (slp_one_sided_packed_to_finite_coordinates
        (root_coord, branch_coord))"

theorem slp_left_branch_complex_kernel_packed_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "case_prod (slp_left_branch_complex_kernel_packed cutoff potential
        terminal_value) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have joint_measurable:
      "(slp_left_branch_complex_kernel_joint cutoff potential terminal_value ::
        'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_complex_kernel_joint_measurable)
      (rule cutoff_measurable potential_measurable
        terminal_value_measurable)+
  show ?thesis
  proof -
    have composed:
        "(\<lambda>x. slp_left_branch_complex_kernel_joint cutoff potential
            terminal_value
            (slp_one_sided_packed_to_finite_coordinates x))
          \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      using measurable_comp[OF
      slp_one_sided_packed_to_finite_coordinates_measurable
      joint_measurable]
      by (simp only: comp_def)
    have identity:
        "case_prod (slp_left_branch_complex_kernel_packed cutoff potential
            terminal_value) =
          (\<lambda>x. slp_left_branch_complex_kernel_joint cutoff potential
            terminal_value
            (slp_one_sided_packed_to_finite_coordinates x))"
    proof (rule ext)
      fix x :: "(real^bool) \<times>
        (real^((unit + ('i::finite + 'i)) \<times> bool))"
      obtain root_coord branch_coord where
          x: "x = (root_coord, branch_coord)"
        by (cases x)
      show "case_prod
          (slp_left_branch_complex_kernel_packed cutoff potential
            terminal_value) x =
          slp_left_branch_complex_kernel_joint cutoff potential terminal_value
            (slp_one_sided_packed_to_finite_coordinates x)"
        by (simp only: x case_prod_conv
            slp_left_branch_complex_kernel_packed_def)
    qed
    show ?thesis
      using composed by (simp only: identity)
  qed
qed

end
