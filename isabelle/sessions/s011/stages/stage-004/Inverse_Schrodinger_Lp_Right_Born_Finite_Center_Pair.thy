theory Inverse_Schrodinger_Lp_Right_Born_Finite_Center_Pair
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Primitive_Difference"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Center_Fubini"
begin

section \<open>The finite right primitive-difference center pair\<close>

theorem slp_right_branch_fixed_primitive_diff_center_pair:
  fixes branch_dummy :: "'i::finite itself"
    and tau :: real
    and center_field primitive root_weight cutoff potential ::
      "slp_point \<Rightarrow> complex"
  assumes center_integrable: "integrable lborel center_field"
    and source_integrable:
      "integrable lborel (\<lambda>u. center_field u * primitive u)"
    and primitive_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          primitive (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and unit_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "of_real tau * inverse (of_real pi) *
        (\<integral>center. center_field center *
          (\<integral>(coordinates ::
              'i slp_left_branch_finite_coordinates).
            root_weight (fst coordinates) *
              slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
                center cutoff potential
                  (\<lambda>x. primitive x - primitive center)
                (fst coordinates) (snd coordinates)
            \<partial>lborel)
          \<partial>(lborel :: slp_point measure)) =
      of_real (tau / pi) *
          (\<integral>center.
            \<integral>(coordinates ::
                'i slp_left_branch_finite_coordinates).
              slp_right_branch_finite_center_integrand tau center_field
                (slp_right_branch_complex_amplitude_finite root_weight cutoff
                  potential primitive (\<lambda>_. 1))
                (center, coordinates) \<partial>lborel \<partial>lborel) -
        of_real (tau / pi) *
          (\<integral>center.
            \<integral>(coordinates ::
                'i slp_left_branch_finite_coordinates).
              slp_right_branch_finite_center_integrand tau
                (\<lambda>u. center_field u * primitive u)
                (slp_right_branch_complex_amplitude_finite root_weight cutoff
                  potential (\<lambda>_. 1) (\<lambda>_. 1))
                (center, coordinates) \<partial>lborel \<partial>lborel)"
proof -
  let ?primitive_amplitude =
    "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
      primitive (\<lambda>_. 1) ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?unit_amplitude =
    "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
      (\<lambda>_. 1) (\<lambda>_. 1) ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?first =
    "slp_right_branch_finite_center_integrand tau center_field
      ?primitive_amplitude"
  let ?second =
    "slp_right_branch_finite_center_integrand tau
      (\<lambda>u. center_field u * primitive u) ?unit_amplitude"
  let ?graph =
    "\<lambda>(center, coordinates ::
        'i slp_left_branch_finite_coordinates).
      center_field center *
        (root_weight (fst coordinates) *
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. primitive x - primitive center)
            (fst coordinates) (snd coordinates))"
  have first_joint:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: 'i slp_left_branch_finite_coordinates measure)) ?first"
    by (rule slp_right_branch_finite_center_integrand_integrable[OF
          center_integrable primitive_amplitude_integrable])
  have second_joint:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: 'i slp_left_branch_finite_coordinates measure)) ?second"
    by (rule slp_right_branch_finite_center_integrand_integrable[OF
          source_integrable unit_amplitude_integrable])
  have first_joint_split:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: 'i slp_left_branch_finite_coordinates measure))
        (case_prod (\<lambda>center coordinates. ?first (center, coordinates)))"
    using first_joint by simp
  have second_joint_split:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: 'i slp_left_branch_finite_coordinates measure))
        (case_prod (\<lambda>center coordinates. ?second (center, coordinates)))"
    using second_joint by simp
  have graph_pointwise:
      "?graph pair = ?first pair - ?second pair" for pair
  proof -
    obtain center coordinates where pair_eq: "pair = (center, coordinates)"
      by (cases pair) simp
    show ?thesis
      unfolding pair_eq split_beta'
        slp_right_branch_finite_center_integrand_def
      apply (subst
        slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_primitive_diff)
      by (simp add: algebra_simps)
  qed
  have graph_eq:
      "?graph = (\<lambda>pair. ?first pair - ?second pair)"
    by (rule ext) (rule graph_pointwise)
  have graph_joint:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: 'i slp_left_branch_finite_coordinates measure)) ?graph"
    unfolding graph_eq
    by (rule Bochner_Integration.integrable_diff[OF first_joint second_joint])
  have graph_fubini:
      "(\<integral>center.
          \<integral>(coordinates ::
              'i slp_left_branch_finite_coordinates).
            ?graph (center, coordinates) \<partial>lborel
          \<partial>(lborel :: slp_point measure)) =
        integral\<^sup>L
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: 'i slp_left_branch_finite_coordinates measure))
          ?graph"
    using lborel_pair.integral_fst[OF graph_joint] by simp
  have first_fubini:
      "(\<integral>center.
          \<integral>(coordinates ::
              'i slp_left_branch_finite_coordinates).
            ?first (center, coordinates) \<partial>lborel
          \<partial>(lborel :: slp_point measure)) =
        integral\<^sup>L
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: 'i slp_left_branch_finite_coordinates measure))
          ?first"
    using lborel_pair.integral_fst[OF first_joint_split] by simp
  have second_fubini:
      "(\<integral>center.
          \<integral>(coordinates ::
              'i slp_left_branch_finite_coordinates).
            ?second (center, coordinates) \<partial>lborel
          \<partial>(lborel :: slp_point measure)) =
        integral\<^sup>L
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: 'i slp_left_branch_finite_coordinates measure))
          ?second"
    using lborel_pair.integral_fst[OF second_joint_split] by simp
  have product_split:
      "integral\<^sup>L
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: 'i slp_left_branch_finite_coordinates measure))
          ?graph =
        integral\<^sup>L
            ((lborel :: slp_point measure) \<Otimes>\<^sub>M
              (lborel :: 'i slp_left_branch_finite_coordinates measure))
            ?first -
          integral\<^sup>L
            ((lborel :: slp_point measure) \<Otimes>\<^sub>M
              (lborel :: 'i slp_left_branch_finite_coordinates measure))
            ?second"
    unfolding graph_eq
    by (rule Bochner_Integration.integral_diff[OF first_joint second_joint])
  have graph_nested:
      "(\<integral>center. center_field center *
          (\<integral>(coordinates ::
              'i slp_left_branch_finite_coordinates).
            root_weight (fst coordinates) *
              slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
                center cutoff potential
                  (\<lambda>x. primitive x - primitive center)
                (fst coordinates) (snd coordinates)
            \<partial>lborel)
          \<partial>(lborel :: slp_point measure)) =
        (\<integral>center.
          \<integral>(coordinates ::
              'i slp_left_branch_finite_coordinates).
            ?graph (center, coordinates) \<partial>lborel
          \<partial>(lborel :: slp_point measure))"
    by simp
  have outer_split:
      "(\<integral>center. center_field center *
          (\<integral>(coordinates ::
              'i slp_left_branch_finite_coordinates).
            root_weight (fst coordinates) *
              slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
                center cutoff potential
                  (\<lambda>x. primitive x - primitive center)
                (fst coordinates) (snd coordinates)
            \<partial>lborel)
          \<partial>(lborel :: slp_point measure)) =
        (\<integral>center.
          \<integral>(coordinates ::
              'i slp_left_branch_finite_coordinates).
            ?first (center, coordinates) \<partial>lborel
          \<partial>(lborel :: slp_point measure)) -
        (\<integral>center.
          \<integral>(coordinates ::
              'i slp_left_branch_finite_coordinates).
            ?second (center, coordinates) \<partial>lborel
          \<partial>(lborel :: slp_point measure))"
    using graph_nested graph_fubini first_fubini second_fubini product_split
    by simp
  have coefficient:
      "(of_real tau * inverse (of_real pi) :: complex) =
        of_real (tau / pi)"
    by (simp add: divide_inverse)
  show ?thesis
    using outer_split
    by (simp only: coefficient right_diff_distrib)
qed

end
