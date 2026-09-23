theory Inverse_Schrodinger_Lp_Left_Born_Finite_Center_Cauchy_Evaluated
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Born_Finite_Primitive_Difference"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Cauchy_Evaluated"
begin

section \<open>Evaluation of the finite-coordinate left Born center pair\<close>

theorem slp_left_branch_fixed_primitive_diff_center_pair:
  fixes branch_dummy :: "'i::finite itself"
    and tau :: real
    and center_field primitive root_weight cutoff potential ::
      "slp_point \<Rightarrow> complex"
  assumes center_integrable: "integrable lborel center_field"
    and source_integrable:
      "integrable lborel (\<lambda>u. center_field u * primitive u)"
    and primitive_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          primitive (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and unit_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "of_real tau * inverse (of_real pi) *
        (\<integral>center. center_field center *
          (\<integral>(coordinates ::
              'i slp_left_branch_finite_coordinates).
            root_weight (fst coordinates) *
              slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
                center cutoff potential
                  (\<lambda>x. primitive x - primitive center)
                (fst coordinates) (snd coordinates)
            \<partial>lborel)
          \<partial>(lborel :: slp_point measure)) =
      of_real (tau / pi) *
          (\<integral>center.
            \<integral>(coordinates ::
                'i slp_left_branch_finite_coordinates).
              slp_left_branch_finite_center_integrand tau center_field
                (slp_left_branch_complex_amplitude_finite root_weight cutoff
                  potential primitive (\<lambda>_. 1))
                (center, coordinates) \<partial>lborel \<partial>lborel) -
        of_real (tau / pi) *
          (\<integral>center.
            \<integral>(coordinates ::
                'i slp_left_branch_finite_coordinates).
              slp_left_branch_finite_center_integrand tau
                (\<lambda>u. center_field u * primitive u)
                (slp_left_branch_complex_amplitude_finite root_weight cutoff
                  potential (\<lambda>_. 1) (\<lambda>_. 1))
                (center, coordinates) \<partial>lborel \<partial>lborel)"
proof -
  let ?primitive_amplitude =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      primitive (\<lambda>_. 1) ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?unit_amplitude =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      (\<lambda>_. 1) (\<lambda>_. 1) ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?first =
    "slp_left_branch_finite_center_integrand tau center_field
      ?primitive_amplitude"
  let ?second =
    "slp_left_branch_finite_center_integrand tau
      (\<lambda>u. center_field u * primitive u) ?unit_amplitude"
  let ?graph =
    "\<lambda>(center, coordinates ::
        'i slp_left_branch_finite_coordinates).
      center_field center *
        (root_weight (fst coordinates) *
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. primitive x - primitive center)
            (fst coordinates) (snd coordinates))"
  have first_joint:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: 'i slp_left_branch_finite_coordinates measure)) ?first"
    by (rule slp_left_branch_finite_center_integrand_integrable[OF
          center_integrable primitive_amplitude_integrable])
  have second_joint:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: 'i slp_left_branch_finite_coordinates measure)) ?second"
    by (rule slp_left_branch_finite_center_integrand_integrable[OF
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
        slp_left_branch_finite_center_integrand_def
      apply (subst
        slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_primitive_diff)
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
              slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
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
              slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
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

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_born_functional_eq_finite_center_cauchy_pair_lp_root:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real
    and X :: "slp_point set"
    and phi root_weight cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and root_support:
      "\<And>x :: slp_point. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and cutoff_support:
      "\<And>x :: slp_point. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x :: slp_point. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "slp_left_born_functional CARD('i) tau phi root_weight cutoff potential
        orientation =
      slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (slp_cauchy_transform orientation potential)
            (slp_center_average tau phi) -
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (\<lambda>_. 1)
            (slp_center_average tau
              (\<lambda>u. phi u *
                slp_cauchy_transform orientation potential u))"
proof -
  let ?primitive = "slp_cauchy_transform orientation potential"
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have source_integrable:
      "integrable lborel (\<lambda>u. phi u * ?primitive u)"
    by (rule slp_test_cauchy_product_integrable[OF
          p_lower p_upper potential_lp phi_test])
  have primitive_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          ?primitive (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule slp_left_branch_complex_amplitude_finite_cauchy_integrable_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative])
  have unit_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule slp_left_branch_complex_amplitude_finite_unit_integrable_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative])
  have born_finite:
      "slp_left_born_functional CARD('i) tau phi root_weight cutoff potential
          orientation =
        of_real tau * inverse (of_real pi) *
          integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
            phi center *
              (\<integral>(coordinates ::
                  'i slp_left_branch_finite_coordinates).
                root_weight (fst coordinates) *
                  slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
                    center cutoff potential
                      (\<lambda>x. ?primitive x - ?primitive center)
                    (fst coordinates) (snd coordinates)
                \<partial>lborel))"
    by (rule
      slp_left_born_functional_eq_fixed_finite_primitive_diff_lp_root[
        where B=B and C=C and p=p and X=X,
        OF B_nonnegative root_support cutoff_support potential_support
          p_lower p_upper X_measurable X_bounded cutoff_measurable potential_lp
          root_weight_lp root_weight_outside cutoff_bound C_nonnegative])
  have center_pair:
      "of_real tau * inverse (of_real pi) *
          integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
            phi center *
              (\<integral>(coordinates ::
                  'i slp_left_branch_finite_coordinates).
                root_weight (fst coordinates) *
                  slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau
                    center cutoff potential
                      (\<lambda>x. ?primitive x - ?primitive center)
                    (fst coordinates) (snd coordinates)
                \<partial>lborel)) =
        of_real (tau / pi) *
            (\<integral>center.
              \<integral>(coordinates ::
                  'i slp_left_branch_finite_coordinates).
                slp_left_branch_finite_center_integrand tau phi
                  (slp_left_branch_complex_amplitude_finite root_weight cutoff
                    potential ?primitive (\<lambda>_. 1))
                  (center, coordinates) \<partial>lborel \<partial>lborel) -
          of_real (tau / pi) *
            (\<integral>center.
              \<integral>(coordinates ::
                  'i slp_left_branch_finite_coordinates).
                slp_left_branch_finite_center_integrand tau
                  (\<lambda>u. phi u * ?primitive u)
                  (slp_left_branch_complex_amplitude_finite root_weight cutoff
                    potential (\<lambda>_. 1) (\<lambda>_. 1))
                  (center, coordinates) \<partial>lborel \<partial>lborel)"
    by (rule slp_left_branch_fixed_primitive_diff_center_pair[OF
          phi_integrable source_integrable primitive_amplitude_integrable
          unit_amplitude_integrable])
  have pair_evaluated:
      "of_real (tau / pi) *
          (\<integral>center.
            \<integral>(coordinates ::
                'i slp_left_branch_finite_coordinates).
              slp_left_branch_finite_center_integrand tau phi
                (slp_left_branch_complex_amplitude_finite root_weight cutoff
                  potential ?primitive (\<lambda>_. 1))
                (center, coordinates) \<partial>lborel \<partial>lborel) -
        of_real (tau / pi) *
          (\<integral>center.
            \<integral>(coordinates ::
                'i slp_left_branch_finite_coordinates).
              slp_left_branch_finite_center_integrand tau
                (\<lambda>u. phi u * ?primitive u)
                (slp_left_branch_complex_amplitude_finite root_weight cutoff
                  potential (\<lambda>_. 1) (\<lambda>_. 1))
                (center, coordinates) \<partial>lborel \<partial>lborel) =
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential ?primitive (slp_center_average tau phi) -
          slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential (\<lambda>_. 1)
              (slp_center_average tau (\<lambda>u. phi u * ?primitive u))"
    by (rule slp_left_branch_finite_center_cauchy_pair_evaluated_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative phi_test])
  show ?thesis
    using born_finite center_pair pair_evaluated by simp
qed

end


end
