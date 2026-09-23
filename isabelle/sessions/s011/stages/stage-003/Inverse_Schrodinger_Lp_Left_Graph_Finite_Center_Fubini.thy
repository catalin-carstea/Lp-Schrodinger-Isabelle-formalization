theory Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Primitive_Difference"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Principal_Integral"
begin

section \<open>Finite center-coordinate integrability and Fubini\<close>

lemma slp_left_branch_finite_output_measurable:
  "(\<lambda>(coordinates :: 'i::finite slp_left_branch_finite_coordinates).
      slp_left_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))) \<in> borel_measurable lborel"
proof -
  have packed_tail_measurable:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        snd (slp_one_sided_finite_to_packed_coordinates coordinates))
        \<in> measurable lborel lborel"
    using measurable_compose[
      OF slp_one_sided_finite_to_packed_coordinates_measurable measurable_snd]
    by (simp only: comp_def)
  have packed_output_measurable:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        slp_one_sided_packed_output_point
          (snd (slp_one_sided_finite_to_packed_coordinates coordinates)))
        \<in> borel_measurable lborel"
    using measurable_compose[
      OF packed_tail_measurable
        slp_one_sided_packed_output_point_measurable]
    by (simp only: comp_def)
  show ?thesis
    using packed_output_measurable
    by (simp only: slp_one_sided_finite_packed_output_point)
qed

lemma slp_left_branch_separable_finite_integrable:
  fixes center_field :: "slp_point \<Rightarrow> complex"
    and amplitude :: "'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
  assumes center_integrable: "integrable lborel center_field"
    and amplitude_integrable: "integrable lborel amplitude"
  shows
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: 'i slp_left_branch_finite_coordinates measure))
      (\<lambda>(center, coordinates).
        center_field center * amplitude coordinates)"
proof -
  have product_measurable:
      "(\<lambda>(center, coordinates).
          center_field center * amplitude coordinates) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: 'i slp_left_branch_finite_coordinates measure))"
    using center_integrable amplitude_integrable by measurable
  have amplitude_norm_integrable:
      "integrable
        (lborel :: 'i slp_left_branch_finite_coordinates measure)
        (\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
          norm_class.norm (amplitude coordinates))"
    using amplitude_integrable by simp
  have center_norm_integrable:
      "integrable (lborel :: slp_point measure)
        (\<lambda>center :: slp_point.
          norm_class.norm (center_field center))"
    using center_integrable by simp
  have inner_norm:
      "(\<integral>coordinates. norm_class.norm
          (center_field center * amplitude coordinates)
          \<partial>(lborel :: 'i slp_left_branch_finite_coordinates measure)) =
        norm_class.norm (center_field center) *
          (\<integral>coordinates. norm_class.norm (amplitude coordinates)
            \<partial>(lborel :: 'i slp_left_branch_finite_coordinates measure))"
    for center :: slp_point
    by (simp only: norm_mult
        Bochner_Integration.integral_mult_right[OF amplitude_norm_integrable])
  have scaled_center_norm_integrable:
      "integrable (lborel :: slp_point measure)
        (\<lambda>center :: slp_point.
          norm_class.norm (center_field center) *
            (\<integral>coordinates. norm_class.norm (amplitude coordinates)
              \<partial>(lborel ::
                'i slp_left_branch_finite_coordinates measure)))"
    by (rule Bochner_Integration.integrable_mult_left)
      (use center_norm_integrable in simp)
  have outer_function:
      "(\<lambda>center :: slp_point. \<integral>coordinates.
          norm_class.norm (center_field center * amplitude coordinates)
            \<partial>(lborel :: 'i slp_left_branch_finite_coordinates measure)) =
        (\<lambda>center. norm_class.norm (center_field center) *
          (\<integral>coordinates. norm_class.norm (amplitude coordinates)
            \<partial>(lborel ::
              'i slp_left_branch_finite_coordinates measure)))"
    by (rule ext) (rule inner_norm)
  have outer_integrable:
      "integrable (lborel :: slp_point measure)
        (\<lambda>center :: slp_point. \<integral>coordinates.
          norm_class.norm (center_field center * amplitude coordinates)
            \<partial>(lborel :: 'i slp_left_branch_finite_coordinates measure))"
    using scaled_center_norm_integrable
    by (simp only: outer_function)
  have slice_integrable:
      "AE center in (lborel :: slp_point measure).
        integrable (lborel :: 'i slp_left_branch_finite_coordinates measure)
          (\<lambda>coordinates. center_field center * amplitude coordinates)"
    using amplitude_integrable
    by (intro always_eventually allI
        Bochner_Integration.integrable_mult_right)
  show ?thesis
    by (rule lborel_pair.Fubini_integrable)
      (use product_measurable outer_integrable slice_integrable in simp_all)
qed

definition slp_left_branch_finite_center_integrand ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      ('i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex) \<Rightarrow>
      slp_point \<times> 'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
where
  "slp_left_branch_finite_center_integrand tau center_field amplitude pair =
    center_field (fst pair) *
      slp_center_kernel tau (fst pair)
        (slp_left_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd (snd pair))) $ i)
            (\<lambda>i. snd (fst (snd (snd pair))) $ i))
          (snd (snd (snd pair)))) *
      (exp (\<i> * of_real
          (tau * slp_one_sided_finite_residual (snd pair))) *
        amplitude (snd pair))"

theorem slp_left_branch_finite_center_integrand_integrable:
  fixes center_field :: "slp_point \<Rightarrow> complex"
    and amplitude :: "'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
  assumes center_integrable: "integrable lborel center_field"
    and amplitude_integrable: "integrable lborel amplitude"
  shows
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: 'i slp_left_branch_finite_coordinates measure))
      (slp_left_branch_finite_center_integrand tau center_field amplitude)"
proof (rule Bochner_Integration.integrable_bound[
    OF slp_left_branch_separable_finite_integrable[
      OF center_integrable amplitude_integrable]])
  have center_field_measurable[measurable]:
      "center_field \<in> borel_measurable lborel"
    using center_integrable by measurable
  have amplitude_measurable[measurable]:
      "amplitude \<in> borel_measurable lborel"
    using amplitude_integrable by measurable
  have output_measurable[measurable]:
      "(\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        slp_left_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd coordinates)) $ i)
            (\<lambda>i. snd (fst (snd coordinates)) $ i))
          (snd (snd coordinates))) \<in> borel_measurable lborel"
    by (rule slp_left_branch_finite_output_measurable)
  have residual_measurable[measurable]:
      "(slp_one_sided_finite_residual ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> real)
        \<in> borel_measurable lborel"
    unfolding slp_one_sided_finite_residual_def
    using measurable_compose[
      OF measurable_compose[
        OF slp_one_sided_finite_to_packed_coordinates_measurable measurable_snd]
        slp_one_sided_packed_residual_measurable]
    by (simp only: comp_def)
  have output_snd_measurable:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        slp_left_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd (snd pair))) $ i)
            (\<lambda>i. snd (fst (snd (snd pair))) $ i))
          (snd (snd (snd pair)))) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: 'i slp_left_branch_finite_coordinates measure))"
    by (rule measurable_snd''[OF output_measurable])
  have residual_snd_measurable:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        slp_one_sided_finite_residual (snd pair)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: 'i slp_left_branch_finite_coordinates measure))"
    by (rule measurable_snd''[OF residual_measurable])
  have amplitude_snd_measurable:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        amplitude (snd pair)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: 'i slp_left_branch_finite_coordinates measure))"
    by (rule measurable_snd''[OF amplitude_measurable])
  have output_snd_lborel_measurable[measurable]:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        slp_left_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd (snd pair))) $ i)
            (\<lambda>i. snd (fst (snd (snd pair))) $ i))
          (snd (snd (snd pair)))) \<in>
        borel_measurable
          (lborel ::
            (slp_point \<times> 'i slp_left_branch_finite_coordinates) measure)"
    using output_snd_measurable by (simp only: lborel_prod)
  have residual_snd_lborel_measurable[measurable]:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        slp_one_sided_finite_residual (snd pair)) \<in>
        borel_measurable
          (lborel ::
            (slp_point \<times> 'i slp_left_branch_finite_coordinates) measure)"
    using residual_snd_measurable by (simp only: lborel_prod)
  have amplitude_snd_lborel_measurable[measurable]:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        amplitude (snd pair)) \<in>
        borel_measurable
          (lborel ::
            (slp_point \<times> 'i slp_left_branch_finite_coordinates) measure)"
    using amplitude_snd_measurable by (simp only: lborel_prod)
  have center_field_fst_measurable:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        center_field (fst pair)) \<in>
        borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: 'i slp_left_branch_finite_coordinates measure))"
    by (rule measurable_fst''[OF center_field_measurable])
  have center_field_fst_lborel_measurable[measurable]:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        center_field (fst pair)) \<in>
        borel_measurable
          (lborel ::
            (slp_point \<times> 'i slp_left_branch_finite_coordinates) measure)"
    using center_field_fst_measurable by (simp only: lborel_prod)
  have coordinate_component_measurable:
      "(\<lambda>x :: slp_point. x $ j) \<in> borel_measurable lborel" for j
    by measurable
  have coordinate_component_borel_measurable:
      "(\<lambda>x :: slp_point. x $ j) \<in> borel_measurable borel" for j
    using coordinate_component_measurable[of j]
    by (simp only: measurable_lborel2)
  have center_component_measurable[measurable]:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        fst pair $ j) \<in>
        borel_measurable
          (lborel ::
            (slp_point \<times> 'i slp_left_branch_finite_coordinates) measure)"
    for j
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI)
      (intro continuous_intros)
  have output_component_measurable[measurable]:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        slp_left_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd (snd pair))) $ i)
            (\<lambda>i. snd (fst (snd (snd pair))) $ i))
          (snd (snd (snd pair))) $ j) \<in>
        borel_measurable
          (lborel ::
            (slp_point \<times> 'i slp_left_branch_finite_coordinates) measure)"
    for j
    using measurable_compose[
      OF output_snd_lborel_measurable coordinate_component_borel_measurable]
    by (simp only: comp_def)
  have center_phase_lborel_measurable:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        slp_center_phase (fst pair)
          (slp_left_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd (snd pair))) $ i)
              (\<lambda>i. snd (fst (snd (snd pair))) $ i))
            (snd (snd (snd pair))))) \<in>
        borel_measurable
          (lborel ::
            (slp_point \<times> 'i slp_left_branch_finite_coordinates) measure)"
    unfolding slp_center_phase_def
    by measurable
  have center_kernel_lborel_measurable[measurable]:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        slp_center_kernel tau (fst pair)
          (slp_left_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd (snd pair))) $ i)
              (\<lambda>i. snd (fst (snd (snd pair))) $ i))
            (snd (snd (snd pair))))) \<in>
        borel_measurable
          (lborel ::
            (slp_point \<times> 'i slp_left_branch_finite_coordinates) measure)"
    unfolding slp_center_kernel_def
    using center_phase_lborel_measurable by measurable
  have residual_amplitude_lborel_measurable[measurable]:
      "(\<lambda>pair ::
          slp_point \<times> 'i slp_left_branch_finite_coordinates.
        exp (\<i> * of_real
            (tau * slp_one_sided_finite_residual (snd pair))) *
          amplitude (snd pair)) \<in>
        borel_measurable
          (lborel ::
            (slp_point \<times> 'i slp_left_branch_finite_coordinates) measure)"
    by measurable
  have joint_lborel_measurable:
      "slp_left_branch_finite_center_integrand tau center_field amplitude \<in>
        borel_measurable
          (lborel ::
            (slp_point \<times> 'i slp_left_branch_finite_coordinates) measure)"
    unfolding slp_left_branch_finite_center_integrand_def
    by measurable
  show
    "slp_left_branch_finite_center_integrand tau center_field amplitude \<in>
      borel_measurable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: 'i slp_left_branch_finite_coordinates measure))"
    using joint_lborel_measurable by (simp only: lborel_prod)
  show
    "AE pair in
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: 'i slp_left_branch_finite_coordinates measure)).
      norm_class.norm
        (slp_left_branch_finite_center_integrand tau center_field amplitude
          pair) \<le>
      norm_class.norm (case pair of (center, coordinates) \<Rightarrow>
        center_field center * amplitude coordinates)"
    unfolding slp_left_branch_finite_center_integrand_def
    apply (intro always_eventually allI)
    by (simp only: norm_mult slp_center_kernel_norm norm_exp_i_times
        mult_1 mult_1_left order_refl split_beta)
qed

theorem slp_left_branch_finite_center_integrand_fubini:
  fixes center_field :: "slp_point \<Rightarrow> complex"
    and amplitude :: "'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
  assumes center_integrable: "integrable lborel center_field"
    and amplitude_integrable: "integrable lborel amplitude"
  shows
    "(\<integral>center. \<integral>coordinates.
        slp_left_branch_finite_center_integrand tau center_field amplitude
          (center, coordinates) \<partial>lborel \<partial>lborel) =
      (\<integral>coordinates. \<integral>center.
        slp_left_branch_finite_center_integrand tau center_field amplitude
          (center, coordinates) \<partial>lborel \<partial>lborel)"
proof (rule sym)
  show
    "(\<integral>coordinates. \<integral>center.
        slp_left_branch_finite_center_integrand tau center_field amplitude
          (center, coordinates) \<partial>lborel \<partial>lborel) =
      (\<integral>center. \<integral>coordinates.
        slp_left_branch_finite_center_integrand tau center_field amplitude
          (center, coordinates) \<partial>lborel \<partial>lborel)"
    by (rule lborel_pair.Fubini_integral)
      (use slp_left_branch_finite_center_integrand_integrable[
        OF center_integrable amplitude_integrable] in simp)
qed

end
