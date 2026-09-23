theory Inverse_Schrodinger_Lp_Right_Graph_Finite_Center_Cauchy_Evaluated
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Center_Output"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Amplitude_Integrable_Lp_Root"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Cauchy_Evaluated"
begin

section \<open>Evaluated finite right center pair\<close>

theorem slp_right_branch_finite_center_primitive_pair_evaluated:
  fixes branch_dummy :: "'i::finite itself"
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
    "of_real (tau / pi) *
        (\<integral>center.
          \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
          slp_right_branch_finite_center_integrand tau center_field
            (slp_right_branch_complex_amplitude_finite root_weight cutoff
              potential primitive (\<lambda>_. 1))
            (center, coordinates) \<partial>lborel \<partial>lborel) -
      of_real (tau / pi) *
        (\<integral>center.
          \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
          slp_right_branch_finite_center_integrand tau
            (\<lambda>u. center_field u * primitive u)
            (slp_right_branch_complex_amplitude_finite root_weight cutoff
              potential (\<lambda>_. 1) (\<lambda>_. 1))
            (center, coordinates) \<partial>lborel \<partial>lborel) =
      slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential primitive (slp_center_average tau center_field) -
        slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (\<lambda>_. 1)
            (slp_center_average tau
              (\<lambda>u. center_field u * primitive u))"
proof -
  note primitive_evaluated =
    slp_right_branch_finite_center_integrand_scaled_fubini[
      where 'i='i and tau=tau and center_field=center_field and
        amplitude="slp_right_branch_complex_amplitude_finite root_weight cutoff
          potential primitive (\<lambda>_. 1)",
      OF center_integrable primitive_amplitude_integrable]
  note unit_evaluated =
    slp_right_branch_finite_center_integrand_scaled_fubini[
      where 'i='i and tau=tau and
        center_field="\<lambda>u. center_field u * primitive u" and
        amplitude="slp_right_branch_complex_amplitude_finite root_weight cutoff
          potential (\<lambda>_. 1) (\<lambda>_. 1)",
      OF source_integrable unit_amplitude_integrable]
  note primitive_output = slp_right_branch_finite_center_output_integral[
    where 'i='i and tau=tau and root_weight=root_weight and cutoff=cutoff and
      potential=potential and terminal_value=primitive and
      output_factor="slp_center_average tau center_field"]
  note unit_output = slp_right_branch_finite_center_output_integral[
    where 'i='i and tau=tau and root_weight=root_weight and cutoff=cutoff and
      potential=potential and terminal_value="\<lambda>_. 1" and
      output_factor="slp_center_average tau
        (\<lambda>u. center_field u * primitive u)"]
  show ?thesis
    apply (subst primitive_evaluated)
    apply (subst unit_evaluated)
    apply (subst primitive_output)
    apply (subst unit_output)
    by (rule refl)
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_branch_finite_center_cauchy_pair_evaluated_lp_root:
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
    "of_real (tau / pi) *
        (\<integral>center.
          \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
          slp_right_branch_finite_center_integrand tau phi
            (slp_right_branch_complex_amplitude_finite root_weight cutoff
              potential (slp_cauchy_transform orientation potential)
                (\<lambda>_. 1))
            (center, coordinates) \<partial>lborel \<partial>lborel) -
      of_real (tau / pi) *
        (\<integral>center.
          \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
          slp_right_branch_finite_center_integrand tau
            (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)
            (slp_right_branch_complex_amplitude_finite root_weight cutoff
              potential (\<lambda>_. 1) (\<lambda>_. 1))
            (center, coordinates) \<partial>lborel \<partial>lborel) =
      slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (slp_cauchy_transform orientation potential)
            (slp_center_average tau phi) -
        slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (\<lambda>_. 1)
            (slp_center_average tau
              (\<lambda>u. phi u *
                slp_cauchy_transform orientation potential u))"
proof -
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have source_integrable:
      "integrable lborel
        (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)"
    by (rule slp_test_cauchy_product_integrable[OF
          p_lower p_upper potential_lp phi_test])
  have primitive_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          (slp_cauchy_transform orientation potential) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
        slp_right_branch_complex_amplitude_finite_cauchy_integrable_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative])
  have unit_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
        slp_right_branch_complex_amplitude_finite_unit_integrable_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative])
  show ?thesis
    by (rule slp_right_branch_finite_center_primitive_pair_evaluated[
          where 'i='i and tau=tau and center_field=phi and
            primitive="slp_cauchy_transform orientation potential" and
            root_weight=root_weight and cutoff=cutoff and potential=potential,
          OF phi_integrable source_integrable primitive_amplitude_integrable
            unit_amplitude_integrable])
qed

end

end
