theory Inverse_Schrodinger_Lp_Right_Graph_Finite_Center_Cauchy_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Center_Fubini"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Amplitude_Integrable_Lp_Root"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Cauchy_Evaluated"
begin

section \<open>Physical finite right center pair and Fubini\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_branch_finite_center_cauchy_pair_integrable_lp_root:
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
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: 'i slp_left_branch_finite_coordinates measure))
      (slp_right_branch_finite_center_integrand tau phi
        (slp_right_branch_complex_amplitude_finite root_weight cutoff
          potential (slp_cauchy_transform orientation potential)
            (\<lambda>_. 1)))"
    and
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: 'i slp_left_branch_finite_coordinates measure))
      (slp_right_branch_finite_center_integrand tau
        (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)
        (slp_right_branch_complex_amplitude_finite root_weight cutoff
          potential (\<lambda>_. 1) (\<lambda>_. 1)))"
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
        (slp_right_branch_complex_amplitude_finite root_weight cutoff
          potential (slp_cauchy_transform orientation potential)
            (\<lambda>_. 1) ::
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
        (slp_right_branch_complex_amplitude_finite root_weight cutoff
          potential (\<lambda>_. 1) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
        slp_right_branch_complex_amplitude_finite_unit_integrable_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative])
  show
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: 'i slp_left_branch_finite_coordinates measure))
      (slp_right_branch_finite_center_integrand tau phi
        (slp_right_branch_complex_amplitude_finite root_weight cutoff
          potential (slp_cauchy_transform orientation potential)
            (\<lambda>_. 1)))"
    by (rule slp_right_branch_finite_center_integrand_integrable[
          OF phi_integrable primitive_amplitude_integrable])
  show
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: 'i slp_left_branch_finite_coordinates measure))
      (slp_right_branch_finite_center_integrand tau
        (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)
        (slp_right_branch_complex_amplitude_finite root_weight cutoff
          potential (\<lambda>_. 1) (\<lambda>_. 1)))"
    by (rule slp_right_branch_finite_center_integrand_integrable[
          OF source_integrable unit_amplitude_integrable])
qed

theorem slp_right_branch_finite_center_cauchy_pair_fubini_lp_root:
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
    "(\<integral>center.
      \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        slp_right_branch_finite_center_integrand tau phi
          (slp_right_branch_complex_amplitude_finite root_weight cutoff
            potential (slp_cauchy_transform orientation potential)
              (\<lambda>_. 1))
          (center, coordinates) \<partial>lborel \<partial>lborel) =
      (\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        \<integral>center.
        slp_right_branch_finite_center_integrand tau phi
          (slp_right_branch_complex_amplitude_finite root_weight cutoff
            potential (slp_cauchy_transform orientation potential)
              (\<lambda>_. 1))
          (center, coordinates) \<partial>lborel \<partial>lborel)"
    and
    "(\<integral>center.
      \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        slp_right_branch_finite_center_integrand tau
          (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)
          (slp_right_branch_complex_amplitude_finite root_weight cutoff
            potential (\<lambda>_. 1) (\<lambda>_. 1))
          (center, coordinates) \<partial>lborel \<partial>lborel) =
      (\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        \<integral>center.
        slp_right_branch_finite_center_integrand tau
          (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)
          (slp_right_branch_complex_amplitude_finite root_weight cutoff
            potential (\<lambda>_. 1) (\<lambda>_. 1))
          (center, coordinates) \<partial>lborel \<partial>lborel)"
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
        (slp_right_branch_complex_amplitude_finite root_weight cutoff
          potential (slp_cauchy_transform orientation potential)
            (\<lambda>_. 1) ::
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
        (slp_right_branch_complex_amplitude_finite root_weight cutoff
          potential (\<lambda>_. 1) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule
        slp_right_branch_complex_amplitude_finite_unit_integrable_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative])
  note primitive_fubini =
    slp_right_branch_finite_center_integrand_fubini[
      where 'i='i and tau=tau and center_field=phi and
        amplitude="slp_right_branch_complex_amplitude_finite root_weight
          cutoff potential (slp_cauchy_transform orientation potential)
            (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex",
      OF phi_integrable primitive_amplitude_integrable]
  note unit_fubini =
    slp_right_branch_finite_center_integrand_fubini[
      where 'i='i and tau=tau and
        center_field="\<lambda>u. phi u *
          slp_cauchy_transform orientation potential u" and
        amplitude="slp_right_branch_complex_amplitude_finite root_weight
          cutoff potential (\<lambda>_. 1) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex",
      OF source_integrable unit_amplitude_integrable]
  show
    "(\<integral>center.
      \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        slp_right_branch_finite_center_integrand tau phi
          (slp_right_branch_complex_amplitude_finite root_weight cutoff
            potential (slp_cauchy_transform orientation potential)
              (\<lambda>_. 1))
          (center, coordinates) \<partial>lborel \<partial>lborel) =
      (\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        \<integral>center.
        slp_right_branch_finite_center_integrand tau phi
          (slp_right_branch_complex_amplitude_finite root_weight cutoff
            potential (slp_cauchy_transform orientation potential)
              (\<lambda>_. 1))
          (center, coordinates) \<partial>lborel \<partial>lborel)"
    using primitive_fubini by simp
  show
    "(\<integral>center.
      \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        slp_right_branch_finite_center_integrand tau
          (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)
          (slp_right_branch_complex_amplitude_finite root_weight cutoff
            potential (\<lambda>_. 1) (\<lambda>_. 1))
          (center, coordinates) \<partial>lborel \<partial>lborel) =
      (\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        \<integral>center.
        slp_right_branch_finite_center_integrand tau
          (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)
          (slp_right_branch_complex_amplitude_finite root_weight cutoff
            potential (\<lambda>_. 1) (\<lambda>_. 1))
          (center, coordinates) \<partial>lborel \<partial>lborel)"
    using unit_fubini by simp
qed

end

end
