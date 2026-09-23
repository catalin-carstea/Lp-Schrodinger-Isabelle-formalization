theory Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Cauchy_Evaluated
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Amplitude_Integrable_Lp_Root"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Test_Cauchy_Product_L2"
begin

section \<open>Evaluated finite center pair for the Cauchy primitive\<close>

context aim_planar_hls_cauchy
begin

theorem slp_test_cauchy_product_integrable:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "integrable lborel
      (\<lambda>x. phi x * slp_cauchy_transform orientation potential x)"
proof -
  let ?X = "closure {x. phi x \<noteq> 0}"
  have X_compact: "compact ?X"
    using phi_test unfolding slp_test_function_on_def by blast
  have X_measurable: "?X \<in> sets lborel"
    using borel_compact[OF X_compact] by simp
  have X_bounded: "bounded ?X"
    by (rule compact_imp_bounded[OF X_compact])
  have product_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>x. phi x * slp_cauchy_transform orientation potential x)"
    by (rule slp_test_cauchy_product_l2[OF
          p_lower p_upper potential_lp phi_test])
  have product_outside:
      "\<And>x. x \<notin> ?X \<Longrightarrow>
        phi x * slp_cauchy_transform orientation potential x = 0"
    by auto
  show ?thesis
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded product_l2 product_outside]) simp
qed

end

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_finite_center_cauchy_pair_evaluated_lp_root:
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
          slp_left_branch_finite_center_integrand tau phi
            (slp_left_branch_complex_amplitude_finite root_weight cutoff
              potential (slp_cauchy_transform orientation potential)
                (\<lambda>_. 1))
            (center, coordinates) \<partial>lborel \<partial>lborel) -
      of_real (tau / pi) *
        (\<integral>center.
          \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
          slp_left_branch_finite_center_integrand tau
            (\<lambda>u. phi u * slp_cauchy_transform orientation potential u)
            (slp_left_branch_complex_amplitude_finite root_weight cutoff
              potential (\<lambda>_. 1) (\<lambda>_. 1))
            (center, coordinates) \<partial>lborel \<partial>lborel) =
      slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (slp_cauchy_transform orientation potential)
            (slp_center_average tau phi) -
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
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
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          (slp_cauchy_transform orientation potential) (\<lambda>_. 1) ::
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
  show ?thesis
    by (rule slp_left_branch_finite_center_primitive_pair_evaluated[
          where 'i='i and tau=tau and center_field=phi and
            primitive="slp_cauchy_transform orientation potential" and
            root_weight=root_weight and cutoff=cutoff and potential=potential,
          OF phi_integrable source_integrable primitive_amplitude_integrable
            unit_amplitude_integrable])
qed

end

end
