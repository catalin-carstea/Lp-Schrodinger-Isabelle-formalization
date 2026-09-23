theory Inverse_Schrodinger_Lp_Right_Born_Finite_Coordinates
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Born_Finite_Primitive_Difference"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Primitive_Difference_Fubini"
begin

section \<open>The official right Born functional on finite coordinates\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_born_functional_eq_fixed_finite_primitive_diff_lp_root:
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
  shows
    "slp_right_born_functional CARD('i) tau phi root_weight cutoff potential
        orientation =
      of_real tau * inverse (of_real pi) *
        integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
          phi center *
            (\<integral>(coordinates ::
                'i slp_left_branch_finite_coordinates).
              root_weight (fst coordinates) *
                slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
                  center cutoff potential
                    (\<lambda>x.
                      slp_cauchy_transform orientation potential x -
                      slp_cauchy_transform orientation potential center)
                  (fst coordinates) (snd coordinates)
              \<partial>lborel))"
proof -
  have born_iterated:
      "slp_right_born_functional CARD('i) tau phi root_weight cutoff potential
          orientation =
        of_real tau * inverse (of_real pi) *
          integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
            phi center *
              (\<integral>root. root_weight root *
                (\<integral>inner.
                  slp_right_branch_oscillatory_graph_kernel_fixed_root_finite
                    tau center cutoff potential
                      (\<lambda>x.
                        slp_cauchy_transform orientation potential x -
                        slp_cauchy_transform orientation potential center)
                    root inner
                  \<partial>(lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
                    slp_point) measure))
              \<partial>(lborel :: slp_point measure)))"
    by (rule
      slp_right_born_functional_eq_fixed_finite_primitive_diff_iterated[
        where B=B and C=C and p=p,
        OF B_nonnegative root_support cutoff_support potential_support
          p_lower p_upper cutoff_measurable potential_lp cutoff_bound
          C_nonnegative])
  have center_eq:
      "(\<integral>root. root_weight root *
          (\<integral>inner.
            slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
              center cutoff potential
                (\<lambda>x. slp_cauchy_transform orientation potential x -
                  slp_cauchy_transform orientation potential center)
              root inner
            \<partial>(lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
              slp_point) measure))
        \<partial>(lborel :: slp_point measure)) =
        (\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
          root_weight (fst coordinates) *
            slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
              center cutoff potential
                (\<lambda>x. slp_cauchy_transform orientation potential x -
                  slp_cauchy_transform orientation potential center)
              (fst coordinates) (snd coordinates)
          \<partial>lborel)" for center
    by (rule slp_right_branch_fixed_primitive_diff_root_fubini_lp_root[
          where B=B and C=C and p=p and X=X,
          OF B_nonnegative root_support cutoff_support potential_support
            p_lower p_upper X_measurable X_bounded cutoff_measurable
            potential_lp root_weight_lp root_weight_outside cutoff_bound
            C_nonnegative])
  have outer_eq:
      "integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
          phi center *
            (\<integral>root. root_weight root *
              (\<integral>inner.
                slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
                  center cutoff potential
                    (\<lambda>x.
                      slp_cauchy_transform orientation potential x -
                      slp_cauchy_transform orientation potential center)
                  root inner
                \<partial>(lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
                  slp_point) measure))
            \<partial>(lborel :: slp_point measure))) =
        integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
          phi center *
            (\<integral>(coordinates ::
                'i slp_left_branch_finite_coordinates).
              root_weight (fst coordinates) *
                slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
                  center cutoff potential
                    (\<lambda>x.
                      slp_cauchy_transform orientation potential x -
                      slp_cauchy_transform orientation potential center)
                  (fst coordinates) (snd coordinates)
              \<partial>lborel))"
  proof (rule Bochner_Integration.integral_cong[OF refl])
    fix center :: slp_point
    assume "center \<in> space (lborel :: slp_point measure)"
    show
      "phi center *
          (\<integral>root. root_weight root *
            (\<integral>inner.
              slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
                center cutoff potential
                  (\<lambda>x.
                    slp_cauchy_transform orientation potential x -
                    slp_cauchy_transform orientation potential center)
                root inner
              \<partial>(lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
                slp_point) measure))
          \<partial>(lborel :: slp_point measure)) =
        phi center *
          (\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
            root_weight (fst coordinates) *
              slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
                center cutoff potential
                  (\<lambda>x.
                    slp_cauchy_transform orientation potential x -
                    slp_cauchy_transform orientation potential center)
                (fst coordinates) (snd coordinates)
            \<partial>lborel)"
      by (simp only: center_eq)
  qed
  show ?thesis
    using born_iterated outer_eq by simp
qed

end

end
