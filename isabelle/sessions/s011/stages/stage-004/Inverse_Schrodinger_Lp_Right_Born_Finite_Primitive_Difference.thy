theory Inverse_Schrodinger_Lp_Right_Born_Finite_Primitive_Difference
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Born_Natural_Graph"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Finite_Primitive_Difference_Transport"
begin

section \<open>The right Born functional on iterated finite primitive-difference coordinates\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_branch_natural_root_integral_eq_fixed_finite_primitive_diff:
  fixes branch_dummy :: "'i::finite itself"
    and p tau :: real
    and center :: slp_point
    and root_weight cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
  shows
    "(\<integral>root. root_weight root *
        integral\<^sup>L
          (((PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
            (PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
          (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            root)
      \<partial>(lborel :: slp_point measure)) =
      (\<integral>root. root_weight root *
        (\<integral>inner.
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            root inner
          \<partial>(lborel ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure))
      \<partial>(lborel :: slp_point measure))"
proof (rule Bochner_Integration.integral_cong[OF refl])
  fix root :: slp_point
  assume "root \<in> space (lborel :: slp_point measure)"
  have inner_eq:
      "integral\<^sup>L
          (((PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
            (PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
          (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            root) =
        (\<integral>inner.
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            root inner
          \<partial>(lborel ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure))"
    by (rule sym, rule
      slp_right_branch_oscillatory_graph_kernel_natural_finite_primitive_diff_integral[
        where p=p, OF p_lower p_upper cutoff_measurable potential_lp])
  show
    "root_weight root *
        integral\<^sup>L
          (((PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
            (PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
          (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            root) =
      root_weight root *
        (\<integral>inner.
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
            center cutoff potential
              (\<lambda>x. slp_cauchy_transform orientation potential x -
                slp_cauchy_transform orientation potential center)
            root inner
          \<partial>(lborel ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure))"
    by (simp only: inner_eq)
qed

theorem slp_right_born_functional_eq_fixed_finite_primitive_diff_iterated:
  fixes branch_dummy :: "'i::finite itself"
    and B C p tau :: real
    and phi root_weight cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and root_weight_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow> Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "slp_right_born_functional CARD('i) tau phi root_weight cutoff potential
        orientation =
      of_real tau * inverse (of_real pi) *
        integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
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
            \<partial>(lborel :: slp_point measure)))"
proof -
  have born_graph:
      "slp_right_born_functional CARD('i) tau phi root_weight cutoff potential
          orientation =
        of_real tau * inverse (of_real pi) *
          integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
            phi center *
              integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
                root_weight root *
                  integral\<^sup>L
                    (((PiM {..<CARD('i)}
                        (\<lambda>_::nat. (lborel :: slp_point measure)))
                        \<Otimes>\<^sub>M
                      (PiM {..<CARD('i)}
                        (\<lambda>_::nat. (lborel :: slp_point measure))))
                        \<Otimes>\<^sub>M (lborel :: slp_point measure))
                    (slp_right_branch_oscillatory_graph_kernel_natural
                      CARD('i) tau center cutoff potential
                        (\<lambda>x.
                          slp_cauchy_transform orientation potential x -
                          slp_cauchy_transform orientation potential center)
                      root)))"
    by (rule slp_right_born_functional_eq_natural_graph[
          where B=B and C=C and p=p,
          OF B_nonnegative root_weight_support cutoff_support potential_support
            p_lower p_upper cutoff_measurable potential_lp cutoff_bound
            C_nonnegative])
  have center_eq:
      "integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
          root_weight root *
            integral\<^sup>L
              (((PiM {..<CARD('i)}
                  (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
                (PiM {..<CARD('i)}
                  (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
                (lborel :: slp_point measure))
              (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau
                center cutoff potential
                  (\<lambda>x. slp_cauchy_transform orientation potential x -
                    slp_cauchy_transform orientation potential center)
                root)) =
        (\<integral>root. root_weight root *
          (\<integral>inner.
            slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
              center cutoff potential
                (\<lambda>x. slp_cauchy_transform orientation potential x -
                  slp_cauchy_transform orientation potential center)
              root inner
            \<partial>(lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
              slp_point) measure))
        \<partial>(lborel :: slp_point measure))" for center
    by (rule
      slp_right_branch_natural_root_integral_eq_fixed_finite_primitive_diff[
        where p=p, OF p_lower p_upper cutoff_measurable potential_lp])
  have outer_eq:
      "integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
          phi center *
            integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
              root_weight root *
                integral\<^sup>L
                  (((PiM {..<CARD('i)}
                      (\<lambda>_::nat. (lborel :: slp_point measure)))
                      \<Otimes>\<^sub>M
                    (PiM {..<CARD('i)}
                      (\<lambda>_::nat. (lborel :: slp_point measure))))
                      \<Otimes>\<^sub>M (lborel :: slp_point measure))
                  (slp_right_branch_oscillatory_graph_kernel_natural
                    CARD('i) tau center cutoff potential
                      (\<lambda>x.
                        slp_cauchy_transform orientation potential x -
                        slp_cauchy_transform orientation potential center)
                    root))) =
        integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
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
            \<partial>(lborel :: slp_point measure)))"
  proof (rule Bochner_Integration.integral_cong[OF refl])
    fix center :: slp_point
    assume "center \<in> space (lborel :: slp_point measure)"
    show
      "phi center *
          integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
            root_weight root *
              integral\<^sup>L
                (((PiM {..<CARD('i)}
                    (\<lambda>_::nat. (lborel :: slp_point measure)))
                    \<Otimes>\<^sub>M
                  (PiM {..<CARD('i)}
                    (\<lambda>_::nat. (lborel :: slp_point measure))))
                    \<Otimes>\<^sub>M (lborel :: slp_point measure))
                (slp_right_branch_oscillatory_graph_kernel_natural
                  CARD('i) tau center cutoff potential
                    (\<lambda>x.
                      slp_cauchy_transform orientation potential x -
                      slp_cauchy_transform orientation potential center)
                  root)) =
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
          \<partial>(lborel :: slp_point measure))"
      by (simp only: center_eq)
  qed
  show ?thesis
    using born_graph outer_eq by simp
qed

end

end
