theory Inverse_Schrodinger_Lp_Left_Born_Functional
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Neumann_Iterate"
begin

section \<open>The exact center-averaged left Born functional\<close>

definition slp_left_born_functional ::
    "nat \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_cauchy_orientation \<Rightarrow> complex"
where
  "slp_left_born_functional n tau phi root_weight cutoff potential
      orientation =
    of_real tau * inverse (of_real pi) *
      integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
        phi center *
          integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
            root_weight root *
              slp_left_neumann_iterate n tau center cutoff potential
                orientation root))"

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_born_functional_eq_natural_graph:
  fixes B C p tau :: real
    and phi root_weight cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and root_weight_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "slp_left_born_functional n tau phi root_weight cutoff potential
        orientation =
      of_real tau * inverse (of_real pi) *
        integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
          phi center *
            integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
              root_weight root *
                integral\<^sup>L
                  (((PiM {..<n}
                      (\<lambda>_::nat. (lborel :: slp_point measure)))
                      \<Otimes>\<^sub>M
                    (PiM {..<n}
                      (\<lambda>_::nat. (lborel :: slp_point measure))))
                      \<Otimes>\<^sub>M (lborel :: slp_point measure))
                  (slp_left_branch_oscillatory_graph_kernel_natural n tau
                    center cutoff potential
                      (\<lambda>x.
                        slp_cauchy_transform orientation potential x -
                        slp_cauchy_transform orientation potential center)
                    root)))"
proof -
  have inner_eq:
      "integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
          root_weight root *
            slp_left_neumann_iterate n tau center cutoff potential orientation
              root) =
        integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
          root_weight root *
            integral\<^sup>L
              (((PiM {..<n}
                  (\<lambda>_::nat. (lborel :: slp_point measure)))
                  \<Otimes>\<^sub>M
                (PiM {..<n}
                  (\<lambda>_::nat. (lborel :: slp_point measure))))
                  \<Otimes>\<^sub>M (lborel :: slp_point measure))
              (slp_left_branch_oscillatory_graph_kernel_natural n tau center
                cutoff potential
                  (\<lambda>x. slp_cauchy_transform orientation potential x -
                    slp_cauchy_transform orientation potential center)
                root))" for center
  proof (rule Bochner_Integration.integral_cong[OF refl])
    fix root :: slp_point
    assume "root \<in> space (lborel :: slp_point measure)"
    show
      "root_weight root *
          slp_left_neumann_iterate n tau center cutoff potential orientation
            root =
        root_weight root *
          integral\<^sup>L
            (((PiM {..<n}
                (\<lambda>_::nat. (lborel :: slp_point measure)))
                \<Otimes>\<^sub>M
              (PiM {..<n}
                (\<lambda>_::nat. (lborel :: slp_point measure))))
                \<Otimes>\<^sub>M (lborel :: slp_point measure))
            (slp_left_branch_oscillatory_graph_kernel_natural n tau center
              cutoff potential
                (\<lambda>x. slp_cauchy_transform orientation potential x -
                  slp_cauchy_transform orientation potential center)
              root)"
    proof (cases "root_weight root = 0")
      case True
      then show ?thesis by simp
    next
      case False
      have root_bound: "Real_Vector_Spaces.norm root \<le> B"
        by (rule root_weight_support[OF False])
      note representation =
        slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_neumann_iterate[
          OF B_nonnegative root_bound cutoff_support potential_support p_lower
            p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative]
      show ?thesis
        using representation by simp
    qed
  qed
  show ?thesis
    unfolding slp_left_born_functional_def
    by (simp only: inner_eq)
qed

end

end
