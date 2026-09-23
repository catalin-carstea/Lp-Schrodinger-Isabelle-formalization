theory Inverse_Schrodinger_Lp_Right_Born_Functional
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Born_Functional"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Neumann_Iterate"
begin

section \<open>The exact center-averaged right Born functional\<close>

definition slp_right_born_functional ::
    "nat \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_cauchy_orientation \<Rightarrow> complex"
where
  "slp_right_born_functional n tau phi root_weight cutoff potential
      orientation =
    of_real tau * inverse (of_real pi) *
      integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
        phi center *
          integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
            root_weight root *
              slp_right_neumann_iterate n tau center cutoff potential
                orientation root))"

theorem slp_right_born_functional_eq_neg_conjugate_left:
  "slp_right_born_functional n tau phi root_weight cutoff potential
      orientation =
    - cnj (slp_left_born_functional n (- tau)
        (\<lambda>x. cnj (phi x)) (\<lambda>x. cnj (root_weight x))
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
        (slp_opposite_cauchy_orientation orientation))"
proof -
  have inner_conjugate:
      "integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
          root_weight root *
            slp_right_neumann_iterate n tau center cutoff potential
              orientation root) =
        cnj (integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
          cnj (root_weight root) *
            slp_left_neumann_iterate n (- tau) center
              (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
              (slp_opposite_cauchy_orientation orientation) root))"
    for center
  proof -
    have move_conjugate:
        "integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
            cnj (cnj (root_weight root) *
              slp_left_neumann_iterate n (- tau) center
                (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
                (slp_opposite_cauchy_orientation orientation) root)) =
          cnj (integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
            cnj (root_weight root) *
              slp_left_neumann_iterate n (- tau) center
                (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
                (slp_opposite_cauchy_orientation orientation) root))"
      by (rule Bochner_Integration.integral_cnj)
    show ?thesis
      using move_conjugate
      by (simp add: slp_left_neumann_iterate_conjugate_eq_right)
  qed
  have outer_conjugate:
      "integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
          phi center *
            integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
              root_weight root *
                slp_right_neumann_iterate n tau center cutoff potential
                  orientation root)) =
        cnj (integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
          cnj (phi center) *
            integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
              cnj (root_weight root) *
                slp_left_neumann_iterate n (- tau) center
                  (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
                  (slp_opposite_cauchy_orientation orientation) root)))"
  proof -
    have move_conjugate:
        "integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
            cnj (cnj (phi center) *
              integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
                cnj (root_weight root) *
                  slp_left_neumann_iterate n (- tau) center
                    (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
                    (slp_opposite_cauchy_orientation orientation) root))) =
          cnj (integral\<^sup>L (lborel :: slp_point measure) (\<lambda>center.
            cnj (phi center) *
              integral\<^sup>L (lborel :: slp_point measure) (\<lambda>root.
                cnj (root_weight root) *
                  slp_left_neumann_iterate n (- tau) center
                    (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
                    (slp_opposite_cauchy_orientation orientation) root)))"
      by (rule Bochner_Integration.integral_cnj)
    show ?thesis
      using move_conjugate inner_conjugate by simp
  qed
  show ?thesis
    unfolding slp_right_born_functional_def slp_left_born_functional_def
    using outer_conjugate by simp
qed

end
