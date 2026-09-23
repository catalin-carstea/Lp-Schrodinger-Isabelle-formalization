theory Inverse_Schrodinger_Lp_H1_Pair_W1p_Descent
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Affine_Fixed_Point_H1"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Project H1 pairs as exponent-two W1p pairs\<close>

lemma slp_h1_gradient_component_square_integrable:
  fixes Du :: slp_gradient_field
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and Du_measurable:
      "Du \<in> borel_measurable (restrict_space lborel X)"
    and gradient_square_integrable:
      "set_integrable lborel X
        (\<lambda>x. Real_Vector_Spaces.norm (Du x) ^ 2)"
  shows "set_integrable lborel X
    (\<lambda>x. Real_Vector_Spaces.norm (Du x $ i) ^ 2)"
proof -
  have component_measurable:
      "(\<lambda>x. Du x $ i) \<in>
        borel_measurable (restrict_space lborel X)"
  proof -
    have projection_measurable:
        "(\<lambda>v :: complex ^ 2. v $ i) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
         (intro continuous_intros)
    show ?thesis
      using measurable_comp[OF Du_measurable projection_measurable]
      by (simp only: comp_def)
  qed
  have restricted_component_measurable:
      "(\<lambda>x. indicator X x *\<^sub>R (Du x $ i))
        \<in> borel_measurable lborel"
    using component_measurable
    by (subst (asm) borel_measurable_restrict_space_iff)
       (use X_measurable in simp_all)
  have target_measurable:
      "(\<lambda>x. indicator X x *\<^sub>R
          (Real_Vector_Spaces.norm (Du x $ i) ^ 2))
        \<in> borel_measurable lborel"
  proof -
    have source: "(\<lambda>x. Real_Vector_Spaces.norm
          (indicator X x *\<^sub>R (Du x $ i)) ^ 2)
        \<in> borel_measurable lborel"
      using restricted_component_measurable by measurable
    have normalization:
        "(\<lambda>x. Real_Vector_Spaces.norm
            (indicator X x *\<^sub>R (Du x $ i)) ^ 2) =
          (\<lambda>x. indicator X x *\<^sub>R
            (Real_Vector_Spaces.norm (Du x $ i) ^ 2))"
      by (rule ext) (auto simp: indicator_def)
    show ?thesis
      using source unfolding normalization .
  qed
  have majorant_integrable:
      "integrable lborel
        (\<lambda>x. indicator X x *\<^sub>R
          (Real_Vector_Spaces.norm (Du x) ^ 2))"
    using gradient_square_integrable unfolding set_integrable_def .
  have pointwise_bound:
      "AE x in lborel.
        norm (indicator X x *\<^sub>R
            (Real_Vector_Spaces.norm (Du x $ i) ^ 2))
          \<le> norm (indicator X x *\<^sub>R
            (Real_Vector_Spaces.norm (Du x) ^ 2))"
  proof (rule AE_I2)
    fix x :: slp_point
    have coordinate_bound:
        "Real_Vector_Spaces.norm (Du x $ i)
          \<le> Real_Vector_Spaces.norm (Du x)"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    have square_bound:
        "Real_Vector_Spaces.norm (Du x $ i) ^ 2
          \<le> Real_Vector_Spaces.norm (Du x) ^ 2"
      by (rule power_mono[OF coordinate_bound]) simp
    show "norm (indicator X x *\<^sub>R
          (Real_Vector_Spaces.norm (Du x $ i) ^ 2))
        \<le> norm (indicator X x *\<^sub>R
          (Real_Vector_Spaces.norm (Du x) ^ 2))"
      by (cases "x \<in> X")
         (use square_bound in \<open>simp_all add: indicator_def\<close>)
  qed
  have target_integrable:
      "integrable lborel
        (\<lambda>x. indicator X x *\<^sub>R
          (Real_Vector_Spaces.norm (Du x $ i) ^ 2))"
    by (rule Bochner_Integration.integrable_bound[OF
          majorant_integrable target_measurable pointwise_bound])
  show ?thesis
    using target_integrable unfolding set_integrable_def .
qed

lemma slp_h1_pair_on_w1p_pair_on_two:
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and pair: "slp_h1_pair_on X u Du"
  shows "slp_w1p_pair_on 2 X u Du"
proof -
  have u_measurable:
      "u \<in> borel_measurable (restrict_space lborel X)"
    and Du_measurable:
      "Du \<in> borel_measurable (restrict_space lborel X)"
    and weak: "slp_weak_gradient_on X u Du"
    and u_square_integrable:
      "set_integrable lborel X
        (\<lambda>x. Real_Vector_Spaces.norm (u x) ^ 2)"
    and gradient_square_integrable:
      "set_integrable lborel X
        (\<lambda>x. Real_Vector_Spaces.norm (Du x) ^ 2)"
    using pair unfolding slp_h1_pair_on_def by blast+
  have u_indicator_measurable:
      "(\<lambda>x. indicator X x *\<^sub>R u x) \<in> borel_measurable lborel"
    using u_measurable
    by (subst (asm) borel_measurable_restrict_space_iff)
       (use X_measurable in simp_all)
  have u_restricted_measurable:
      "slp_restrict_field X u \<in> borel_measurable lborel"
  proof -
    have restriction:
        "(\<lambda>x. indicator X x *\<^sub>R u x) = slp_restrict_field X u"
      by (rule ext) (auto simp: indicator_def slp_restrict_field_def)
    show ?thesis
      using u_indicator_measurable unfolding restriction .
  qed
  have u_restricted_power_integrable:
      "integrable lborel
        (\<lambda>x. Real_Vector_Spaces.norm (slp_restrict_field X u x)
          powr 2)"
  proof -
    have source: "integrable lborel
        (\<lambda>x. indicator X x *\<^sub>R
          (Real_Vector_Spaces.norm (u x) ^ 2))"
      using u_square_integrable unfolding set_integrable_def .
    have restriction_square:
        "(\<lambda>x. indicator X x *\<^sub>R
            (Real_Vector_Spaces.norm (u x) ^ 2)) =
          (\<lambda>x. Real_Vector_Spaces.norm (slp_restrict_field X u x)
            powr 2)"
      by (rule ext)
         (auto simp: indicator_def slp_restrict_field_def powr_nat)
    show ?thesis
      using source unfolding restriction_square .
  qed
  have u_l2: "slp_complex_lp_on 2 X u"
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
    using u_restricted_measurable u_restricted_power_integrable by blast
  have component_l2: "slp_complex_lp_on 2 X (\<lambda>x. Du x $ i)" for i
  proof -
    have component_measurable:
        "(\<lambda>x. Du x $ i) \<in>
          borel_measurable (restrict_space lborel X)"
    proof -
      have projection_measurable:
          "(\<lambda>v :: complex ^ 2. v $ i) \<in> borel_measurable borel"
        by (rule borel_measurable_continuous_onI)
           (intro continuous_intros)
      show ?thesis
        using measurable_comp[OF Du_measurable projection_measurable]
        by (simp only: comp_def)
    qed
    have component_indicator_measurable:
        "(\<lambda>x. indicator X x *\<^sub>R (Du x $ i))
          \<in> borel_measurable lborel"
      using component_measurable
      by (subst (asm) borel_measurable_restrict_space_iff)
         (use X_measurable in simp_all)
    have component_restricted_measurable:
        "slp_restrict_field X (\<lambda>x. Du x $ i)
          \<in> borel_measurable lborel"
    proof -
      have restriction:
          "(\<lambda>x. indicator X x *\<^sub>R (Du x $ i)) =
            slp_restrict_field X (\<lambda>x. Du x $ i)"
        by (rule ext) (auto simp: indicator_def slp_restrict_field_def)
      show ?thesis
        using component_indicator_measurable unfolding restriction .
    qed
    have component_square_integrable:
        "set_integrable lborel X
          (\<lambda>x. Real_Vector_Spaces.norm (Du x $ i) ^ 2)"
      by (rule slp_h1_gradient_component_square_integrable[OF
            X_measurable Du_measurable gradient_square_integrable])
    have component_restricted_power_integrable:
        "integrable lborel
          (\<lambda>x. Real_Vector_Spaces.norm
            (slp_restrict_field X (\<lambda>y. Du y $ i) x) powr 2)"
    proof -
      have source: "integrable lborel
          (\<lambda>x. indicator X x *\<^sub>R
            (Real_Vector_Spaces.norm (Du x $ i) ^ 2))"
        using component_square_integrable unfolding set_integrable_def .
      have restriction_square:
          "(\<lambda>x. indicator X x *\<^sub>R
              (Real_Vector_Spaces.norm (Du x $ i) ^ 2)) =
            (\<lambda>x. Real_Vector_Spaces.norm
              (slp_restrict_field X (\<lambda>y. Du y $ i) x) powr 2)"
        by (rule ext)
           (auto simp: indicator_def slp_restrict_field_def powr_nat)
      show ?thesis
        using source unfolding restriction_square .
    qed
    show ?thesis
      unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
      using component_restricted_measurable
        component_restricted_power_integrable by blast
  qed
  show ?thesis
    unfolding slp_w1p_pair_on_def
    using weak u_l2 component_l2[of 0] component_l2[of 1] by blast
qed

theorem slp_h1_pair_on_w1p_pair_on_below_two:
  assumes exponent_positive: "0 < (a::real)"
    and exponent_below_two: "a < 2"
    and X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
    and pair: "slp_h1_pair_on X u Du"
  shows "slp_w1p_pair_on a X u Du"
proof -
  have pair_two: "slp_w1p_pair_on 2 X u Du"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF X_measurable pair])
  have weak: "slp_weak_gradient_on X u Du"
    and u_l2: "slp_complex_lp_on 2 X u"
    and D0_l2: "slp_complex_lp_on 2 X (\<lambda>x. Du x $ 0)"
    and D1_l2: "slp_complex_lp_on 2 X (\<lambda>x. Du x $ 1)"
    using pair_two unfolding slp_w1p_pair_on_def by blast+
  have exponent_order: "a \<le> 2"
    using exponent_below_two by linarith
  have u_la: "slp_complex_lp_on a X u"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          exponent_positive exponent_order X_measurable X_bounded u_l2])
  have D0_la: "slp_complex_lp_on a X (\<lambda>x. Du x $ 0)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          exponent_positive exponent_order X_measurable X_bounded D0_l2])
  have D1_la: "slp_complex_lp_on a X (\<lambda>x. Du x $ 1)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          exponent_positive exponent_order X_measurable X_bounded D1_l2])
  show ?thesis
    unfolding slp_w1p_pair_on_def
    using weak u_la D0_la D1_la by blast
qed

end
