theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Coefficient_Expansion
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Product_Derivative_Split"
begin

section \<open>Exact expansion of the rough far-coefficient contribution\<close>

definition slp_w1p_global_far_cutoff_derivative_source ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_point set \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_w1p_global_far_cutoff_derivative_source delta c X u z =
    slp_real_wirtinger_partial
        (slp_global_cutoff.slp_scaled_cutoff_derivative delta c z) *
      inverse (slp_point_as_complex (z - c)) *
      slp_restrict_field X u z"

definition slp_w1p_global_far_square_denominator_source ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_point set \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_w1p_global_far_square_denominator_source delta c X u z =
    of_real (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c)) ^ 2 *
      slp_restrict_field X u z"

lemma slp_global_far_coefficient_wirtinger_away:
  assumes away_from_center: "z \<noteq> c"
  shows
    "slp_classical_wirtinger_partial
        (slp_global_far_coefficient delta c) z =
      - slp_real_wirtinger_partial
          (slp_global_cutoff.slp_scaled_cutoff_derivative delta c z) *
          inverse (slp_point_as_complex (z - c)) -
        of_real (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *
          inverse (slp_point_as_complex (z - c)) ^ 2"
proof -
  have constant_derivative:
      "((\<lambda>_ :: slp_point. (1 :: complex)) has_derivative
        (\<lambda>_. 0)) (at z)"
    by (auto intro!: derivative_eq_intros)
  have far_derivative:
      "((slp_global_cutoff.slp_far_product delta c
          (\<lambda>_. (1 :: complex))) has_derivative
        slp_global_cutoff.slp_far_product_derivative delta c
          (\<lambda>_. (1 :: complex)) (\<lambda>_. 0) z) (at z)"
    by (rule slp_global_cutoff.slp_far_product_has_derivative[
          OF away_from_center constant_derivative])
  have coefficient_eq:
      "slp_global_far_coefficient delta c =
        slp_global_cutoff.slp_far_product delta c
          (\<lambda>_. (1 :: complex))"
    by (rule ext)
      (simp only: slp_global_far_coefficient_def
        slp_global_cutoff.slp_far_product_def mult.right_neutral)
  have coefficient_derivative:
      "((slp_global_far_coefficient delta c) has_derivative
        slp_global_cutoff.slp_far_product_derivative delta c
          (\<lambda>_. (1 :: complex)) (\<lambda>_. 0) z) (at z)"
    unfolding coefficient_eq by (rule far_derivative)
  have coefficient_frechet:
      "frechet_derivative (slp_global_far_coefficient delta c) (at z) =
        slp_global_cutoff.slp_far_product_derivative delta c
          (\<lambda>_. (1 :: complex)) (\<lambda>_. 0) z"
    by (rule sym, rule frechet_derivative_at[OF coefficient_derivative])
  have zero_wirtinger:
      "slp_complex_wirtinger_partial
        (\<lambda>_ :: slp_point. (0 :: complex)) = 0"
    unfolding slp_complex_wirtinger_partial_def by simp
  show ?thesis
    unfolding slp_classical_wirtinger_partial_frechet coefficient_frechet
      slp_global_cutoff.slp_far_product_partial
      zero_wirtinger
    by (simp only: mult_zero_right mult.right_neutral
          diff_conv_add_uminus add.left_neutral mult_minus_left)
qed

theorem slp_w1p_global_far_coefficient_derivative_source_away:
  assumes away_from_center: "z \<noteq> c"
  shows
    "slp_w1p_global_far_coefficient_derivative_source delta c X u z =
      - slp_w1p_global_far_cutoff_derivative_source delta c X u z -
        slp_w1p_global_far_square_denominator_source delta c X u z"
proof -
  note coefficient = slp_global_far_coefficient_wirtinger_away[
    OF away_from_center, of delta]
  show ?thesis
    unfolding slp_w1p_global_far_coefficient_derivative_source_def
      slp_w1p_global_far_cutoff_derivative_source_def
      slp_w1p_global_far_square_denominator_source_def
      coefficient
    by (simp only: right_diff_distrib mult_minus_right mult.commute
          mult.assoc)
qed

theorem slp_w1p_global_far_coefficient_derivative_source_AE:
  "AE z in (lborel :: slp_point measure).
    slp_w1p_global_far_coefficient_derivative_source delta c X u z =
      - slp_w1p_global_far_cutoff_derivative_source delta c X u z -
        slp_w1p_global_far_square_denominator_source delta c X u z"
proof -
  have sphere_negligible: "negligible (sphere c 0)"
    by (rule negligible_sphere)
  have sphere_null: "sphere c 0 \<in> null_sets lborel"
    using sphere_negligible
    by (auto simp: negligible_iff_null_sets null_sets_completion_iff)
  have away_from_sphere:
      "AE z in (lborel :: slp_point measure). z \<notin> sphere c 0"
    by (rule AE_not_in[OF sphere_null])
  show ?thesis
  proof (rule eventually_mono[OF away_from_sphere])
    fix z :: slp_point
    assume outside: "z \<notin> sphere c 0"
    have away_from_center: "z \<noteq> c"
      using outside by (simp add: sphere_def)
    show
      "slp_w1p_global_far_coefficient_derivative_source delta c X u z =
        - slp_w1p_global_far_cutoff_derivative_source delta c X u z -
          slp_w1p_global_far_square_denominator_source delta c X u z"
      by (rule slp_w1p_global_far_coefficient_derivative_source_away[
            OF away_from_center])
  qed
qed

end
