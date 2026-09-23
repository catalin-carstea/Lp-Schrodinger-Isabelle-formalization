theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Product_Derivative_Split
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Derivative_Pointwise"
begin

section \<open>Exact splitting of the restricted rough far product derivative\<close>

definition slp_w1p_global_far_coefficient_derivative_source ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_point set \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_w1p_global_far_coefficient_derivative_source delta c X u z =
    slp_restrict_field X u z *
      slp_classical_wirtinger_partial
        (slp_global_far_coefficient delta c) z"

theorem slp_w1p_global_far_product_derivative_split:
  "slp_restrict_field X
      (slp_gradient_wirtinger_partial
        (\<lambda>x. \<chi> i.
          slp_global_far_coefficient delta c x * Du x $ i +
          u x * slp_complex_partial_derivative
            (slp_global_far_coefficient delta c) i x)) =
    (\<lambda>x.
      slp_w1p_global_far_derivative_source delta c X Du x +
      slp_w1p_global_far_coefficient_derivative_source delta c X u x)"
proof (rule ext)
  fix x :: slp_point
  note product = fun_cong[OF slp_product_gradient_wirtinger_partial[
    where a="slp_global_far_coefficient delta c" and Du=Du and u=u], of x]
  show
    "slp_restrict_field X
        (slp_gradient_wirtinger_partial
          (\<lambda>x. \<chi> i.
            slp_global_far_coefficient delta c x * Du x $ i +
            u x * slp_complex_partial_derivative
              (slp_global_far_coefficient delta c) i x)) x =
      slp_w1p_global_far_derivative_source delta c X Du x +
        slp_w1p_global_far_coefficient_derivative_source delta c X u x"
  proof (cases "x \<in> X")
    case True
    show ?thesis
      using product True
      unfolding slp_w1p_global_far_derivative_source_def
        slp_w1p_global_far_coefficient_derivative_source_def
      by (simp only: slp_restrict_field_def if_True
          slp_gradient_wirtinger_partial_restrict_gradient)
  next
    case False
    show ?thesis
      using False
      unfolding slp_w1p_global_far_derivative_source_def
        slp_w1p_global_far_coefficient_derivative_source_def
      by (simp only: slp_restrict_field_def if_False
          slp_gradient_wirtinger_partial_restrict_gradient
          mult_zero_right mult_zero_left add.right_neutral)
  qed
qed

end
