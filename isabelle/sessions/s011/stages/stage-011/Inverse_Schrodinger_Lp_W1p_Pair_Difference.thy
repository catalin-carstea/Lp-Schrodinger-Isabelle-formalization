theory Inverse_Schrodinger_Lp_W1p_Pair_Difference
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Pair_AE_Transport"
begin

section \<open>Linearity of valid Sobolev pairs under subtraction\<close>

theorem slp_weak_gradient_on_diff:
  assumes first_weak: "slp_weak_gradient_on X u Du"
    and second_weak: "slp_weak_gradient_on X v Dv"
  shows "slp_weak_gradient_on X (\<lambda>x. u x - v x) (\<lambda>x. Du x - Dv x)"
  unfolding slp_weak_gradient_on_def
proof (intro allI impI)
  fix phi i
  assume phi_test: "slp_test_function_on X phi"
  have first:
      "set_integrable lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) \<and>
       set_integrable lborel X (\<lambda>x. Du x $ i * phi x) \<and>
       set_lebesgue_integral lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * phi x)"
    using first_weak phi_test unfolding slp_weak_gradient_on_def by blast
  have second:
      "set_integrable lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x) \<and>
       set_integrable lborel X (\<lambda>x. Dv x $ i * phi x) \<and>
       set_lebesgue_integral lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel X (\<lambda>x. Dv x $ i * phi x)"
    using second_weak phi_test unfolding slp_weak_gradient_on_def by blast
  have left_integrable:
      "set_integrable lborel X
        (\<lambda>x. (u x - v x) * slp_complex_partial_derivative phi i x)"
    using set_integral_diff(1)[OF conjunct1[OF first] conjunct1[OF second]]
    by (simp add: left_diff_distrib)
  have right_integrable:
      "set_integrable lborel X (\<lambda>x. (Du x - Dv x) $ i * phi x)"
    using set_integral_diff(1)[OF conjunct1[OF conjunct2[OF first]]
          conjunct1[OF conjunct2[OF second]]]
    by (simp add: left_diff_distrib)
  have left_difference:
      "set_lebesgue_integral lborel X
          (\<lambda>x. (u x - v x) * slp_complex_partial_derivative phi i x) =
        set_lebesgue_integral lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) -
        set_lebesgue_integral lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x)"
    using set_integral_diff(2)[OF conjunct1[OF first] conjunct1[OF second]]
    by (simp add: left_diff_distrib)
  have right_difference:
      "set_lebesgue_integral lborel X
          (\<lambda>x. (Du x - Dv x) $ i * phi x) =
        set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * phi x) -
        set_lebesgue_integral lborel X (\<lambda>x. Dv x $ i * phi x)"
    using set_integral_diff(2)[OF conjunct1[OF conjunct2[OF first]]
          conjunct1[OF conjunct2[OF second]]]
    by (simp add: left_diff_distrib)
  have integral_identity:
      "set_lebesgue_integral lborel X
          (\<lambda>x. (u x - v x) * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel X
          (\<lambda>x. (Du x - Dv x) $ i * phi x)"
    using first second left_difference right_difference by simp
  show "set_integrable lborel X
          (\<lambda>x. (u x - v x) * slp_complex_partial_derivative phi i x) \<and>
        set_integrable lborel X (\<lambda>x. (Du x - Dv x) $ i * phi x) \<and>
        set_lebesgue_integral lborel X
          (\<lambda>x. (u x - v x) * slp_complex_partial_derivative phi i x) =
          - set_lebesgue_integral lborel X
            (\<lambda>x. (Du x - Dv x) $ i * phi x)"
    using left_integrable right_integrable integral_identity by blast
qed

theorem slp_w1p_pair_on_diff:
  assumes exponent_one_le: "1 \<le> p"
    and first_pair: "slp_w1p_pair_on p X u Du"
    and second_pair: "slp_w1p_pair_on p X v Dv"
  shows "slp_w1p_pair_on p X (\<lambda>x. u x - v x) (\<lambda>x. Du x - Dv x)"
proof -
  have weak:
      "slp_weak_gradient_on X (\<lambda>x. u x - v x) (\<lambda>x. Du x - Dv x)"
    by (rule slp_weak_gradient_on_diff[
          OF slp_w1p_pair_onD(1)[OF first_pair]
            slp_w1p_pair_onD(1)[OF second_pair]])
  note lp = slp_w1p_pair_difference_lp_components[
    OF exponent_one_le first_pair second_pair]
  show ?thesis
    unfolding slp_w1p_pair_on_def
    using weak lp by blast
qed

end
