theory Inverse_Schrodinger_Lp_Damped_Center_Hyperbolic_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Planar_Pair_Transport"
begin

section \<open>The exact hyperbolic Fubini identity\<close>

lemma slp_damped_center_fourier_transform_hyperbolic_fubini:
  assumes eps: "0 < eps"
  shows "slp_fourier_transform
      (slp_damped_center_kernel eps tau) xi =
    (1 / 2) *\<^sub>R
      integral\<^sup>L lborel
        (slp_hyperbolic_post_first eps tau xi)"
proof -
  let ?F = "\<lambda>x.
    slp_fourier_phase xi x * slp_damped_center_kernel eps tau x"
  let ?G = "\<lambda>u. ?F (slp_hyperbolic_mix u)"
  let ?H = "\<lambda>uv :: real \<times> real.
    ?G (slp_pair_to_point uv)"
  have damped_integrable:
      "integrable lborel (slp_damped_center_kernel eps tau)"
    by (rule slp_damped_center_kernel_integrable[OF eps])
  have F_integrable: "integrable lborel ?F"
    by (rule slp_fourier_integrand_integrable[OF damped_integrable])
  have G_integrable: "integrable lborel ?G"
    by (rule slp_hyperbolic_mix_integrable[OF F_integrable])
  have H_integrable:
      "integrable (lborel :: (real \<times> real) measure) ?H"
    by (rule slp_pair_pullback_integrable[OF G_integrable])
  have H_product_case_integrable:
      "integrable
        ((lborel :: real measure) \<Otimes>\<^sub>M lborel)
        (case_prod (curry ?H))"
    using H_integrable
    by (simp only: lborel_prod case_prod_curry)
  have inner_value:
      "integral\<^sup>L lborel (\<lambda>u. ?H (u, v)) =
        slp_hyperbolic_post_first eps tau xi v" for v
  proof -
    have pointwise:
        "?H (u, v) =
          slp_hyperbolic_first_fiber eps tau xi v u *
            slp_hyperbolic_outer_factor eps xi v" for u
      by (simp add: slp_pair_to_point_def
          slp_hyperbolic_pulled_integrand_factor)
    have fiber_integrable:
        "integrable lborel
          (slp_hyperbolic_first_fiber eps tau xi v)"
      by (rule slp_hyperbolic_first_fiber_integrable[OF eps])
    have replacement:
        "integral\<^sup>L lborel (\<lambda>u. ?H (u, v)) =
          integral\<^sup>L lborel (\<lambda>u.
            slp_hyperbolic_first_fiber eps tau xi v u *
              slp_hyperbolic_outer_factor eps xi v)"
      by (rule Bochner_Integration.integral_cong[OF refl])
        (simp only: pointwise)
    have extraction:
        "integral\<^sup>L lborel (\<lambda>u.
            slp_hyperbolic_first_fiber eps tau xi v u *
              slp_hyperbolic_outer_factor eps xi v) =
          integral\<^sup>L lborel
              (slp_hyperbolic_first_fiber eps tau xi v) *
            slp_hyperbolic_outer_factor eps xi v"
      by (rule Bochner_Integration.integral_mult_left_zero)
    show ?thesis
      using replacement extraction
      by (simp only: slp_hyperbolic_post_first_def mult.commute)
  qed
  have pair_as_iterated:
      "integral\<^sup>L (lborel :: (real \<times> real) measure) ?H =
        integral\<^sup>L lborel
          (slp_hyperbolic_post_first eps tau xi)"
  proof -
    have fubini:
        "integral\<^sup>L lborel
            (\<lambda>v. integral\<^sup>L lborel (\<lambda>u. ?H (u, v))) =
          integral\<^sup>L
            ((lborel :: real measure) \<Otimes>\<^sub>M lborel)
            (case_prod (curry ?H))"
      using lborel_pair.integral_snd[
        where f = "curry ?H", OF H_product_case_integrable]
      by simp
    have product_presentation:
        "integral\<^sup>L (lborel :: (real \<times> real) measure) ?H =
          integral\<^sup>L
            ((lborel :: real measure) \<Otimes>\<^sub>M lborel)
            (case_prod (curry ?H))"
      by (simp only: lborel_prod case_prod_curry)
    have iterated_value:
        "integral\<^sup>L lborel
            (\<lambda>v. integral\<^sup>L lborel (\<lambda>u. ?H (u, v))) =
          integral\<^sup>L lborel
            (slp_hyperbolic_post_first eps tau xi)"
      by (rule Bochner_Integration.integral_cong[OF refl])
        (simp only: inner_value)
    show ?thesis
      using product_presentation fubini iterated_value
      by simp
  qed
  have pulled_integral:
      "integral\<^sup>L lborel ?G =
        integral\<^sup>L (lborel :: (real \<times> real) measure) ?H"
    by (rule slp_pair_pullback_integral[OF G_integrable])
  have hyperbolic_integral:
      "integral\<^sup>L lborel ?F =
        (1 / 2) *\<^sub>R integral\<^sup>L lborel ?G"
    by (rule slp_hyperbolic_mix_integral[OF F_integrable])
  show ?thesis
    unfolding slp_fourier_transform_def
    using hyperbolic_integral pulled_integral pair_as_iterated
    by simp
qed

end
