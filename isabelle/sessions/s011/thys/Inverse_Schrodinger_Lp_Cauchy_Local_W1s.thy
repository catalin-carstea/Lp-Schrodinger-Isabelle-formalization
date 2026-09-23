theory Inverse_Schrodinger_Lp_Cauchy_Local_W1s
  imports
    Inverse_Schrodinger_Lp_Cauchy_Gradient_Lp
    Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Above_Two
begin

section \<open>A transparent qualitative local Sobolev certificate\<close>

definition slp_local_w1s_certificate ::
  "real \<Rightarrow> slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_gradient_field \<Rightarrow> bool"
where
  "slp_local_w1s_certificate s X u Du \<longleftrightarrow>
    slp_weak_gradient_on UNIV u Du \<and>
    slp_complex_lp_on s X u \<and>
    slp_complex_lp_on s X (\<lambda>x. Du x $ 0) \<and>
    slp_complex_lp_on s X (\<lambda>x. Du x $ 1)"

lemma slp_gradient_components_lp_restrict:
  assumes s_positive: "0 < s"
    and X_measurable: "X \<in> sets lborel"
    and components_lp: "slp_gradient_components_lp s Du"
  shows "slp_complex_lp_on s X (\<lambda>x. Du x $ 0) \<and>
    slp_complex_lp_on s X (\<lambda>x. Du x $ 1)"
proof -
  have component_0:
    "aim_complex_lp_on_plane s (\<lambda>x. Du x $ 0)"
    and component_1:
    "aim_complex_lp_on_plane s (\<lambda>x. Du x $ 1)"
    using components_lp unfolding slp_gradient_components_lp_def by auto
  show ?thesis
    using aim_complex_lp_on_plane_restrict[OF
        s_positive X_measurable component_0]
      aim_complex_lp_on_plane_restrict[OF
        s_positive X_measurable component_1]
    by blast
qed

locale slp_cauchy_local_w1s =
  aim_planar_cauchy_beurling_derivatives +
  aim_planar_hls_cauchy
begin

theorem slp_both_cauchy_local_w1s_certificates:
  assumes s_lower: "1 < (s::real)"
    and f_lp: "aim_complex_lp_on_plane s f"
    and f_support: "bounded {x. f x \<noteq> 0}"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
  shows "slp_local_w1s_certificate s X
      (slp_dbar_inverse f) (slp_dbar_inverse_gradient f) \<and>
    slp_local_w1s_certificate s X
      (slp_partial_inverse f) (slp_partial_inverse_gradient f)"
proof -
  have s_positive: "0 < s"
    using s_lower by linarith
  have gradient_package:
    "slp_weak_gradient_on UNIV
        (slp_dbar_inverse f) (slp_dbar_inverse_gradient f) \<and>
      slp_gradient_components_lp s (slp_dbar_inverse_gradient f) \<and>
      slp_weak_gradient_on UNIV
        (slp_partial_inverse f) (slp_partial_inverse_gradient f) \<and>
      slp_gradient_components_lp s (slp_partial_inverse_gradient f)"
    by (rule slp_both_cauchy_weak_gradients_with_lp_components[OF
          s_lower f_lp f_support])
  have dbar_components:
    "slp_complex_lp_on s X
        (\<lambda>x. slp_dbar_inverse_gradient f x $ 0) \<and>
      slp_complex_lp_on s X
        (\<lambda>x. slp_dbar_inverse_gradient f x $ 1)"
    by (rule slp_gradient_components_lp_restrict[OF
          s_positive X_measurable])
       (use gradient_package in blast)
  have partial_components:
    "slp_complex_lp_on s X
        (\<lambda>x. slp_partial_inverse_gradient f x $ 0) \<and>
      slp_complex_lp_on s X
        (\<lambda>x. slp_partial_inverse_gradient f x $ 1)"
    by (rule slp_gradient_components_lp_restrict[OF
          s_positive X_measurable])
       (use gradient_package in blast)
  have zero_order:
    "slp_complex_lp_on s X (slp_dbar_inverse f) \<and>
      slp_complex_lp_on s X (slp_partial_inverse f)"
  proof (cases "s < 2")
    case True
    show ?thesis
      by (rule slp_both_cauchy_local_lp_below_two[OF
            s_lower True f_lp X_measurable X_bounded])
  next
    case False
    then have two_le: "2 \<le> s"
      by simp
    show ?thesis
    proof (cases "s = 2")
      case True
      then show ?thesis
        using slp_both_cauchy_local_lp_two[OF _ f_support
          X_measurable X_bounded] f_lp
        by simp
    next
      case False
      have two_less: "2 < s"
        using two_le False by linarith
      show ?thesis
        by (rule slp_both_cauchy_local_lp_above_two[OF
              two_less f_lp f_support X_measurable X_bounded])
    qed
  qed
  show ?thesis
    unfolding slp_local_w1s_certificate_def
    using gradient_package dbar_components partial_components zero_order
    by blast
qed

end

end
