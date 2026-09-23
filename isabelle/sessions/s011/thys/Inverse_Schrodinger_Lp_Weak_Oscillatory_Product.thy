theory Inverse_Schrodinger_Lp_Weak_Oscillatory_Product
  imports Inverse_Schrodinger_Lp_Center_Kernel_Smooth
begin

section \<open>Weak product rule for the physical oscillatory modulation\<close>

theorem slp_weak_gradient_on_oscillatory_modulation:
  assumes p_at_least_one: "1 \<le> p"
    and U_measurable: "U \<in> sets lborel"
    and U_bounded: "bounded U"
    and u_lp: "aim_complex_lp_on_plane p u"
    and Du_lp: "slp_gradient_components_lp p Du"
    and weak_u: "slp_weak_gradient_on U u Du"
  shows "slp_weak_gradient_on U
      (slp_oscillatory_modulation tau c u)
      (\<lambda>x. \<chi> i. slp_center_kernel tau c x * Du x $ i +
        u x * slp_complex_partial_derivative
          (slp_center_kernel tau c) i x) \<and>
    slp_gradient_wirtinger_partial
      (\<lambda>x. \<chi> i. slp_center_kernel tau c x * Du x $ i +
        u x * slp_complex_partial_derivative
          (slp_center_kernel tau c) i x) =
      (\<lambda>x. slp_center_kernel tau c x *
          slp_gradient_wirtinger_partial Du x +
        u x * (\<i> * of_real tau * slp_point_as_complex (x - c) *
          slp_center_kernel tau c x))"
  unfolding slp_oscillatory_modulation_def
  using slp_weak_gradient_on_mult_smooth_wirtinger[
      OF p_at_least_one U_measurable U_bounded u_lp Du_lp
        slp_center_kernel_smooth weak_u, of tau c]
  by (simp only: slp_classical_wirtinger_partial_center_kernel_eq)

end
