theory Inverse_Schrodinger_Lp_Weak_Product_Rule
  imports Inverse_Schrodinger_Lp_Weak_Test_Derivative
    Inverse_Schrodinger_Lp_Set_Integrable_Multiplier
    Inverse_Schrodinger_Lp_Cauchy_Gradient_Lp
begin

section \<open>Smooth multipliers of Cartesian weak gradients\<close>

lemma aim_complex_lp_on_plane_mult_smooth_set_integrable_bounded:
  fixes f g :: slp_scalar_field
  assumes p_at_least_one: "1 \<le> p"
    and U_measurable: "U \<in> sets lborel"
    and U_bounded: "bounded U"
    and f_lp: "aim_complex_lp_on_plane p f"
    and g_smooth: "smooth_on UNIV g"
  shows "set_integrable lborel U (\<lambda>x. f x * g x)"
proof -
  have closure_compact: "compact (closure U)"
    using U_bounded by simp
  have g_continuous: "continuous_on UNIV g"
    by (rule smooth_on_imp_continuous_on[OF g_smooth])
  have g_measurable: "g \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF g_continuous] by simp
  have g_continuous_closure: "continuous_on (closure U) g"
    by (rule continuous_on_subset[OF g_continuous]) simp
  have closure_integrable:
    "set_integrable lborel (closure U) (\<lambda>x. f x * g x)"
    by (rule aim_complex_lp_on_plane_mult_set_integrable_compact[OF
          p_at_least_one closure_compact f_lp g_measurable
          g_continuous_closure])
  show ?thesis
    by (rule set_integrable_subset[OF closure_integrable
          U_measurable closure_subset])
qed

theorem slp_weak_gradient_on_mult_smooth:
  assumes p_at_least_one: "1 \<le> p"
    and U_measurable: "U \<in> sets lborel"
    and U_bounded: "bounded U"
    and u_lp: "aim_complex_lp_on_plane p u"
    and Du_lp: "slp_gradient_components_lp p Du"
    and a_smooth: "smooth_on UNIV a"
    and weak_u: "slp_weak_gradient_on U u Du"
  shows "slp_weak_gradient_on U
    (\<lambda>x. a x * u x)
    (\<lambda>x. \<chi> i. a x * Du x $ i +
      u x * slp_complex_partial_derivative a i x)"
  unfolding slp_weak_gradient_on_def
proof (intro allI impI)
  fix phi i
  assume phi_test: "slp_test_function_on U phi"
    let ?dphi = "slp_complex_partial_derivative phi i"
    let ?da = "slp_complex_partial_derivative a i"
    let ?A = "\<lambda>x. u x * (a x * ?dphi x)"
    let ?B = "\<lambda>x. u x * (?da x * phi x)"
    let ?C = "\<lambda>x. Du x $ i * (a x * phi x)"
    let ?D = "\<lambda>x. a x * u x * ?dphi x"
    let ?E = "\<lambda>x. (a x * Du x $ i + u x * ?da x) * phi x"

    have phi_smooth: "smooth_on UNIV phi"
      using phi_test unfolding slp_test_function_on_def by blast
    have dphi_smooth: "smooth_on UNIV ?dphi"
      by (rule slp_complex_partial_derivative_smooth[OF phi_smooth])
    have da_smooth: "smooth_on UNIV ?da"
      by (rule slp_complex_partial_derivative_smooth[OF a_smooth])
    have a_dphi_smooth: "smooth_on UNIV (\<lambda>x. a x * ?dphi x)"
      by (rule smooth_on_mult[OF a_smooth dphi_smooth open_UNIV])
    have da_phi_smooth: "smooth_on UNIV (\<lambda>x. ?da x * phi x)"
      by (rule smooth_on_mult[OF da_smooth phi_smooth open_UNIV])
    have a_phi_smooth: "smooth_on UNIV (\<lambda>x. a x * phi x)"
      by (rule smooth_on_mult[OF a_smooth phi_smooth open_UNIV])

    have two_eq_zero: "(2 :: 2) = 0"
      by (simp add: of_nat_eq_0_iff_char_dvd)
    have Du_i_lp: "aim_complex_lp_on_plane p (\<lambda>x. Du x $ i)"
      using Du_lp exhaust_2[of i] two_eq_zero
      unfolding slp_gradient_components_lp_def
      by auto
    have A_integrable: "set_integrable lborel U ?A"
      by (rule aim_complex_lp_on_plane_mult_smooth_set_integrable_bounded[OF
            p_at_least_one U_measurable U_bounded u_lp a_dphi_smooth])
    have B_integrable: "set_integrable lborel U ?B"
      by (rule aim_complex_lp_on_plane_mult_smooth_set_integrable_bounded[OF
            p_at_least_one U_measurable U_bounded u_lp da_phi_smooth])
    have C_integrable: "set_integrable lborel U ?C"
      by (rule aim_complex_lp_on_plane_mult_smooth_set_integrable_bounded[OF
            p_at_least_one U_measurable U_bounded Du_i_lp a_phi_smooth])
    have D_integrable: "set_integrable lborel U ?D"
      using A_integrable by (simp add: mult_ac)
    have E_integrable: "set_integrable lborel U ?E"
    proof -
      have "set_integrable lborel U (\<lambda>x. ?C x + ?B x)"
        by (rule set_integral_add(1)[OF C_integrable B_integrable])
      then show ?thesis
        by (simp add: mult_ac ring_distribs)
    qed

    have multiplied_test:
      "slp_test_function_on U (\<lambda>x. a x * phi x)"
      by (rule slp_test_function_on_mult_left[OF a_smooth phi_test])
    have weak_multiplied:
      "set_integrable lborel U
          (\<lambda>x. u x * slp_complex_partial_derivative
            (\<lambda>y. a y * phi y) i x) \<and>
       set_integrable lborel U (\<lambda>x. Du x $ i * (a x * phi x)) \<and>
       set_lebesgue_integral lborel U
          (\<lambda>x. u x * slp_complex_partial_derivative
            (\<lambda>y. a y * phi y) i x) =
        - set_lebesgue_integral lborel U
          (\<lambda>x. Du x $ i * (a x * phi x))"
      using weak_u multiplied_test
      unfolding slp_weak_gradient_on_def by blast

    have left_expansion:
      "set_lebesgue_integral lborel U
          (\<lambda>x. u x * slp_complex_partial_derivative
            (\<lambda>y. a y * phi y) i x) =
        set_lebesgue_integral lborel U ?A +
          set_lebesgue_integral lborel U ?B"
    proof -
      have "set_lebesgue_integral lborel U
          (\<lambda>x. u x * slp_complex_partial_derivative
            (\<lambda>y. a y * phi y) i x) =
        set_lebesgue_integral lborel U (\<lambda>x. ?A x + ?B x)"
      proof (rule set_lebesgue_integral_cong[OF U_measurable], intro allI impI)
        fix x
        assume "x \<in> U"
        show "u x * slp_complex_partial_derivative
              (\<lambda>y. a y * phi y) i x = ?A x + ?B x"
          unfolding slp_complex_partial_derivative_mult[OF a_smooth phi_smooth]
          by (simp add: ring_distribs)
      qed
      also have "... = set_lebesgue_integral lborel U ?A +
          set_lebesgue_integral lborel U ?B"
        by (rule set_integral_add(2)[OF A_integrable B_integrable])
      finally show ?thesis .
    qed
    have D_integral:
      "set_lebesgue_integral lborel U ?D =
        set_lebesgue_integral lborel U ?A"
      by (rule set_lebesgue_integral_cong[OF U_measurable])
         (intro allI impI, simp add: mult_ac)
    have E_integral:
      "set_lebesgue_integral lborel U ?E =
        set_lebesgue_integral lborel U ?C +
          set_lebesgue_integral lborel U ?B"
    proof -
      have "set_lebesgue_integral lborel U ?E =
          set_lebesgue_integral lborel U (\<lambda>x. ?C x + ?B x)"
        by (rule set_lebesgue_integral_cong[OF U_measurable])
           (intro allI impI, simp add: mult_ac ring_distribs)
      also have "... = set_lebesgue_integral lborel U ?C +
          set_lebesgue_integral lborel U ?B"
        by (rule set_integral_add(2)[OF C_integrable B_integrable])
      finally show ?thesis .
    qed
    have scalar_identity:
      "set_lebesgue_integral lborel U ?A =
        - (set_lebesgue_integral lborel U ?C +
          set_lebesgue_integral lborel U ?B)"
    proof -
      have weak_multiplied_identity:
        "set_lebesgue_integral lborel U
            (\<lambda>x. u x * slp_complex_partial_derivative
              (\<lambda>y. a y * phi y) i x) =
          - set_lebesgue_integral lborel U ?C"
        using weak_multiplied by blast
      have AB_identity:
        "set_lebesgue_integral lborel U ?A +
            set_lebesgue_integral lborel U ?B =
          - set_lebesgue_integral lborel U ?C"
        using weak_multiplied_identity left_expansion
        by simp
      have sub_identity:
        "(set_lebesgue_integral lborel U ?A +
            set_lebesgue_integral lborel U ?B) -
            set_lebesgue_integral lborel U ?B =
          (- set_lebesgue_integral lborel U ?C) -
            set_lebesgue_integral lborel U ?B"
        by (rule arg_cong[OF AB_identity])
      show ?thesis
        using sub_identity by simp
    qed
    have product_identity:
      "set_lebesgue_integral lborel U ?D =
        - set_lebesgue_integral lborel U ?E"
      using D_integral E_integral scalar_identity by simp

    show "set_integrable lborel U
        (\<lambda>x. a x * u x * slp_complex_partial_derivative phi i x) \<and>
      set_integrable lborel U
        (\<lambda>x. (\<chi> j. a x * Du x $ j +
            u x * slp_complex_partial_derivative a j x) $ i *
          phi x) \<and>
      set_lebesgue_integral lborel U
        (\<lambda>x. a x * u x * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel U
          (\<lambda>x. (\<chi> j. a x * Du x $ j +
              u x * slp_complex_partial_derivative a j x) $ i *
            phi x)"
      using D_integrable E_integrable product_identity by simp
qed

end
