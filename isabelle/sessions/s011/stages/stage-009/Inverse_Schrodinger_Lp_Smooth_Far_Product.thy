theory Inverse_Schrodinger_Lp_Smooth_Far_Product
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Scaled_Smooth_Cutoff_L2"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Far_Product_Rule"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Oscillatory_Test_Closure"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Weak_Test_Multiplier"
begin

section \<open>The removable singularity in the canonical far product\<close>

definition slp_global_far_coefficient ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_global_far_coefficient delta c z =
    of_real (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c))"

lemma slp_global_scaled_cutoff_smooth:
  "smooth_on UNIV (slp_global_cutoff.slp_scaled_cutoff delta c)"
proof -
  have chi_smooth: "smooth_on UNIV slp_global_cutoff_chi"
    by (rule slp_global_cutoff_profile_spec[THEN conjunct2, THEN conjunct1])
  have shift_smooth:
      "smooth_on UNIV (\<lambda>z :: slp_point. z - c)"
    by (rule smooth_on_minus[OF smooth_on_id smooth_on_const open_UNIV])
  have argument_smooth:
      "smooth_on UNIV
        (slp_global_cutoff.slp_cutoff_argument delta c)"
    unfolding slp_global_cutoff.slp_cutoff_argument_def
    by (rule smooth_on_scaleR[OF smooth_on_const shift_smooth open_UNIV])
  have composed:
      "smooth_on UNIV
        (slp_global_cutoff_chi o
          slp_global_cutoff.slp_cutoff_argument delta c)"
    by (rule smooth_on_compose[
          OF chi_smooth argument_smooth open_UNIV open_UNIV])
      (rule subset_UNIV)
  show ?thesis
    unfolding slp_global_cutoff.slp_scaled_cutoff_def
    using composed unfolding o_def .
qed

lemma slp_global_far_coefficient_smooth:
  assumes delta_positive: "0 < delta"
  shows "smooth_on UNIV (slp_global_far_coefficient delta c)"
proof -
  let ?inner = "ball c delta"
  let ?outer = "UNIV - {c}"
  have inner_open: "open ?inner"
    by (rule open_ball)
  have outer_open: "open ?outer"
    by (rule open_Diff[OF open_UNIV closed_singleton])

  have inner_zero:
      "slp_global_far_coefficient delta c z = 0"
    if z_inner: "z \<in> ?inner" for z
  proof -
    have distance: "norm (c - z) < delta"
      using z_inner by (simp only: mem_ball dist_norm)
    have oriented_distance: "norm (z - c) < delta"
      using distance by (simp only: norm_minus_commute)
    have inside: "norm (z - c) \<le> delta"
      by (rule less_imp_le[OF oriented_distance])
    have cutoff_one:
        "slp_global_cutoff.slp_scaled_cutoff delta c z = 1"
      by (rule slp_global_cutoff.slp_scaled_cutoff_inner[
            OF delta_positive inside])
    show ?thesis
      unfolding slp_global_far_coefficient_def
      by (simp only: cutoff_one diff_self of_real_0 mult_zero_left)
  qed
  have inner_smooth:
      "smooth_on ?inner (slp_global_far_coefficient delta c)"
  proof (rule smooth_on_cong[OF smooth_on_const inner_open])
    fix z
    assume "z \<in> ?inner"
    then show "slp_global_far_coefficient delta c z = (0 :: complex)"
      by (rule inner_zero)
  qed

  have scaled_smooth_outer:
      "smooth_on ?outer
        (slp_global_cutoff.slp_scaled_cutoff delta c)"
    by (rule smooth_on_subset[OF slp_global_scaled_cutoff_smooth])
      (rule subset_UNIV)
  have complement_smooth:
      "smooth_on ?outer
        (\<lambda>z. 1 - slp_global_cutoff.slp_scaled_cutoff delta c z)"
    by (rule smooth_on_minus[
          OF smooth_on_const scaled_smooth_outer outer_open])
  have shifted_smooth_outer:
      "smooth_on ?outer
        (\<lambda>z. slp_point_as_complex (z - c))"
    by (rule smooth_on_subset[OF slp_shifted_point_as_complex_smooth])
      (rule subset_UNIV)
  have shifted_nonzero:
      "0 \<notin> (\<lambda>z. slp_point_as_complex (z - c)) ` ?outer"
  proof
    assume membership:
      "0 \<in> (\<lambda>z. slp_point_as_complex (z - c)) ` ?outer"
    from membership show False
    proof (rule imageE)
      fix z
      assume z_outer: "z \<in> ?outer"
      assume zero_reverse: "0 = slp_point_as_complex (z - c)"
      have zero: "slp_point_as_complex (z - c) = 0"
        by (rule sym[OF zero_reverse])
      have difference_zero: "z - c = 0"
        using zero by (simp only: slp_point_as_complex_eq_zero_iff)
      have z_eq: "z = c"
        by (rule iffD2[OF eq_iff_diff_eq_0 difference_zero])
      have z_not_singleton: "z \<notin> {c}"
      proof
        assume z_in_singleton: "z \<in> {c}"
        show False
          by (rule DiffD2[OF z_outer z_in_singleton])
      qed
      have z_not_c: "z \<noteq> c"
      proof
        assume z_eq_again: "z = c"
        have z_in_singleton: "z \<in> {c}"
          unfolding z_eq_again by (rule singletonI)
        show False
          by (rule notE[OF z_not_singleton z_in_singleton])
      qed
      show False
        by (rule notE[OF z_not_c z_eq])
    qed
  qed
  have inverse_smooth:
      "smooth_on ?outer
        (\<lambda>z. inverse (slp_point_as_complex (z - c)))"
    by (rule smooth_on_inverse[
          OF shifted_smooth_outer shifted_nonzero outer_open])
  have scaled_product_smooth:
      "smooth_on ?outer
        (\<lambda>z.
          (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *\<^sub>R
            inverse (slp_point_as_complex (z - c)))"
    by (rule smooth_on_scaleR[
          OF complement_smooth inverse_smooth outer_open])
  have coefficient_eq:
      "slp_global_far_coefficient delta c =
        (\<lambda>z.
          (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *\<^sub>R
            inverse (slp_point_as_complex (z - c)))"
  proof (rule ext)
    fix z
    show "slp_global_far_coefficient delta c z =
        (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *\<^sub>R
          inverse (slp_point_as_complex (z - c))"
      unfolding slp_global_far_coefficient_def
      by (simp only: scaleR_conv_of_real)
  qed
  have outer_smooth:
      "smooth_on ?outer (slp_global_far_coefficient delta c)"
    unfolding coefficient_eq
    by (rule scaled_product_smooth)

  have cover: "?inner \<union> ?outer = UNIV"
  proof (rule equalityI)
    show "?inner \<union> ?outer \<subseteq> UNIV"
      by (rule subset_UNIV)
    show "UNIV \<subseteq> ?inner \<union> ?outer"
    proof (rule subsetI)
      fix z :: slp_point
      assume "z \<in> UNIV"
      show "z \<in> ?inner \<union> ?outer"
      proof (cases "z = c")
        case True
        have "dist z c < delta"
          using delta_positive True by (simp only: dist_self)
        then have "z \<in> ?inner"
          by (simp only: mem_ball dist_commute)
        then show ?thesis
          by (rule UnI1)
      next
        case False
        have z_not_singleton: "z \<notin> {c}"
        proof
          assume z_in_singleton: "z \<in> {c}"
          have z_eq: "z = c"
            by (rule singletonD[OF z_in_singleton])
          show False
            by (rule notE[OF False z_eq])
        qed
        have "z \<in> ?outer"
          by (rule DiffI[OF UNIV_I z_not_singleton])
        then show ?thesis
          by (rule UnI2)
      qed
    qed
  qed
  have union_smooth:
      "smooth_on (?inner \<union> ?outer)
        (slp_global_far_coefficient delta c)"
    by (rule smooth_on_open_Un[
          OF inner_smooth outer_smooth inner_open outer_open])
  show ?thesis
    using union_smooth unfolding cover .
qed

theorem slp_global_far_product_test_function:
  assumes delta_positive: "0 < delta"
    and f_test: "slp_test_function_on UNIV f"
  shows
    "slp_test_function_on UNIV
      (slp_global_cutoff.slp_far_product delta c f)"
proof -
  have product_test:
      "slp_test_function_on UNIV
        (\<lambda>z. slp_global_far_coefficient delta c z * f z)"
    by (rule slp_test_function_on_mult_left[
          OF slp_global_far_coefficient_smooth[OF delta_positive] f_test])
  have far_product_eq:
      "slp_global_cutoff.slp_far_product delta c f =
        (\<lambda>z. slp_global_far_coefficient delta c z * f z)"
  proof (rule ext)
    fix z
    show "slp_global_cutoff.slp_far_product delta c f z =
        slp_global_far_coefficient delta c z * f z"
      unfolding slp_global_far_coefficient_def
        slp_global_cutoff.slp_far_product_def
      by (rule refl)
  qed
  from product_test show ?thesis
    unfolding far_product_eq .
qed

end
