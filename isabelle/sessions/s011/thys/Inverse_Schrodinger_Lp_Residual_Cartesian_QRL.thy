theory Inverse_Schrodinger_Lp_Residual_Cartesian_QRL
  imports
    Inverse_Schrodinger_Lp_Residual_Matrix_QRL
    Inverse_Schrodinger_Lp_Passive_Shear_Transport
begin

section \<open>Residual decay in the original packed coordinates\<close>

lemma slp_signed_complex_pair_unpack_pack:
  fixes cu :: "complex \<times> ('i::finite \<Rightarrow> complex)"
  shows
    "(slp_complex_coordinate_unpack
        (fst (slp_signed_complex_pair_pack cu)),
      slp_complex_family_unpack
        (snd (slp_signed_complex_pair_pack cu))) = cu"
  by (cases cu)
    (simp add: slp_complex_coordinate_unpack_def
      slp_signed_complex_pair_pack_def slp_complex_family_unpack_def
      complex_eq_iff fun_eq_iff)

definition slp_signed_passive_shear_shift ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow>
    real^('i \<times> bool) \<Rightarrow> real^bool"
where
  "slp_signed_passive_shear_shift epsilon u =
    fst (slp_signed_cartesian_to_product
      (slp_signed_cartesian_split epsilon
        (slp_signed_product_to_cartesian (0, u))))"

lemma slp_signed_passive_shear_shift_linear:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  shows "linear (slp_signed_passive_shear_shift epsilon)"
proof -
  let ?embed = "\<lambda>u :: real^('i \<times> bool). (0, u)"
  let ?T = "slp_signed_cartesian_to_product \<circ>
    (slp_signed_cartesian_split epsilon \<circ>
      (slp_signed_product_to_cartesian \<circ> ?embed))"
  have embed_linear: "linear ?embed"
    by (rule linearI; simp)
  have product_linear:
    "linear (slp_signed_product_to_cartesian \<circ> ?embed)"
    by (rule linear_compose[
        OF embed_linear slp_signed_product_to_cartesian_linear])
  have split_linear:
    "linear (slp_signed_cartesian_split epsilon \<circ>
      (slp_signed_product_to_cartesian \<circ> ?embed))"
    by (rule linear_compose[
        OF product_linear slp_signed_cartesian_split_linear])
  have T_linear: "linear ?T"
    by (rule linear_compose[
        OF split_linear slp_signed_cartesian_to_product_linear])
  interpret T: linear ?T
    by (rule T_linear)
  show ?thesis
  proof (rule linearI)
    show "slp_signed_passive_shear_shift epsilon (x + y) =
        slp_signed_passive_shear_shift epsilon x +
          slp_signed_passive_shear_shift epsilon y"
      for x y :: "real^('i \<times> bool)"
      using T.add[of x y]
      by (simp add: slp_signed_passive_shear_shift_def)
    show "slp_signed_passive_shear_shift epsilon (r *\<^sub>R x) =
        r *\<^sub>R slp_signed_passive_shear_shift epsilon x"
      for r and x :: "real^('i \<times> bool)"
      using T.scale[of r x]
      by (simp add: slp_signed_passive_shear_shift_def)
  qed
qed

lemma slp_signed_passive_shear_shift_measurable:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  shows "slp_signed_passive_shear_shift epsilon \<in>
    borel_measurable (lborel :: (real^('i::finite \<times> bool)) measure)"
proof -
  have bounded: "bounded_linear (slp_signed_passive_shear_shift epsilon)"
    using slp_signed_passive_shear_shift_linear
    by (simp add: linear_conv_bounded_linear)
  have continuous:
    "continuous_on UNIV (slp_signed_passive_shear_shift epsilon)"
    by (rule linear_continuous_on[OF bounded])
  show ?thesis
    using borel_measurable_continuous_onI[OF continuous] by simp
qed

lemma slp_signed_product_unpack:
  "slp_signed_family_to_pair
      (slp_complex_family_unpack
        (slp_signed_product_to_cartesian cu)) =
    (slp_complex_coordinate_unpack (fst cu),
      slp_complex_family_unpack (snd cu))"
  by (cases cu)
    (simp add: slp_signed_family_to_pair_def
      slp_complex_family_unpack_def slp_signed_product_to_cartesian_def
      slp_complex_coordinate_unpack_def fun_eq_iff)

lemma slp_signed_cartesian_split_product_shear:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  shows
    "slp_signed_cartesian_to_product
        (slp_signed_cartesian_split epsilon
          (slp_signed_product_to_cartesian cu)) =
      (slp_signed_passive_shear_shift epsilon (snd cu) +
          epsilon (Inl ()) *\<^sub>R fst cu,
        snd cu)"
proof -
  let ?T = "slp_signed_cartesian_to_product \<circ>
    (slp_signed_cartesian_split epsilon \<circ>
      slp_signed_product_to_cartesian)"
  have T_linear: "linear ?T"
  proof -
    have inner_linear:
      "linear (slp_signed_cartesian_split epsilon \<circ>
        slp_signed_product_to_cartesian)"
      by (rule linear_compose[OF slp_signed_product_to_cartesian_linear
          slp_signed_cartesian_split_linear])
    show ?thesis
      by (rule linear_compose[
          OF inner_linear slp_signed_cartesian_to_product_linear])
  qed
  interpret T: linear ?T
    by (rule T_linear)
  have decomposition:
    "cu = (fst cu, 0) + (0, snd cu)"
    by simp
  have T_decomposition:
    "?T cu = ?T (fst cu, 0) + ?T (0, snd cu)"
    using T.add[of "(fst cu, 0)" "(0, snd cu)"] decomposition
    by simp
  have passive_only:
    "?T (fst cu, 0) = (epsilon (Inl ()) *\<^sub>R fst cu, 0)"
    unfolding o_def
    by (simp add: slp_signed_cartesian_split_product_coordinates
        slp_signed_complex_pair_pack_def slp_signed_coordinate_split_def
        slp_signed_output_sum_type slp_signed_tail_output_def
        slp_complex_family_unpack_def slp_signed_product_to_cartesian_def
        vec_eq_iff)
  have active_only:
    "?T (0, snd cu) =
      (slp_signed_passive_shear_shift epsilon (snd cu), snd cu)"
  proof (rule prod_eqI)
    show "fst (?T (0, snd cu)) =
        fst (slp_signed_passive_shear_shift epsilon (snd cu), snd cu)"
      by (simp add: slp_signed_passive_shear_shift_def)
    show "snd (?T (0, snd cu)) =
        snd (slp_signed_passive_shear_shift epsilon (snd cu), snd cu)"
      unfolding o_def
      by (simp add: slp_signed_cartesian_split_product_coordinates
          slp_signed_complex_pair_pack_def slp_signed_coordinate_split_def
          slp_complex_family_unpack_def slp_signed_product_to_cartesian_def
          vec_eq_iff)
  qed
  show ?thesis
    using T_decomposition passive_only active_only
    by (simp add: o_def add.commute)
qed

lemma slp_signed_cartesian_split_product_residual:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
  shows
    "slp_signed_residual epsilon
        (slp_signed_coordinate_join epsilon
          (slp_complex_coordinate_unpack
              (fst (slp_signed_cartesian_to_product
                (slp_signed_cartesian_split epsilon x))),
            slp_complex_family_unpack
              (snd (slp_signed_cartesian_to_product
                (slp_signed_cartesian_split epsilon x))))) =
      slp_signed_residual epsilon (slp_complex_family_unpack x)"
proof -
  have packed_coordinates:
    "slp_signed_cartesian_to_product
        (slp_signed_cartesian_split epsilon x) =
      slp_signed_complex_pair_pack
        (slp_signed_coordinate_split epsilon
          (slp_complex_family_unpack x))"
    by (rule slp_signed_cartesian_split_product_coordinates)
  have pair_coordinates:
    "(slp_complex_coordinate_unpack
        (fst (slp_signed_cartesian_to_product
          (slp_signed_cartesian_split epsilon x))),
      slp_complex_family_unpack
        (snd (slp_signed_cartesian_to_product
          (slp_signed_cartesian_split epsilon x)))) =
      slp_signed_coordinate_split epsilon (slp_complex_family_unpack x)"
    using packed_coordinates
      slp_signed_complex_pair_unpack_pack[
        where cu =
          "slp_signed_coordinate_split epsilon
            (slp_complex_family_unpack x)"]
    by simp
  have joined_coordinates:
    "slp_signed_coordinate_join epsilon
        (slp_complex_coordinate_unpack
          (fst (slp_signed_cartesian_to_product
            (slp_signed_cartesian_split epsilon x))),
        slp_complex_family_unpack
          (snd (slp_signed_cartesian_to_product
            (slp_signed_cartesian_split epsilon x)))) =
      slp_complex_family_unpack x"
  proof -
    have
      "slp_signed_coordinate_join epsilon
          (slp_complex_coordinate_unpack
            (fst (slp_signed_cartesian_to_product
              (slp_signed_cartesian_split epsilon x))),
          slp_complex_family_unpack
            (snd (slp_signed_cartesian_to_product
              (slp_signed_cartesian_split epsilon x)))) =
        slp_signed_coordinate_join epsilon
          (slp_signed_coordinate_split epsilon
            (slp_complex_family_unpack x))"
      using pair_coordinates by simp
    also have "... = slp_complex_family_unpack x"
      by (rule slp_signed_coordinate_join_split[
          where epsilon = epsilon and y = "slp_complex_family_unpack x"])
        (rule distinguished_nonzero)
    finally show ?thesis .
  qed
  show ?thesis
    using joined_coordinates by simp
qed

lemma slp_signed_residual_product_measurable:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
  shows
    "(\<lambda>cu. slp_signed_residual epsilon
      (slp_signed_coordinate_join epsilon
        (slp_complex_coordinate_unpack (fst cu),
          slp_complex_family_unpack (snd cu)))) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
proof -
  have phase_identity:
    "slp_signed_residual epsilon
        (slp_signed_coordinate_join epsilon
          (slp_complex_coordinate_unpack c,
            slp_complex_family_unpack u)) =
      inner u (slp_signed_active_hessian epsilon *v u) / 2 +
        inner (slp_signed_passive_coefficient epsilon c) u +
        slp_signed_passive_constant epsilon c"
    for c u
    by (rule slp_signed_residual_product_phase[
        where epsilon = epsilon and c = c and u = u])
      (rule distinguished_sign)
  have rhs_measurable:
    "(\<lambda>cu.
      inner (snd cu) (slp_signed_active_hessian epsilon *v snd cu) / 2 +
        inner (slp_signed_passive_coefficient epsilon (fst cu)) (snd cu) +
        slp_signed_passive_constant epsilon (fst cu)) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
  proof -
    have fst_continuous:
      "continuous_on UNIV
        (\<lambda>cu :: (real^bool) \<times> (real^('i \<times> bool)). fst cu)"
      by (intro continuous_intros)
    have fst_measurable:
      "(\<lambda>cu :: (real^bool) \<times> (real^('i \<times> bool)). fst cu) \<in>
        borel_measurable
          (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
      using borel_measurable_continuous_onI[OF fst_continuous] by simp
    have fst_to_lborel:
      "(\<lambda>cu :: (real^bool) \<times> (real^('i \<times> bool)). fst cu) \<in>
        measurable
          (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)
          (lborel :: (real^bool) measure)"
      using fst_measurable by simp
    have snd_continuous:
      "continuous_on UNIV
        (\<lambda>cu :: (real^bool) \<times> (real^('i \<times> bool)). snd cu)"
      by (intro continuous_intros)
    have snd_measurable:
      "(\<lambda>cu :: (real^bool) \<times> (real^('i \<times> bool)). snd cu) \<in>
        borel_measurable
          (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
      using borel_measurable_continuous_onI[OF snd_continuous] by simp
    have snd_to_lborel:
      "(\<lambda>cu :: (real^bool) \<times> (real^('i \<times> bool)). snd cu) \<in>
        measurable
          (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)
          (lborel :: (real^('i \<times> bool)) measure)"
      using snd_measurable by simp
    have coefficient_after_fst:
      "(\<lambda>cu :: (real^bool) \<times> (real^('i \<times> bool)).
        slp_signed_passive_coefficient epsilon (fst cu)) \<in>
        borel_measurable
          (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
      by (rule measurable_compose[OF fst_to_lborel
          slp_signed_passive_coefficient_measurable])
    have constant_after_fst:
      "(\<lambda>cu :: (real^bool) \<times> (real^('i \<times> bool)).
        slp_signed_passive_constant epsilon (fst cu)) \<in>
        borel_measurable
          (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
      by (rule measurable_compose[OF fst_to_lborel
          slp_signed_passive_constant_measurable])
    have hessian_after_snd:
      "(\<lambda>cu :: (real^bool) \<times> (real^('i \<times> bool)).
        slp_signed_active_hessian epsilon *v snd cu) \<in>
        borel_measurable
          (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
    proof -
      have hessian_continuous:
        "continuous_on UNIV
          (\<lambda>u :: real^('i \<times> bool).
            slp_signed_active_hessian epsilon *v u)"
        by (intro continuous_intros)
      have hessian_measurable:
        "(\<lambda>u :: real^('i \<times> bool).
          slp_signed_active_hessian epsilon *v u) \<in>
          borel_measurable (lborel :: (real^('i \<times> bool)) measure)"
        using borel_measurable_continuous_onI[OF hessian_continuous] by simp
      show ?thesis
        by (rule measurable_compose[OF snd_to_lborel hessian_measurable])
    qed
    show ?thesis
      using snd_measurable coefficient_after_fst constant_after_fst
        hessian_after_snd
      by measurable
  qed
  show ?thesis
    using rhs_measurable
    by (simp only: phase_identity)
qed

theorem slp_signed_residual_cartesian_quadratic_decay:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
    and F :: "real^((unit + 'i) \<times> bool) \<Rightarrow> complex"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim TYPE('i \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE('i \<times> bool)"
    and signs: "\<And>k. epsilon k = -1 \<or> epsilon k = 1"
    and signed_sum: "(\<Sum>k\<in>UNIV. epsilon k) = 1"
    and F_integrable: "integrable lborel F"
  shows
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>x. exp (\<i> * of_real
          (omega * slp_signed_residual epsilon
            (slp_complex_family_unpack x))) * F x))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?a = "slp_signed_passive_shear_shift epsilon"
  let ?c = "epsilon (Inl ())"
  let ?cinv = "inverse ?c"
  let ?ainv = "\<lambda>u. (- ?cinv) *\<^sub>R ?a u"
  let ?B = "\<lambda>cu. F (slp_signed_product_to_cartesian cu)"
  let ?A = "\<lambda>cu.
    ?B (?ainv (snd cu) + ?cinv *\<^sub>R fst cu, snd cu)"
  let ?H = "\<lambda>omega. \<lambda>(c, u).
    exp (\<i> * of_real
      (omega * slp_signed_residual epsilon
        (slp_signed_coordinate_join epsilon
          (slp_complex_coordinate_unpack c,
            slp_complex_family_unpack u)))) * ?A (c, u)"

  have distinguished_sign: "?c = -1 \<or> ?c = 1"
    by (rule signs)
  have c_nonzero: "?c \<noteq> 0"
    using distinguished_sign by auto
  have cinv_nonzero: "?cinv \<noteq> 0"
    using c_nonzero by simp
  have a_measurable:
    "?a \<in> borel_measurable
      (lborel :: (real^('i \<times> bool)) measure)"
    by (rule slp_signed_passive_shear_shift_measurable)
  have ainv_measurable:
    "?ainv \<in> borel_measurable
      (lborel :: (real^('i \<times> bool)) measure)"
    using a_measurable by measurable
  have inverse_shear:
    "?ainv u + ?cinv *\<^sub>R (?a u + ?c *\<^sub>R x) = x"
    for u :: "real^('i \<times> bool)" and x :: "real^bool"
    using c_nonzero
    by (simp add: scaleR_add_right scaleR_scaleR)

  have F_measurable:
    "F \<in> borel_measurable
      (lborel :: (real^((unit + 'i) \<times> bool)) measure)"
    using F_integrable by measurable
  have B_measurable:
    "?B \<in> borel_measurable
      (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
    by (rule measurable_compose[
        OF slp_signed_product_to_cartesian_measurable F_measurable])
  have B_cartesian_integrable:
    "integrable lborel
      (\<lambda>x. ?B (slp_signed_cartesian_to_product x))"
    using F_integrable
    by (simp only: slp_signed_product_to_cartesian_to_product)
  have B_integrable: "integrable lborel ?B"
    by (rule iffD2[OF slp_signed_cartesian_product_integrable_iff[
        OF B_measurable] B_cartesian_integrable])
  have A_integrable: "integrable lborel ?A"
    by (rule slp_passive_affine_shear_integrable[
        where a = ?ainv and c = ?cinv and F = ?B,
        OF ainv_measurable cinv_nonzero B_integrable])
  have A_measurable:
    "?A \<in> borel_measurable
      (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
    using A_integrable by measurable
  have A_pair_eq:
    "(\<lambda>(c, u). ?A (c, u)) = ?A"
  proof (rule ext)
    fix cu :: "(real^bool) \<times> (real^('i \<times> bool))"
    show "(case cu of (c, u) \<Rightarrow> ?A (c, u)) = ?A cu"
      by (cases cu) simp
  qed
  have A_pair_integrable:
    "integrable lborel (\<lambda>(c, u). ?A (c, u))"
    using A_integrable by (simp only: A_pair_eq)

  have H_decay:
    "((\<lambda>omega. integral\<^sup>L lborel (?H omega))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_signed_residual_product_quadratic_decay[
        where epsilon = epsilon and F = "\<lambda>c u. ?A (c, u)",
        OF stationary_phase density signs signed_sum])
      (rule A_pair_integrable)
  have residual_measurable:
    "(\<lambda>cu. slp_signed_residual epsilon
      (slp_signed_coordinate_join epsilon
        (slp_complex_coordinate_unpack (fst cu),
          slp_complex_family_unpack (snd cu)))) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
    by (rule slp_signed_residual_product_measurable[
        where epsilon = epsilon])
      (rule distinguished_sign)
  have H_raw_measurable:
    "(\<lambda>cu. exp (\<i> * of_real
        (omega * slp_signed_residual epsilon
          (slp_signed_coordinate_join epsilon
            (slp_complex_coordinate_unpack (fst cu),
              slp_complex_family_unpack (snd cu))))) * ?A cu) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
    for omega
    using residual_measurable A_measurable by measurable
  have H_function_eq:
    "?H omega = (\<lambda>cu. exp (\<i> * of_real
        (omega * slp_signed_residual epsilon
          (slp_signed_coordinate_join epsilon
            (slp_complex_coordinate_unpack (fst cu),
              slp_complex_family_unpack (snd cu))))) * ?A cu)"
    for omega
  proof (rule ext)
    fix cu :: "(real^bool) \<times> (real^('i \<times> bool))"
    show "?H omega cu =
        exp (\<i> * of_real
          (omega * slp_signed_residual epsilon
            (slp_signed_coordinate_join epsilon
              (slp_complex_coordinate_unpack (fst cu),
                slp_complex_family_unpack (snd cu))))) * ?A cu"
      by (cases cu) simp
  qed
  have H_measurable:
    "?H omega \<in> borel_measurable
      (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
    for omega
    using H_raw_measurable[where omega = omega]
    by (simp only: H_function_eq)
  have H_integrable: "integrable lborel (?H omega)" for omega
  proof (rule Bochner_Integration.integrable_bound[
      OF A_integrable H_measurable])
    show "AE cu in lborel. norm (?H omega cu) \<le> norm (?A cu)"
    proof (rule AE_I2)
      fix cu
      show "norm (?H omega cu) \<le> norm (?A cu)"
        by (cases cu) (simp add: norm_mult norm_exp)
    qed
  qed

  have sheared_decay:
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>cu. ?H omega
          (?a (snd cu) + ?c *\<^sub>R fst cu, snd cu)))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_passive_affine_shear_tendsto_zero[
        where a = ?a and c = ?c and H = ?H,
        OF a_measurable c_nonzero H_integrable H_decay])

  have phase_after_shear:
    "slp_signed_residual epsilon
        (slp_signed_coordinate_join epsilon
          (slp_complex_coordinate_unpack
              (?a (snd cu) + ?c *\<^sub>R fst cu),
            slp_complex_family_unpack (snd cu))) =
      slp_signed_residual epsilon
        (slp_complex_family_unpack
          (slp_signed_product_to_cartesian cu))"
    for cu
  proof -
    have coordinates:
      "slp_signed_cartesian_to_product
          (slp_signed_cartesian_split epsilon
            (slp_signed_product_to_cartesian cu)) =
        (?a (snd cu) + ?c *\<^sub>R fst cu, snd cu)"
      by (rule slp_signed_cartesian_split_product_shear)
    have residual:
      "slp_signed_residual epsilon
          (slp_signed_coordinate_join epsilon
            (slp_complex_coordinate_unpack
                (fst (slp_signed_cartesian_to_product
                  (slp_signed_cartesian_split epsilon
                    (slp_signed_product_to_cartesian cu)))),
              slp_complex_family_unpack
                (snd (slp_signed_cartesian_to_product
                  (slp_signed_cartesian_split epsilon
                    (slp_signed_product_to_cartesian cu)))))) =
        slp_signed_residual epsilon
          (slp_complex_family_unpack
            (slp_signed_product_to_cartesian cu))"
      by (rule slp_signed_cartesian_split_product_residual[
          where epsilon = epsilon
            and x = "slp_signed_product_to_cartesian cu"])
        (rule c_nonzero)
    show ?thesis
      using residual coordinates by simp
  qed
  have amplitude_after_shear:
    "?A (?a (snd cu) + ?c *\<^sub>R fst cu, snd cu) = ?B cu"
    for cu
    using inverse_shear[of "snd cu" "fst cu"] by simp
  have H_after_shear:
    "?H omega (?a (snd cu) + ?c *\<^sub>R fst cu, snd cu) =
      exp (\<i> * of_real
        (omega * slp_signed_residual epsilon
          (slp_complex_family_unpack
            (slp_signed_product_to_cartesian cu)))) * ?B cu"
    for omega cu
    using phase_after_shear[of cu] amplitude_after_shear[of cu]
    by (cases cu) simp
  have product_decay:
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>cu. exp (\<i> * of_real
          (omega * slp_signed_residual epsilon
            (slp_complex_family_unpack
              (slp_signed_product_to_cartesian cu)))) * ?B cu))
      \<longlongrightarrow> 0) at_top"
    using sheared_decay by (simp only: H_after_shear)

  have G_integrable:
    "integrable lborel
      (\<lambda>cu. exp (\<i> * of_real
        (omega * slp_signed_residual epsilon
          (slp_complex_family_unpack
            (slp_signed_product_to_cartesian cu)))) * ?B cu)"
    for omega
  proof -
    have sheared_integrable:
      "integrable lborel
        (\<lambda>cu. ?H omega
          (?a (snd cu) + ?c *\<^sub>R fst cu, snd cu))"
      by (rule slp_passive_affine_shear_integrable[
          where a = ?a and c = ?c and F = "?H omega",
          OF a_measurable c_nonzero H_integrable])
    show ?thesis
      using sheared_integrable by (simp only: H_after_shear)
  qed
  have G_measurable:
    "(\<lambda>cu. exp (\<i> * of_real
        (omega * slp_signed_residual epsilon
          (slp_complex_family_unpack
            (slp_signed_product_to_cartesian cu)))) * ?B cu) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
    for omega
    using G_integrable[where omega = omega] by measurable
  have regrouped_integral:
    "integral\<^sup>L lborel
        (\<lambda>cu. exp (\<i> * of_real
          (omega * slp_signed_residual epsilon
            (slp_complex_family_unpack
              (slp_signed_product_to_cartesian cu)))) * ?B cu) =
      integral\<^sup>L lborel
        (\<lambda>x. exp (\<i> * of_real
          (omega * slp_signed_residual epsilon
            (slp_complex_family_unpack x))) * F x)"
    for omega
  proof -
    have transported:
      "integral\<^sup>L lborel
          (\<lambda>cu. exp (\<i> * of_real
            (omega * slp_signed_residual epsilon
              (slp_complex_family_unpack
                (slp_signed_product_to_cartesian cu)))) * ?B cu) =
        integral\<^sup>L lborel
          (\<lambda>x. exp (\<i> * of_real
            (omega * slp_signed_residual epsilon
              (slp_complex_family_unpack
                (slp_signed_product_to_cartesian
                  (slp_signed_cartesian_to_product x))))) *
              ?B (slp_signed_cartesian_to_product x))"
      by (rule slp_signed_cartesian_product_integral[
          OF G_measurable])
    show ?thesis
      using transported
      by (simp only: slp_signed_product_to_cartesian_to_product)
  qed
  show ?thesis
    using product_decay by (simp only: regrouped_integral)
qed

end
