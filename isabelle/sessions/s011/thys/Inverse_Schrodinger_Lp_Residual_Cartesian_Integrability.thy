theory Inverse_Schrodinger_Lp_Residual_Cartesian_Integrability
  imports Inverse_Schrodinger_Lp_Residual_Cartesian_QRL
begin

section \<open>Measurability and integrability of the Cartesian residual phase\<close>

lemma slp_signed_residual_cartesian_measurable:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_sign:
    "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
  shows
    "(\<lambda>x. slp_signed_residual epsilon
      (slp_complex_family_unpack x)) \<in>
      borel_measurable
        (lborel :: (real^((unit + 'i) \<times> bool)) measure)"
proof -
  have distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
    using distinguished_sign by auto
  have split_bounded:
    "bounded_linear (slp_signed_cartesian_split epsilon)"
    using slp_signed_cartesian_split_linear[where epsilon = epsilon]
    by (simp add: linear_conv_bounded_linear)
  have split_continuous:
    "continuous_on UNIV (slp_signed_cartesian_split epsilon)"
    by (rule linear_continuous_on[OF split_bounded])
  have split_borel:
    "slp_signed_cartesian_split epsilon \<in>
      borel_measurable
        (borel :: (real^((unit + 'i) \<times> bool)) measure)"
    by (rule borel_measurable_continuous_onI[OF split_continuous])
  have split_measurable:
    "slp_signed_cartesian_split epsilon \<in>
      measurable
        (lborel :: (real^((unit + 'i) \<times> bool)) measure)
        (lborel :: (real^((unit + 'i) \<times> bool)) measure)"
    using split_borel by simp
  have coordinates_measurable:
    "(slp_signed_cartesian_to_product \<circ>
        slp_signed_cartesian_split epsilon) \<in>
      measurable
        (lborel :: (real^((unit + 'i) \<times> bool)) measure)
        (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
    by (rule measurable_comp[
        OF split_measurable slp_signed_cartesian_to_product_measurable])
  have product_phase_measurable:
    "(\<lambda>cu. slp_signed_residual epsilon
      (slp_signed_coordinate_join epsilon
        (slp_complex_coordinate_unpack (fst cu),
          slp_complex_family_unpack (snd cu)))) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)"
    by (rule slp_signed_residual_product_measurable[where epsilon = epsilon])
      (rule distinguished_sign)
  have composed_measurable:
    "(\<lambda>x. slp_signed_residual epsilon
      (slp_signed_coordinate_join epsilon
        (slp_complex_coordinate_unpack
            (fst (slp_signed_cartesian_to_product
              (slp_signed_cartesian_split epsilon x))),
          slp_complex_family_unpack
            (snd (slp_signed_cartesian_to_product
              (slp_signed_cartesian_split epsilon x)))))) \<in>
      borel_measurable
        (lborel :: (real^((unit + 'i) \<times> bool)) measure)"
    using measurable_compose[
      OF coordinates_measurable product_phase_measurable]
    by (simp only: o_def)
  have residual_identity:
    "slp_signed_residual epsilon
        (slp_signed_coordinate_join epsilon
          (slp_complex_coordinate_unpack
              (fst (slp_signed_cartesian_to_product
                (slp_signed_cartesian_split epsilon x))),
            slp_complex_family_unpack
              (snd (slp_signed_cartesian_to_product
                (slp_signed_cartesian_split epsilon x))))) =
      slp_signed_residual epsilon (slp_complex_family_unpack x)"
    for x
    by (rule slp_signed_cartesian_split_product_residual[
        where epsilon = epsilon and x = x])
      (rule distinguished_nonzero)
  show ?thesis
    using composed_measurable
    by (simp only: residual_identity)
qed

theorem slp_signed_residual_cartesian_integrable:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
    and F :: "real^((unit + 'i) \<times> bool) \<Rightarrow> complex"
    and omega :: real
  assumes distinguished_sign:
      "epsilon (Inl ()) = -1 \<or> epsilon (Inl ()) = 1"
    and F_integrable: "integrable lborel F"
  shows
    "integrable lborel
      (\<lambda>x. exp (\<i> * of_real
        (omega * slp_signed_residual epsilon
          (slp_complex_family_unpack x))) * F x)"
proof (rule Bochner_Integration.integrable_bound[OF F_integrable])
  have F_measurable:
    "F \<in> borel_measurable
      (lborel :: (real^((unit + 'i) \<times> bool)) measure)"
    using F_integrable by measurable
  have phase_measurable:
    "(\<lambda>x. slp_signed_residual epsilon
      (slp_complex_family_unpack x)) \<in>
      borel_measurable
        (lborel :: (real^((unit + 'i) \<times> bool)) measure)"
    by (rule slp_signed_residual_cartesian_measurable[
        where epsilon = epsilon])
      (rule distinguished_sign)
  show
    "(\<lambda>x. exp (\<i> * of_real
        (omega * slp_signed_residual epsilon
          (slp_complex_family_unpack x))) * F x) \<in>
      borel_measurable
        (lborel :: (real^((unit + 'i) \<times> bool)) measure)"
    using phase_measurable F_measurable by measurable
  show
    "AE x in lborel.
      norm (exp (\<i> * of_real
        (omega * slp_signed_residual epsilon
          (slp_complex_family_unpack x))) * F x) \<le> norm (F x)"
    by (simp only: norm_mult norm_exp_i_times mult_1_left order_refl
        eventually_True)
qed

end
