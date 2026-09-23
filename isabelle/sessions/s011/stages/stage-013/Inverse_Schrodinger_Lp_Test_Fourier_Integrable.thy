theory Inverse_Schrodinger_Lp_Test_Fourier_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Test_Fourier_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Fourier integrability for compactly supported smooth inputs\<close>

lemma slp_inverse_one_plus_square_integrable:
  "integrable lborel (\<lambda>x::real. inverse (1 + x^2))"
proof -
  let ?h = "\<lambda>x::real. inverse (1 + x^2)"
  have positive: "0 < 1 + x^2" for x::real
    by (rule add_pos_nonneg) simp_all
  have integrable_interval:
      "set_integrable lborel (einterval (-\<infinity>) \<infinity>) ?h"
  proof (rule interval_integral_FTC_nonneg(1)[where F=arctan
        and A="- (pi/2)" and B="pi/2"])
    show "(-\<infinity>::ereal) < \<infinity>" by simp
    show "DERIV arctan x :> ?h x"
      if "(-\<infinity>::ereal) < ereal x" "ereal x < \<infinity>" for x
      by (rule DERIV_arctan)
    show "isCont ?h x"
      if "(-\<infinity>::ereal) < ereal x" "ereal x < \<infinity>" for x
      using positive[of x] by (intro continuous_intros) auto
    show "AE x in lborel. (-\<infinity>::ereal) < ereal x \<longrightarrow>
        ereal x < \<infinity> \<longrightarrow> 0 \<le> ?h x"
      using positive by (intro AE_I2) simp
    show "((arctan \<circ> real_of_ereal) \<longlongrightarrow> - (pi/2)) (at_right (-\<infinity>))"
      by (simp only: ereal_tendsto_simps1(4)) (rule tendsto_arctan_at_bot)
    show "((arctan \<circ> real_of_ereal) \<longlongrightarrow> pi/2) (at_left \<infinity>)"
      by (simp only: ereal_tendsto_simps1(3)) (rule tendsto_arctan_at_top)
  qed
  show ?thesis using integrable_interval by (simp add: einterval_eq_UNIV set_integrable_def)
qed

lemma slp_planar_product_weight_integrable:
  "integrable lborel (\<lambda>xi::slp_point.
    inverse (1 + (xi $ 0)^2) * inverse (1 + (xi $ 1)^2))"
proof -
  let ?P = "PiM (UNIV::2 set) (\<lambda>_. (lborel::real measure))"
  let ?V = "\<lambda>omega::2 \<Rightarrow> real. \<chi> i. omega i"
  let ?h = "\<lambda>x::real. inverse (1 + x^2)"
  let ?g = "\<lambda>xi::slp_point. \<Prod>i\<in>UNIV. ?h (xi $ i)"
  interpret scalar: product_sigma_finite "\<lambda>_::2. (lborel::real measure)"
    by standard
  have vector_measurable: "?V \<in> measurable ?P borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have planar_borel: "?g \<in> borel_measurable (borel::slp_point measure)"
    by measurable
  have product_integrable: "integrable ?P (\<lambda>omega. \<Prod>i\<in>UNIV. ?h (omega i))"
    by (rule scalar.product_integrable_prod)
      (simp_all add: slp_inverse_one_plus_square_integrable)
  have distribution_integrable: "integrable (distr ?P borel ?V) ?g"
    using integrable_distr_eq[OF vector_measurable planar_borel] product_integrable
    by simp
  have planar_integrable: "integrable lborel ?g"
    using distribution_integrable
    by (simp only: slp_lborel_cartesian_vector_product[where 'n=2])
  have universe_two: "(UNIV::2 set) = {0,1}" using UNIV_2 by auto
  show ?thesis using planar_integrable by (simp add: universe_two)
qed

lemma slp_test_fourier_integrable:
  fixes f :: slp_scalar_field
  assumes f_test: "slp_test_function_on UNIV f"
  shows "integrable lborel (slp_fourier_transform f)"
proof -
  let ?w = "\<lambda>xi::slp_point.
    inverse (1 + (xi $ 0)^2) * inverse (1 + (xi $ 1)^2)"
  obtain C where C_nonnegative: "0 \<le> C"
    and bound: "\<And>xi. norm (slp_fourier_transform f xi) \<le> C * ?w xi"
    using slp_test_fourier_product_decay[OF f_test] by blast
  have f_integrable: "integrable lborel f"
    by (rule slp_test_function_integrable_bounded(1)[OF f_test])
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_integrable by measurable
  have transform_measurable: "slp_fourier_transform f \<in> borel_measurable lborel"
    by (rule slp_fourier_transform_measurable[OF f_measurable])
  have majorant_integrable: "integrable lborel (\<lambda>xi. C * ?w xi)"
    by (rule Bochner_Integration.integrable_mult_right[OF slp_planar_product_weight_integrable])
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable transform_measurable])
    show "AE xi in lborel. norm (slp_fourier_transform f xi) \<le> norm (C * ?w xi)"
    proof (rule AE_I2)
      fix xi
      have "norm (slp_fourier_transform f xi) \<le> C * ?w xi" by (rule bound)
      also have "... \<le> norm (C * ?w xi)" by simp
      finally show "norm (slp_fourier_transform f xi) \<le> norm (C * ?w xi)" .
    qed
  qed
qed

end
