theory Inverse_Schrodinger_Lp_Oscillatory_Cauchy
  imports
    Inverse_Schrodinger_Lp_Cauchy_Transform
    Inverse_Schrodinger_Lp_Center_Average_Physical
    "Paper_ISLP_AIM_Planar_Hardy_Littlewood_Sobolev.AIM_Planar_Hardy_Littlewood_Sobolev_Interface"
begin

section \<open>The two conjugated Cauchy operators\<close>

definition slp_oscillatory_modulation ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field"
where
  "slp_oscillatory_modulation tau c f z =
    slp_center_kernel tau c z * f z"

definition slp_partial_psi_inverse ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field"
where
  "slp_partial_psi_inverse tau c f =
    slp_partial_inverse (slp_oscillatory_modulation tau c f)"

definition slp_dbar_psi_inverse ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field"
where
  "slp_dbar_psi_inverse tau c f =
    slp_dbar_inverse (slp_oscillatory_modulation (- tau) c f)"

lemma slp_center_kernel_norm [simp]:
  "norm (slp_center_kernel tau c z) = 1"
  unfolding slp_center_kernel_def
  by (simp only: norm_exp_i_times)

lemma slp_center_kernel_nonzero [simp]:
  "slp_center_kernel tau c z \<noteq> 0"
  unfolding slp_center_kernel_def by simp

lemma slp_center_kernel_conjugate [simp]:
  "cnj (slp_center_kernel tau c z) = slp_center_kernel (- tau) c z"
  unfolding slp_center_kernel_def
  by (simp add: exp_cnj algebra_simps)

lemma slp_center_kernel_opposite_product [simp]:
  "slp_center_kernel (- tau) c z * slp_center_kernel tau c z = 1"
proof -
  have exponent_sum:
    "\<i> * of_real ((- tau) * slp_center_phase c z) +
        \<i> * of_real (tau * slp_center_phase c z) = 0"
    by (simp add: algebra_simps)
  show ?thesis
    unfolding slp_center_kernel_def
    using exponent_sum
    by (simp only: exp_add[symmetric] exp_zero)
qed

lemma slp_center_kernel_product_opposite [simp]:
  "slp_center_kernel tau c z * slp_center_kernel (- tau) c z = 1"
  using slp_center_kernel_opposite_product[of tau c z]
  by (simp only: mult.commute)

lemma slp_oscillatory_modulation_norm [simp]:
  "norm (slp_oscillatory_modulation tau c f z) = norm (f z)"
  unfolding slp_oscillatory_modulation_def
  by (simp only: norm_mult slp_center_kernel_norm mult_1_left)

lemma slp_oscillatory_modulation_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_oscillatory_modulation tau c f \<in>
    borel_measurable lborel"
  unfolding slp_oscillatory_modulation_def
  using slp_center_kernel_measurable[of tau c] f_measurable
  by measurable

lemma slp_oscillatory_modulation_inverse [simp]:
  "slp_oscillatory_modulation (- tau) c
      (slp_oscillatory_modulation tau c f) = f"
  by (rule ext)
    (simp add: slp_oscillatory_modulation_def algebra_simps)

lemma slp_oscillatory_modulation_measurable_iff [simp]:
  "slp_oscillatory_modulation tau c f \<in> borel_measurable lborel
    \<longleftrightarrow> f \<in> borel_measurable lborel"
proof
  assume modulated_measurable:
    "slp_oscillatory_modulation tau c f \<in> borel_measurable lborel"
  have "slp_oscillatory_modulation (- tau) c
      (slp_oscillatory_modulation tau c f) \<in> borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable[OF modulated_measurable])
  then show "f \<in> borel_measurable lborel"
    by simp
next
  assume "f \<in> borel_measurable lborel"
  then show "slp_oscillatory_modulation tau c f \<in>
      borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable)
qed

lemma slp_oscillatory_modulation_lp_iff [simp]:
  "aim_complex_lp_on_plane p (slp_oscillatory_modulation tau c f)
    \<longleftrightarrow> aim_complex_lp_on_plane p f"
proof -
  have measurable_iff:
    "slp_oscillatory_modulation tau c f \<in> borel_measurable lborel
      \<longleftrightarrow> f \<in> borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable_iff)
  have power_integrable_iff:
    "integrable lborel
        (\<lambda>x. norm (slp_oscillatory_modulation tau c f x) powr p)
      \<longleftrightarrow> integrable lborel (\<lambda>x. norm (f x) powr p)"
    by (simp only: slp_oscillatory_modulation_norm)
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using measurable_iff power_integrable_iff by blast
qed

lemma slp_oscillatory_modulation_lp_norm [simp]:
  "aim_complex_lp_norm p (slp_oscillatory_modulation tau c f) =
    aim_complex_lp_norm p f"
  unfolding aim_complex_lp_norm_def
  by simp

lemma slp_oscillatory_modulation_nonzero_set [simp]:
  "{z. slp_oscillatory_modulation tau c f z \<noteq> 0} =
    {z. f z \<noteq> 0}"
  unfolding slp_oscillatory_modulation_def
  by auto

lemma slp_oscillatory_modulation_conjugate [simp]:
  "cnj (slp_oscillatory_modulation tau c f z) =
    slp_oscillatory_modulation (- tau) c (\<lambda>x. cnj (f x)) z"
  unfolding slp_oscillatory_modulation_def
  by simp

lemma slp_partial_psi_inverse_eq:
  "slp_partial_psi_inverse tau c f z =
    slp_cauchy_transform SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c f) z"
  unfolding slp_partial_psi_inverse_def by simp

lemma slp_dbar_psi_inverse_eq:
  "slp_dbar_psi_inverse tau c f z =
    slp_cauchy_transform SLP_Dbar_Inverse
      (slp_oscillatory_modulation (- tau) c f) z"
  unfolding slp_dbar_psi_inverse_def by simp

lemma slp_partial_psi_integrand_eq:
  "slp_cauchy_integrand SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c f) z y =
    slp_center_kernel tau c y * f y *
      slp_cauchy_kernel SLP_Partial_Inverse z y"
  unfolding slp_cauchy_integrand_def slp_oscillatory_modulation_def
  by (rule refl)

lemma slp_dbar_psi_integrand_eq:
  "slp_cauchy_integrand SLP_Dbar_Inverse
      (slp_oscillatory_modulation (- tau) c f) z y =
    slp_center_kernel (- tau) c y * f y *
      slp_cauchy_kernel SLP_Dbar_Inverse z y"
  unfolding slp_cauchy_integrand_def slp_oscillatory_modulation_def
  by (rule refl)

end
