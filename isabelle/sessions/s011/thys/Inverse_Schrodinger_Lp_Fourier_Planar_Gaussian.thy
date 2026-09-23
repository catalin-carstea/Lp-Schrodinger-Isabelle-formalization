theory Inverse_Schrodinger_Lp_Fourier_Planar_Gaussian
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Scaled_Gaussian"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cartesian_Lebesgue_Reindex"
begin

section \<open>The planar Gaussian as a finite coordinate product\<close>

definition slp_planar_scaled_gaussian ::
  "real \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_planar_scaled_gaussian a x =
    (\<Prod>i\<in>UNIV. slp_scaled_gaussian a (x $ i))"

lemma slp_planar_scaled_gaussian_measurable[measurable]:
  "slp_planar_scaled_gaussian a \<in> borel_measurable lborel"
  unfolding slp_planar_scaled_gaussian_def by measurable

lemma slp_planar_scaled_gaussian_pullback:
  "slp_planar_scaled_gaussian a (\<chi> i. omega i) =
    (\<Prod>i\<in>UNIV. slp_scaled_gaussian a (omega i))"
  by (simp add: slp_planar_scaled_gaussian_def)

lemma slp_planar_scaled_gaussian_integrable:
  assumes a: "0 < a"
  shows "integrable lborel (slp_planar_scaled_gaussian a)"
proof -
  let ?P =
    "PiM (UNIV::2 set) (\<lambda>_. (lborel :: real measure))"
  let ?V = "\<lambda>omega::2 \<Rightarrow> real. \<chi> i. omega i"
  interpret scalar:
    product_sigma_finite "\<lambda>_::2. (lborel :: real measure)"
    by standard
  have vector_measurable: "?V \<in> measurable ?P borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have planar_borel:
      "slp_planar_scaled_gaussian a \<in>
        borel_measurable (borel :: slp_point measure)"
    unfolding slp_planar_scaled_gaussian_def by measurable
  have product_integrable:
      "integrable ?P
        (\<lambda>omega. \<Prod>i\<in>UNIV.
          slp_scaled_gaussian a (omega i))"
    by (rule scalar.product_integrable_prod)
      (simp_all add: slp_scaled_gaussian_integrable[OF a])
  have distr_integrable:
      "integrable (distr ?P borel ?V)
        (slp_planar_scaled_gaussian a)"
    using integrable_distr_eq[OF vector_measurable planar_borel]
      product_integrable
    by (simp only: slp_planar_scaled_gaussian_pullback)
  show ?thesis
    using distr_integrable
    by (simp only:
        slp_lborel_cartesian_vector_product[where 'n=2])
qed

lemma slp_planar_scaled_gaussian_integral:
  assumes a: "0 < a"
  shows "integral\<^sup>L lborel (slp_planar_scaled_gaussian a) =
    (\<Prod>i\<in>(UNIV::2 set).
      of_real (sqrt (2 * pi)) /\<^sub>R sqrt a)"
proof -
  let ?P =
    "PiM (UNIV::2 set) (\<lambda>_. (lborel :: real measure))"
  let ?V = "\<lambda>omega::2 \<Rightarrow> real. \<chi> i. omega i"
  interpret scalar:
    product_sigma_finite "\<lambda>_::2. (lborel :: real measure)"
    by standard
  have vector_measurable: "?V \<in> measurable ?P borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have planar_borel:
      "slp_planar_scaled_gaussian a \<in>
        borel_measurable (borel :: slp_point measure)"
    unfolding slp_planar_scaled_gaussian_def by measurable
  have transported:
      "integral\<^sup>L (distr ?P borel ?V)
          (slp_planar_scaled_gaussian a) =
        integral\<^sup>L ?P
          (\<lambda>omega. \<Prod>i\<in>UNIV.
            slp_scaled_gaussian a (omega i))"
    using integral_distr[OF vector_measurable planar_borel]
    by (simp only: slp_planar_scaled_gaussian_pullback)
    have product_value:
      "integral\<^sup>L ?P
          (\<lambda>omega. \<Prod>i\<in>UNIV.
            slp_scaled_gaussian a (omega i)) =
        (\<Prod>i\<in>(UNIV::2 set).
          integral\<^sup>L lborel (slp_scaled_gaussian a))"
    by (rule scalar.product_integral_prod)
      (simp_all add: slp_scaled_gaussian_integrable[OF a])
  show ?thesis
    using transported product_value
      slp_scaled_gaussian_integral[OF a]
    by (simp only:
        slp_lborel_cartesian_vector_product[where 'n=2])
qed

lemma slp_planar_scaled_gaussian_phase_product:
  "slp_fourier_phase xi x * slp_planar_scaled_gaussian a x =
    (\<Prod>i\<in>UNIV.
      exp (\<i> * of_real (- (xi $ i) * (x $ i))) *
        slp_scaled_gaussian a (x $ i))"
proof -
  have exponent_identity:
      "\<i> * of_real (- inner x xi) =
        (\<Sum>i\<in>UNIV.
          \<i> * of_real (- (xi $ i) * (x $ i)))"
    unfolding inner_vec_def
    by (simp add: sum_distrib_left sum_negf mult.commute)
  have phase_product:
      "slp_fourier_phase xi x =
        (\<Prod>i\<in>UNIV.
          exp (\<i> * of_real (- (xi $ i) * (x $ i))))"
    unfolding slp_fourier_phase_def exponent_identity
    by (rule exp_sum) simp
  show ?thesis
    unfolding phase_product slp_planar_scaled_gaussian_def
    by (simp only: prod.distrib)
qed

lemma slp_planar_scaled_gaussian_fourier_product:
  assumes a: "0 < a"
  shows "slp_fourier_transform (slp_planar_scaled_gaussian a) xi =
    (\<Prod>i\<in>(UNIV::2 set).
      of_real
        (sqrt (2 * pi) *
          exp (- (((xi $ i) / sqrt a) ^ 2) / 2)) /\<^sub>R sqrt a)"
proof -
  let ?P =
    "PiM (UNIV::2 set) (\<lambda>_. (lborel :: real measure))"
  let ?V = "\<lambda>omega::2 \<Rightarrow> real. \<chi> i. omega i"
  let ?one =
    "\<lambda>i::2. \<lambda>y.
      exp (\<i> * of_real (- (xi $ i) * y)) *
        slp_scaled_gaussian a y"
  let ?integrand =
    "\<lambda>x. slp_fourier_phase xi x *
      slp_planar_scaled_gaussian a x"
  interpret scalar:
    product_sigma_finite "\<lambda>_::2. (lborel :: real measure)"
    by standard
  have vector_measurable: "?V \<in> measurable ?P borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have planar_integrable:
      "integrable lborel (slp_planar_scaled_gaussian a)"
    by (rule slp_planar_scaled_gaussian_integrable[OF a])
  have integrand_integrable: "integrable lborel ?integrand"
    by (rule slp_fourier_integrand_integrable[OF planar_integrable])
  have integrand_borel:
      "?integrand \<in> borel_measurable (borel :: slp_point measure)"
  proof -
    have measurable_sets:
        "borel_measurable (lborel :: slp_point measure) =
          borel_measurable (borel :: slp_point measure)"
      by (rule measurable_cong_sets)
        (rule sets_lborel, rule refl)
    show ?thesis
      using integrand_integrable[THEN borel_measurable_integrable]
      by (simp only: measurable_sets)
  qed
  have one_integrable:
      "integrable lborel (?one i)" for i
    by (rule slp_scaled_gaussian_fourier_integrable[OF a])
  have finite_two:
      "finite (UNIV :: 2 set)"
    by simp
  have pullback:
      "(\<lambda>omega. ?integrand (?V omega)) =
        (\<lambda>omega. \<Prod>i\<in>UNIV. ?one i (omega i))"
    by (rule ext)
      (simp only: slp_planar_scaled_gaussian_phase_product
        vec_lambda_beta)
  have transported:
      "integral\<^sup>L (distr ?P borel ?V) ?integrand =
        integral\<^sup>L ?P
          (\<lambda>omega. \<Prod>i\<in>UNIV. ?one i (omega i))"
    using integral_distr[OF vector_measurable integrand_borel]
    by (simp only: pullback)
  have product_value:
      "integral\<^sup>L ?P
          (\<lambda>omega. \<Prod>i\<in>UNIV. ?one i (omega i)) =
        (\<Prod>i\<in>(UNIV::2 set).
          integral\<^sup>L lborel (?one i))"
      by (rule scalar.product_integral_prod[OF finite_two])
        (simp_all only: one_integrable)
  have one_value:
      "integral\<^sup>L lborel (?one i) =
        of_real
          (sqrt (2 * pi) *
            exp (- (((xi $ i) / sqrt a) ^ 2) / 2)) /\<^sub>R sqrt a"
    for i
    by (rule slp_scaled_gaussian_fourier_integral[OF a])
  show ?thesis
    unfolding slp_fourier_transform_def
    using transported product_value one_value
    by (simp only:
        slp_lborel_cartesian_vector_product[where 'n=2])
qed

end
