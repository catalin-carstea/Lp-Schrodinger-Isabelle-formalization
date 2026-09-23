theory Inverse_Schrodinger_Lp_Fourier_Damped_Chirp_Integral_Product
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Damped_Chirp_Product"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cartesian_Lebesgue_Reindex"
begin

section \<open>Product-integral reduction for the damped center chirp\<close>

definition slp_damped_chirp_fourier_integrand ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex"
where
  "slp_damped_chirp_fourier_integrand eps tau xi x =
    exp (\<i> * of_real (- xi * x)) *
      slp_damped_chirp_1 eps tau x"

lemma slp_damped_chirp_fourier_integrand_measurable[measurable]:
  "slp_damped_chirp_fourier_integrand eps tau xi \<in>
    borel_measurable lborel"
  unfolding slp_damped_chirp_fourier_integrand_def by measurable

lemma slp_damped_chirp_fourier_integrand_integrable:
  assumes eps: "0 < eps"
  shows "integrable lborel
    (slp_damped_chirp_fourier_integrand eps tau xi)"
proof (rule Bochner_Integration.integrable_bound[
    OF slp_damped_chirp_1_integrable[OF eps]])
  show "slp_damped_chirp_fourier_integrand eps tau xi \<in>
      borel_measurable lborel"
    by measurable
  show "AE x in lborel.
      norm_class.norm
          (slp_damped_chirp_fourier_integrand eps tau xi x) \<le>
        norm_class.norm (slp_damped_chirp_1 eps tau x)"
    unfolding slp_damped_chirp_fourier_integrand_def
    by (simp only: norm_mult norm_exp_i_times mult.left_neutral order_refl
        eventually_True)
qed

definition slp_damped_chirp_fourier_integral ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex"
where
  "slp_damped_chirp_fourier_integral eps tau xi =
    integral\<^sup>L lborel
      (slp_damped_chirp_fourier_integrand eps tau xi)"

lemma slp_damped_center_fourier_integral_product:
  assumes eps: "0 < eps"
  shows "slp_fourier_transform
      (slp_damped_center_kernel eps tau) xi =
    slp_damped_chirp_fourier_integral eps tau (xi $ (0 :: 2)) *
      slp_damped_chirp_fourier_integral eps (- tau) (xi $ (1 :: 2))"
proof -
  let ?P = "PiM (UNIV::2 set) (\<lambda>_. (lborel :: real measure))"
  let ?V = "\<lambda>omega::2 \<Rightarrow> real. \<chi> i. omega i"
  let ?one =
    "\<lambda>i::2. if i = 0
      then slp_damped_chirp_fourier_integrand eps tau (xi $ 0)
      else slp_damped_chirp_fourier_integrand eps (- tau) (xi $ 1)"
  let ?integrand =
    "\<lambda>x. slp_fourier_phase xi x *
      slp_damped_center_kernel eps tau x"
  interpret scalar:
    product_sigma_finite "\<lambda>_::2. (lborel :: real measure)"
    by standard
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have vector_measurable: "?V \<in> measurable ?P borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have integrand_integrable: "integrable lborel ?integrand"
    by (rule slp_fourier_integrand_integrable)
      (rule slp_damped_center_kernel_integrable[OF eps])
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
  have one_integrable: "integrable lborel (?one i)" for i
    unfolding universe_two
    by (cases i)
      (simp_all add: slp_damped_chirp_fourier_integrand_integrable[OF eps])
  have finite_two: "finite (UNIV :: 2 set)"
    by simp
  have pullback:
      "(\<lambda>omega. ?integrand (?V omega)) =
        (\<lambda>omega. \<Prod>i\<in>UNIV. ?one i (omega i))"
    by (rule ext)
      (simp add: universe_two
        slp_damped_center_fourier_integrand_coordinate_product
        slp_damped_chirp_fourier_integrand_def)
  have transported:
      "integral\<^sup>L (distr ?P borel ?V) ?integrand =
        integral\<^sup>L ?P
          (\<lambda>omega. \<Prod>i\<in>UNIV. ?one i (omega i))"
    using integral_distr[OF vector_measurable integrand_borel]
    by (simp only: pullback)
  have product_value:
      "integral\<^sup>L ?P
          (\<lambda>omega. \<Prod>i\<in>UNIV. ?one i (omega i)) =
        (\<Prod>i\<in>(UNIV::2 set). integral\<^sup>L lborel (?one i))"
    by (rule scalar.product_integral_prod[OF finite_two])
      (simp_all only: one_integrable)
  have product_closed:
      "(\<Prod>i\<in>(UNIV::2 set). integral\<^sup>L lborel (?one i)) =
        integral\<^sup>L lborel
            (slp_damped_chirp_fourier_integrand eps tau (xi $ 0)) *
          integral\<^sup>L lborel
            (slp_damped_chirp_fourier_integrand eps (- tau) (xi $ 1))"
    unfolding universe_two
    by simp
  have transform_product:
      "slp_fourier_transform
          (slp_damped_center_kernel eps tau) xi =
        (\<Prod>i\<in>(UNIV::2 set). integral\<^sup>L lborel (?one i))"
    unfolding slp_fourier_transform_def
    using transported product_value
    by (simp only:
        slp_lborel_cartesian_vector_product[where 'n=2])
  show ?thesis
    unfolding slp_damped_chirp_fourier_integral_def
    by (rule trans[OF transform_product product_closed])
qed

end
