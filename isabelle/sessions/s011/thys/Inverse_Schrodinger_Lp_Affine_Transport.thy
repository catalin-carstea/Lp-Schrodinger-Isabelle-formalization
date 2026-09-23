theory Inverse_Schrodinger_Lp_Affine_Transport
  imports
    Inverse_Schrodinger_Lp_Quadratic_RL_Passive_Affine
    "HOL-Analysis.Change_Of_Vars"
begin

section \<open>Fixed affine-coordinate transport\<close>

lemma slp_has_absolute_integral_change_of_variables_linear_euclidean:
  fixes f :: "real^'n::{finite, wellorder} \<Rightarrow> 'a::euclidean_space"
    and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes g_linear: "linear g"
  shows
    "((\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x))
        absolutely_integrable_on S \<and>
      integral S (\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x)) = b)
    \<longleftrightarrow>
    (f absolutely_integrable_on (g ` S) \<and>
      integral (g ` S) f = b)"
proof -
  have integrability_iff:
    "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x))
        absolutely_integrable_on S
      \<longleftrightarrow> f absolutely_integrable_on (g ` S)"
  proof -
    have
      "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x))
          absolutely_integrable_on S
        \<longleftrightarrow>
        (\<forall>a\<in>Basis. (\<lambda>x. \<bar>det (matrix g)\<bar> * (f (g x) \<bullet> a))
          absolutely_integrable_on S)"
      by (subst absolutely_integrable_componentwise_iff) simp
    also have "... \<longleftrightarrow>
        (\<forall>a\<in>Basis. (\<lambda>x. f x \<bullet> a)
          absolutely_integrable_on (g ` S))"
    proof (intro ball_cong refl)
      fix a :: 'a
      assume "a \<in> Basis"
      have vector_iff:
        "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R
            (vec (f (g x) \<bullet> a) :: real^1))
            absolutely_integrable_on S
          \<longleftrightarrow>
          (\<lambda>x. (vec (f x \<bullet> a) :: real^1))
            absolutely_integrable_on (g ` S)"
        by (rule absolutely_integrable_change_of_variables_linear[OF g_linear])
      show
        "(\<lambda>x. \<bar>det (matrix g)\<bar> * (f (g x) \<bullet> a))
            absolutely_integrable_on S
          \<longleftrightarrow>
          (\<lambda>x. f x \<bullet> a)
            absolutely_integrable_on (g ` S)"
        using vector_iff
        by (simp add: absolutely_integrable_on_1_iff real_scaleR_def)
    qed
    also have "... \<longleftrightarrow> f absolutely_integrable_on (g ` S)"
      by (rule absolutely_integrable_componentwise_iff[symmetric])
    finally show ?thesis .
  qed

  show ?thesis
  proof (intro conj_cong)
    show
      "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x))
          absolutely_integrable_on S
        \<longleftrightarrow> f absolutely_integrable_on (g ` S)"
      by (rule integrability_iff)
  next
    assume f_integrable: "f absolutely_integrable_on (g ` S)"
    have pull_integrable:
      "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x))
        integrable_on S"
    proof (rule set_lebesgue_integral_eq_integral(1))
      show
        "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x))
          absolutely_integrable_on S"
        using integrability_iff f_integrable by (rule iffD2)
    qed
    have original_integrable: "f integrable_on (g ` S)"
      using f_integrable by (rule set_lebesgue_integral_eq_integral(1))

    have
      "(integral S
          (\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x)) = b)
        \<longleftrightarrow>
        (\<forall>a\<in>Basis.
          integral S
            (\<lambda>x. (\<bar>det (matrix g)\<bar> *\<^sub>R f (g x)) \<bullet> a)
            = b \<bullet> a)"
      by (rule integral_eq_iff_componentwise[OF pull_integrable])
    also have "... \<longleftrightarrow>
        (\<forall>a\<in>Basis.
          integral S
            (\<lambda>x. \<bar>det (matrix g)\<bar> * (f (g x) \<bullet> a))
            = b \<bullet> a)"
      by simp
    also have "... \<longleftrightarrow>
        (\<forall>a\<in>Basis.
          integral (g ` S) (\<lambda>x. f x \<bullet> a) = b \<bullet> a)"
    proof (intro ball_cong refl)
      fix a :: 'a
      assume "a \<in> Basis"
      have vector_iff:
        "((\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R
              (vec (f (g x) \<bullet> a) :: real^1))
            absolutely_integrable_on S \<and>
          integral S
            (\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R
              (vec (f (g x) \<bullet> a) :: real^1))
            = (vec (b \<bullet> a) :: real^1))
          \<longleftrightarrow>
          ((\<lambda>x. (vec (f x \<bullet> a) :: real^1))
            absolutely_integrable_on (g ` S) \<and>
          integral (g ` S) (\<lambda>x. (vec (f x \<bullet> a) :: real^1))
            = (vec (b \<bullet> a) :: real^1))"
        by (rule has_absolute_integral_change_of_variables_linear[OF g_linear])
      have component_integrability:
        "(\<lambda>x. f x \<bullet> a) absolutely_integrable_on (g ` S)"
      proof -
        have
          "((\<lambda>z :: 'a. z \<bullet> a) \<circ> f)
            absolutely_integrable_on (g ` S)"
          by (rule absolutely_integrable_linear[
            OF f_integrable bounded_linear_inner_left])
        then show ?thesis by (simp add: o_def)
      qed
      have pullback_absolutely_integrable:
        "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x))
          absolutely_integrable_on S"
        using integrability_iff f_integrable by (rule iffD2)
      have component_pullback_integrability:
        "(\<lambda>x. \<bar>det (matrix g)\<bar> * (f (g x) \<bullet> a))
          absolutely_integrable_on S"
      proof -
        have
          "((\<lambda>z :: 'a. z \<bullet> a) \<circ>
            (\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x)))
            absolutely_integrable_on S"
          by (rule absolutely_integrable_linear[
            OF pullback_absolutely_integrable bounded_linear_inner_left])
        then show ?thesis by (simp add: o_def)
      qed
      show
        "integral S
            (\<lambda>x. \<bar>det (matrix g)\<bar> * (f (g x) \<bullet> a))
            = b \<bullet> a
          \<longleftrightarrow>
          integral (g ` S) (\<lambda>x. f x \<bullet> a) = b \<bullet> a"
        using vector_iff component_integrability
          component_pullback_integrability
        by (simp add: absolutely_integrable_on_1_iff integral_on_1_eq
            real_scaleR_def vec_eq_iff)
    qed
    also have "... \<longleftrightarrow> integral (g ` S) f = b"
      by (rule integral_eq_iff_componentwise[OF original_integrable, symmetric])
    finally show
      "(integral S
          (\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x)) = b)
        \<longleftrightarrow> integral (g ` S) f = b" .
  qed
qed

lemma slp_lborel_integrable_iff_absolutely_integrable_UNIV:
  fixes f :: "real^'n::finite \<Rightarrow> 'a::euclidean_space"
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "integrable lborel f \<longleftrightarrow> f absolutely_integrable_on UNIV"
  using integrable_completion[OF f_measurable]
  by (simp add: set_integrable_def)

lemma slp_lborel_linear_pullback:
  fixes f :: "real^'n::{finite, wellorder} \<Rightarrow> 'a::euclidean_space"
    and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes g_linear: "linear g"
    and g_injective: "inj g"
    and f_integrable: "integrable lborel f"
  shows pullback_integrable: "integrable lborel (\<lambda>x. f (g x))"
    and jacobian_formula:
      "integral\<^sup>L lborel f =
        \<bar>det (matrix g)\<bar> *\<^sub>R
          integral\<^sup>L lborel (\<lambda>x. f (g x))"
proof -
  have g_surjective: "surj g"
    using linear_injective_imp_surjective[OF g_linear g_injective] by simp
  have image_UNIV: "g ` UNIV = UNIV"
    using g_surjective by blast
  have g_bounded: "bounded_linear g"
    using g_linear by (simp add: linear_conv_bounded_linear)
  have g_measurable: "g \<in> measurable lborel borel"
    using borel_measurable_continuous_onI[OF linear_continuous_on[OF g_bounded]]
    by simp
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_integrable by measurable
  have pullback_measurable:
    "(\<lambda>x. f (g x)) \<in> borel_measurable lborel"
    using g_measurable f_measurable by measurable
  have f_absolutely_integrable: "f absolutely_integrable_on UNIV"
    using slp_lborel_integrable_iff_absolutely_integrable_UNIV[
      OF f_measurable] f_integrable by blast
  have transformed:
    "((\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x))
        absolutely_integrable_on UNIV \<and>
      integral UNIV
        (\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x))
        = integral UNIV f)"
  proof -
    have rhs:
      "f absolutely_integrable_on (g ` UNIV) \<and>
        integral (g ` UNIV) f = integral UNIV f"
      using f_absolutely_integrable image_UNIV by simp
    show ?thesis
      using slp_has_absolute_integral_change_of_variables_linear_euclidean[
        OF g_linear, where f=f and S=UNIV and b="integral UNIV f"]
        rhs by blast
  qed
  have det_nonzero: "det (matrix g) \<noteq> 0"
    using det_nz_iff_inj[OF g_linear] g_injective by blast
  have pullback_absolutely_integrable:
    "(\<lambda>x. f (g x)) absolutely_integrable_on UNIV"
    using transformed det_nonzero
    by (simp add: absolutely_integrable_on_scaleR_iff)
  have pullback_lborel_integrable:
    "integrable lborel (\<lambda>x. f (g x))"
    using slp_lborel_integrable_iff_absolutely_integrable_UNIV[
      OF pullback_measurable] pullback_absolutely_integrable by blast
  show "integrable lborel (\<lambda>x. f (g x))"
    by (rule pullback_lborel_integrable)

  have scaled_integral:
    "integral UNIV
        (\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x))
      = \<bar>det (matrix g)\<bar> *\<^sub>R
          integral UNIV (\<lambda>x. f (g x))"
    by (rule integral_cmul)
  show
    "integral\<^sup>L lborel f =
      \<bar>det (matrix g)\<bar> *\<^sub>R
        integral\<^sup>L lborel (\<lambda>x. f (g x))"
    using transformed scaled_integral
      integral_lborel[OF f_integrable]
      integral_lborel[OF pullback_lborel_integrable]
    by metis
qed

lemma slp_lborel_affine_pullback:
  fixes f :: "real^'n::{finite, wellorder} \<Rightarrow> 'a::euclidean_space"
    and g :: "real^'n::_ \<Rightarrow> real^'n::_"
    and a :: "real^'n::_"
  assumes g_linear: "linear g"
    and g_injective: "inj g"
    and f_integrable: "integrable lborel f"
  shows "integrable lborel (\<lambda>x. f (a + g x))"
    and "integral\<^sup>L lborel f =
      \<bar>det (matrix g)\<bar> *\<^sub>R
        integral\<^sup>L lborel (\<lambda>x. f (a + g x))"
proof -
  let ?translated = "\<lambda>y. f (a + y)"
  have translated_integrable: "integrable lborel ?translated"
    by (rule slp_lborel_integrable_translate[OF f_integrable])
  have translated_integral:
    "integral\<^sup>L lborel ?translated = integral\<^sup>L lborel f"
    by (rule slp_lborel_integral_translate[OF f_integrable])
  show "integrable lborel (\<lambda>x. f (a + g x))"
    using slp_lborel_linear_pullback(1)[
      OF g_linear g_injective translated_integrable] .
  have
    "integral\<^sup>L lborel ?translated =
      \<bar>det (matrix g)\<bar> *\<^sub>R
        integral\<^sup>L lborel (\<lambda>x. ?translated (g x))"
    by (rule slp_lborel_linear_pullback(2)[
      OF g_linear g_injective translated_integrable])
  with translated_integral show
    "integral\<^sup>L lborel f =
      \<bar>det (matrix g)\<bar> *\<^sub>R
        integral\<^sup>L lborel (\<lambda>x. f (a + g x))"
    by simp
qed

lemma slp_affine_pullback_tendsto_zero:
  fixes H :: "real \<Rightarrow> real^'n::{finite, wellorder} \<Rightarrow> complex"
    and g :: "real^'n::_ \<Rightarrow> real^'n::_"
    and a :: "real^'n::_"
  assumes g_linear: "linear g"
    and g_injective: "inj g"
    and H_integrable: "\<And>omega. integrable lborel (H omega)"
    and H_decay:
      "((\<lambda>omega. integral\<^sup>L lborel (H omega)) \<longlongrightarrow> 0) at_top"
  shows
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>x. H omega (a + g x))) \<longlongrightarrow> 0) at_top"
proof -
  let ?J = "\<bar>det (matrix g)\<bar>"
  have det_nonzero: "det (matrix g) \<noteq> 0"
    using det_nz_iff_inj[OF g_linear] g_injective by blast
  have J_nonzero: "?J \<noteq> 0"
    using det_nonzero by simp
  have pullback_formula:
    "integral\<^sup>L lborel (\<lambda>x. H omega (a + g x)) =
      inverse ?J *\<^sub>R integral\<^sup>L lborel (H omega)" for omega
  proof -
    have jacobian:
      "integral\<^sup>L lborel (H omega) =
        ?J *\<^sub>R integral\<^sup>L lborel (\<lambda>x. H omega (a + g x))"
      by (rule slp_lborel_affine_pullback(2)[
        OF g_linear g_injective H_integrable])
    have cancelled:
      "inverse ?J *\<^sub>R integral\<^sup>L lborel (H omega) =
        integral\<^sup>L lborel (\<lambda>x. H omega (a + g x))"
    proof -
      have applied:
        "inverse ?J *\<^sub>R integral\<^sup>L lborel (H omega) =
          inverse ?J *\<^sub>R
            (?J *\<^sub>R integral\<^sup>L lborel
              (\<lambda>x. H omega (a + g x)))"
        using jacobian by (rule arg_cong)
      also have "... = integral\<^sup>L lborel
          (\<lambda>x. H omega (a + g x))"
        using J_nonzero
        by (simp add: scaleR_scaleR)
      finally show ?thesis .
    qed
    show ?thesis
      by (rule cancelled[symmetric])
  qed
  have scaled_decay:
    "((\<lambda>omega. inverse ?J *\<^sub>R
        integral\<^sup>L lborel (H omega)) \<longlongrightarrow> 0) at_top"
  proof -
    have
      "((\<lambda>omega. inverse ?J *\<^sub>R
          integral\<^sup>L lborel (H omega))
        \<longlongrightarrow> inverse ?J *\<^sub>R 0) at_top"
      by (rule tendsto_scaleR[OF tendsto_const H_decay])
    then show ?thesis by simp
  qed
  show ?thesis
    using scaled_decay by (simp only: pullback_formula)
qed

end
