theory Inverse_Schrodinger_Lp_Passive_Shear_Transport
  imports Inverse_Schrodinger_Lp_Affine_Transport
begin

section \<open>Passive-dependent affine shear transport\<close>

lemma slp_lborel_scalar_affine_pullback:
  fixes f :: "'d::euclidean_space \<Rightarrow>
    'a::{banach, second_countable_topology}"
    and c :: real
    and t :: 'd
  assumes c_nonzero: "c \<noteq> 0"
    and f_integrable: "integrable lborel f"
  shows pullback_integrable:
      "integrable lborel (\<lambda>x. f (t + c *\<^sub>R x))"
    and integral_formula:
      "integral\<^sup>L lborel f =
        \<bar>c\<bar> ^ DIM('d) *\<^sub>R
          integral\<^sup>L lborel (\<lambda>x. f (t + c *\<^sub>R x))"
proof -
  let ?T = "\<lambda>x. t + c *\<^sub>R x"
  let ?K = "\<bar>c\<bar> ^ DIM('d)"
  let ?D = "distr lborel borel ?T"
  have K_positive: "0 < ?K"
    using c_nonzero by simp
  have K_nonzero: "?K \<noteq> 0"
    using K_positive by simp
  have T_continuous: "continuous_on UNIV ?T"
    by (intro continuous_intros)
  have T_measurable: "?T \<in> measurable lborel borel"
    using borel_measurable_continuous_onI[OF T_continuous] by simp
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_integrable by measurable
  have f_borel_measurable: "f \<in> borel_measurable borel"
    using f_measurable by simp
  have f_D_measurable: "f \<in> borel_measurable ?D"
    using f_measurable T_measurable by simp
  have density_identity:
    "lborel = density ?D (\<lambda>_. ?K)"
    by (rule lborel_affine[where c = c and t = t])
      (rule c_nonzero)
  have density_integrable:
    "integrable (density ?D (\<lambda>_. ?K)) f"
    using f_integrable density_identity by simp
  have scaled_D_integrable:
    "integrable ?D (\<lambda>x. ?K *\<^sub>R f x)"
    using integrable_density[
      where M = ?D and f = f and g = "\<lambda>_. ?K"]
      f_D_measurable density_integrable K_positive
    by simp
  have D_integrable: "integrable ?D f"
  proof -
    have inverse_scaled:
      "integrable ?D
        (\<lambda>x. inverse ?K *\<^sub>R (?K *\<^sub>R f x))"
      by (rule integrable_scaleR_right)
        (use scaled_D_integrable in simp)
    show ?thesis
      using inverse_scaled K_nonzero
      by (simp add: scaleR_scaleR)
  qed
  show "integrable lborel (\<lambda>x. f (t + c *\<^sub>R x))"
    using integrable_distr_eq[OF T_measurable f_borel_measurable]
      D_integrable by blast

  have density_integral_formula:
    "integral\<^sup>L (density ?D (\<lambda>_. ?K)) f =
      integral\<^sup>L ?D (\<lambda>x. ?K *\<^sub>R f x)"
    by (rule integral_density[OF f_D_measurable])
      (use K_positive in simp_all)
  have distr_integral_formula:
    "integral\<^sup>L ?D f =
      integral\<^sup>L lborel (\<lambda>x. f (t + c *\<^sub>R x))"
    by (rule integral_distr[OF T_measurable f_borel_measurable])
  show
    "integral\<^sup>L lborel f =
      ?K *\<^sub>R
        integral\<^sup>L lborel (\<lambda>x. f (t + c *\<^sub>R x))"
  proof -
    have
      "integral\<^sup>L lborel f =
        integral\<^sup>L (density ?D (\<lambda>_. ?K)) f"
      using density_identity by simp
    also have "... =
        integral\<^sup>L ?D (\<lambda>x. ?K *\<^sub>R f x)"
      by (rule density_integral_formula)
    also have "... = ?K *\<^sub>R integral\<^sup>L ?D f"
      by simp
    also have "... = ?K *\<^sub>R
        integral\<^sup>L lborel (\<lambda>x. f (t + c *\<^sub>R x))"
      using distr_integral_formula by simp
    finally show ?thesis .
  qed
qed

lemma slp_passive_affine_shear_measurable:
  fixes a :: "real^'n::finite \<Rightarrow> real^bool"
    and c :: real
  assumes a_measurable: "a \<in> borel_measurable lborel"
  shows
    "(\<lambda>cu. (a (snd cu) + c *\<^sub>R fst cu, snd cu)) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^'n)) measure)"
proof -
  have fst_continuous:
    "continuous_on UNIV
      (\<lambda>cu :: (real^bool) \<times> (real^'n). fst cu)"
    by (intro continuous_intros)
  have fst_measurable:
    "(\<lambda>cu :: (real^bool) \<times> (real^'n). fst cu) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^'n)) measure)"
    using borel_measurable_continuous_onI[OF fst_continuous] by simp
  have snd_continuous:
    "continuous_on UNIV
      (\<lambda>cu :: (real^bool) \<times> (real^'n). snd cu)"
    by (intro continuous_intros)
  have snd_measurable:
    "(\<lambda>cu :: (real^bool) \<times> (real^'n). snd cu) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^'n)) measure)"
    using borel_measurable_continuous_onI[OF snd_continuous] by simp
  have snd_to_lborel:
    "(\<lambda>cu :: (real^bool) \<times> (real^'n). snd cu) \<in>
      measurable
        (lborel :: ((real^bool) \<times> (real^'n)) measure)
        (lborel :: (real^'n) measure)"
    using snd_measurable by simp
  have passive_measurable:
    "(\<lambda>cu :: (real^bool) \<times> (real^'n).
      a (snd cu) + c *\<^sub>R fst cu) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^'n)) measure)"
  proof -
    have a_after_snd:
      "(\<lambda>cu :: (real^bool) \<times> (real^'n). a (snd cu)) \<in>
        borel_measurable
          (lborel :: ((real^bool) \<times> (real^'n)) measure)"
      by (rule measurable_compose[OF snd_to_lborel a_measurable])
    have scaled_fst:
      "(\<lambda>cu :: (real^bool) \<times> (real^'n).
        c *\<^sub>R fst cu) \<in>
        borel_measurable
          (lborel :: ((real^bool) \<times> (real^'n)) measure)"
      using fst_measurable by measurable
    show ?thesis
      using a_after_snd scaled_fst by measurable
  qed
  show ?thesis
    by (rule borel_measurable_Pair[OF passive_measurable snd_measurable])
qed

lemma slp_passive_affine_shear_integrable:
  fixes a :: "real^'n::finite \<Rightarrow> real^bool"
    and c :: real
    and F :: "((real^bool) \<times> (real^'n)) \<Rightarrow>
      'a::{euclidean_space, second_countable_topology}"
  assumes a_measurable: "a \<in> borel_measurable lborel"
    and c_nonzero: "c \<noteq> 0"
    and F_integrable: "integrable lborel F"
  shows
    "integrable lborel
      (\<lambda>cu. F (a (snd cu) + c *\<^sub>R fst cu, snd cu))"
proof -
  let ?T = "\<lambda>cu.
    F (a (snd cu) + c *\<^sub>R fst cu, snd cu)"
  have shear_measurable:
    "(\<lambda>cu. (a (snd cu) + c *\<^sub>R fst cu, snd cu)) \<in>
      borel_measurable
        (lborel :: ((real^bool) \<times> (real^'n)) measure)"
    by (rule slp_passive_affine_shear_measurable[
        where c = c, OF a_measurable])
  have F_measurable:
    "F \<in> borel_measurable
      (lborel :: ((real^bool) \<times> (real^'n)) measure)"
    using F_integrable by measurable
  have T_measurable:
    "?T \<in> borel_measurable
      (lborel :: ((real^bool) \<times> (real^'n)) measure)"
    using shear_measurable F_measurable by measurable
  have swap_continuous:
    "continuous_on UNIV
      (\<lambda>uc :: (real^'n) \<times> (real^bool). (snd uc, fst uc))"
    by (intro continuous_intros)
  have swap_measurable:
    "(\<lambda>uc :: (real^'n) \<times> (real^bool). (snd uc, fst uc)) \<in>
      measurable
        (lborel :: ((real^'n) \<times> (real^bool)) measure)
        (lborel :: ((real^bool) \<times> (real^'n)) measure)"
    using borel_measurable_continuous_onI[OF swap_continuous] by simp
  have T_swapped_measurable_raw:
    "(\<lambda>uc. F
      (a (fst uc) + c *\<^sub>R snd uc, fst uc)) \<in>
      borel_measurable
        (lborel :: ((real^'n) \<times> (real^bool)) measure)"
  proof -
    have composed:
      "(\<lambda>uc :: (real^'n) \<times> (real^bool).
        ?T (snd uc, fst uc)) \<in>
        borel_measurable
          (lborel :: ((real^'n) \<times> (real^bool)) measure)"
      by (rule measurable_compose[OF swap_measurable T_measurable])
    show ?thesis
      using composed by simp
  qed
  have F_product_integrable:
    "integrable
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'n) measure)) F"
    using F_integrable by (simp only: lborel_prod)
  have F_product_case_integrable:
    "integrable
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'n) measure))
      (case_prod (curry F))"
    using F_product_integrable by simp
  have AE_section_integrable:
    "AE u in (lborel :: (real^'n) measure).
      integrable lborel (\<lambda>c. F (c, u))"
    using lborel_pair.AE_integrable_snd[
      where f = "curry F", OF F_product_case_integrable]
    by simp
  have AE_transformed_section_integrable:
    "AE u in (lborel :: (real^'n) measure).
      integrable lborel (\<lambda>x. F (a u + c *\<^sub>R x, u))"
    using AE_section_integrable
  proof eventually_elim
    fix u
    assume section_integrable: "integrable lborel (\<lambda>c. F (c, u))"
    show "integrable lborel (\<lambda>x. F (a u + c *\<^sub>R x, u))"
      by (rule slp_lborel_scalar_affine_pullback(1)[
          where f = "\<lambda>x. F (x, u)" and c = c and t = "a u",
          OF c_nonzero section_integrable])
  qed

  have norm_F_product_integrable:
    "integrable
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'n) measure))
      (\<lambda>cu. norm (F cu))"
    using Bochner_Integration.integrable_norm[OF F_product_integrable] .
  have norm_F_product_case_integrable:
    "integrable
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'n) measure))
      (case_prod (curry (\<lambda>cu. norm (F cu))))"
    using norm_F_product_integrable by simp
  let ?B = "\<lambda>u. integral\<^sup>L lborel (\<lambda>c. norm (F (c, u)))"
  let ?BT = "\<lambda>u. integral\<^sup>L lborel
    (\<lambda>x. norm (F (a u + c *\<^sub>R x, u)))"
  have B_integrable: "integrable lborel ?B"
    using lborel_pair.integrable_snd[
      where f = "curry (\<lambda>cu. norm (F cu))",
      OF norm_F_product_case_integrable]
    by simp

  let ?J = "\<bar>c\<bar> ^ DIM(real^bool)"
  have J_nonzero: "?J \<noteq> 0"
    using c_nonzero by simp
  have AE_norm_section_formula:
    "AE u in (lborel :: (real^'n) measure).
      ?BT u = inverse ?J *\<^sub>R ?B u"
    using AE_section_integrable
  proof eventually_elim
    fix u
    assume section_integrable: "integrable lborel (\<lambda>c. F (c, u))"
    have norm_section_integrable:
      "integrable lborel (\<lambda>c. norm (F (c, u)))"
      using Bochner_Integration.integrable_norm[OF section_integrable] .
    have jacobian:
      "?B u = ?J *\<^sub>R ?BT u"
      by (rule slp_lborel_scalar_affine_pullback(2)[
          where f = "\<lambda>x. norm (F (x, u))"
            and c = c and t = "a u",
          OF c_nonzero norm_section_integrable])
    have
      "inverse ?J *\<^sub>R ?B u =
        inverse ?J *\<^sub>R (?J *\<^sub>R ?BT u)"
      using jacobian by (rule arg_cong)
    also have "... = ?BT u"
      using J_nonzero by (simp add: scaleR_scaleR)
    finally show "?BT u = inverse ?J *\<^sub>R ?B u"
      by (rule sym)
  qed
  have transformed_norm_swapped_measurable:
    "(\<lambda>uc. norm
      (F (a (fst uc) + c *\<^sub>R snd uc, fst uc))) \<in>
      borel_measurable
        ((lborel :: (real^'n) measure) \<Otimes>\<^sub>M
          (lborel :: (real^bool) measure))"
  proof -
    have raw:
      "(\<lambda>uc. norm
        (F (a (fst uc) + c *\<^sub>R snd uc, fst uc))) \<in>
        borel_measurable
          (lborel :: ((real^'n) \<times> (real^bool)) measure)"
      by (rule measurable_compose[
          OF T_swapped_measurable_raw borel_measurable_norm])
    show ?thesis
      using raw by (simp only: lborel_prod)
  qed
  have BT_measurable:
    "?BT \<in> borel_measurable (lborel :: (real^'n) measure)"
    by (rule lborel.borel_measurable_lebesgue_integral[
        where f = "\<lambda>u x.
          norm (F (a u + c *\<^sub>R x, u))"])
      (use transformed_norm_swapped_measurable in simp)
  have scaled_B_integrable:
    "integrable lborel (\<lambda>u. inverse ?J *\<^sub>R ?B u)"
    using B_integrable by simp
  have BT_integrable: "integrable lborel ?BT"
    by (rule integrable_cong_AE_imp[
        OF scaled_B_integrable BT_measurable])
      (use AE_norm_section_formula in eventually_elim; simp)
  have BT_integrable_explicit:
    "integrable (lborel :: (real^'n) measure)
      (\<lambda>u. integral\<^sup>L (lborel :: (real^bool) measure)
        (\<lambda>x. norm (F (a u + c *\<^sub>R x, u))))"
    by (rule BT_integrable)

  have T_swapped_measurable:
    "(\<lambda>uc. F
      (a (fst uc) + c *\<^sub>R snd uc, fst uc)) \<in>
      borel_measurable
        ((lborel :: (real^'n) measure) \<Otimes>\<^sub>M
          (lborel :: (real^bool) measure))"
    using T_swapped_measurable_raw
    by (simp only: lborel_prod)
  have T_swapped_integrable_raw:
    "integrable
      ((lborel :: (real^'n) measure) \<Otimes>\<^sub>M
        (lborel :: (real^bool) measure))
      (\<lambda>uc. F
        (a (fst uc) + c *\<^sub>R snd uc, fst uc))"
    apply (rule lborel_pair.Fubini_integrable)
    apply (rule T_swapped_measurable)
    apply (simp only: prod.sel)
    apply (rule BT_integrable_explicit)
    apply (simp only: prod.sel)
    apply (rule AE_transformed_section_integrable)
    done
  have T_swapped_integrable:
    "integrable
      ((lborel :: (real^'n) measure) \<Otimes>\<^sub>M
        (lborel :: (real^bool) measure))
      (\<lambda>(u, x). F (a u + c *\<^sub>R x, u))"
  proof -
    have function_eq:
      "(\<lambda>uc. F
          (a (fst uc) + c *\<^sub>R snd uc, fst uc)) =
        (\<lambda>(u, x). F (a u + c *\<^sub>R x, u))"
    proof (rule ext)
      fix uc :: "(real^'n) \<times> (real^bool)"
      obtain u x where uc: "uc = (u, x)"
        by (cases uc)
      show "F (a (fst uc) + c *\<^sub>R snd uc, fst uc) =
          (case uc of (u, x) \<Rightarrow> F (a u + c *\<^sub>R x, u))"
        by (simp add: uc)
    qed
    show ?thesis
      using T_swapped_integrable_raw by (simp only: function_eq)
  qed
  have T_product_integrable:
    "integrable
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'n) measure))
      (\<lambda>(x, u). F (a u + c *\<^sub>R x, u))"
    using lborel_pair.integrable_product_swap_iff[
      where f = "\<lambda>(x, u). F (a u + c *\<^sub>R x, u)"]
      T_swapped_integrable
    by simp
  have product_function_eq:
    "(\<lambda>cu. F (a (snd cu) + c *\<^sub>R fst cu, snd cu)) =
      (\<lambda>(x, u). F (a u + c *\<^sub>R x, u))"
  proof (rule ext)
    fix cu :: "(real^bool) \<times> (real^'n)"
    obtain x u where cu: "cu = (x, u)"
      by (cases cu)
    show "F (a (snd cu) + c *\<^sub>R fst cu, snd cu) =
        (case cu of (x, u) \<Rightarrow> F (a u + c *\<^sub>R x, u))"
      by (simp add: cu)
  qed
  show ?thesis
    using T_product_integrable
    by (simp only: lborel_prod product_function_eq)
qed

lemma slp_passive_affine_shear_integral:
  fixes a :: "real^'n::finite \<Rightarrow> real^bool"
    and c :: real
    and F :: "((real^bool) \<times> (real^'n)) \<Rightarrow>
      'a::{euclidean_space, second_countable_topology}"
  assumes a_measurable: "a \<in> borel_measurable lborel"
    and c_nonzero: "c \<noteq> 0"
    and F_integrable: "integrable lborel F"
  shows
    "integral\<^sup>L lborel F =
      \<bar>c\<bar> ^ DIM(real^bool) *\<^sub>R
        integral\<^sup>L lborel
          (\<lambda>cu.
            F (a (snd cu) + c *\<^sub>R fst cu, snd cu))"
proof -
  let ?J = "\<bar>c\<bar> ^ DIM(real^bool)"
  have F_product_integrable:
    "integrable
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'n) measure)) F"
    using F_integrable by (simp only: lborel_prod)
  have F_product_case_integrable:
    "integrable
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'n) measure))
      (case_prod (curry F))"
    using F_product_integrable by simp
  have T_integrable:
    "integrable lborel
      (\<lambda>cu. F
        (a (snd cu) + c *\<^sub>R fst cu, snd cu))"
    by (rule slp_passive_affine_shear_integrable[
        OF a_measurable c_nonzero F_integrable])
  have T_product_integrable:
    "integrable
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'n) measure))
      (\<lambda>cu.
        F (a (snd cu) + c *\<^sub>R fst cu, snd cu))"
    using T_integrable
    by (simp only: lborel_prod)
  have T_product_case_integrable:
    "integrable
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'n) measure))
      (case_prod (curry
        (\<lambda>cu. F
          (a (snd cu) + c *\<^sub>R fst cu, snd cu))))"
    using T_product_integrable by simp
  have AE_section_integrable:
    "AE u in (lborel :: (real^'n) measure).
      integrable lborel (\<lambda>c. F (c, u))"
    using lborel_pair.AE_integrable_snd[
      where f = "curry F", OF F_product_case_integrable]
    by simp
  have AE_section_formula:
    "AE u in (lborel :: (real^'n) measure).
      integral\<^sup>L lborel (\<lambda>c. F (c, u)) =
        ?J *\<^sub>R
          integral\<^sup>L lborel
            (\<lambda>x. F (a u + c *\<^sub>R x, u))"
    using AE_section_integrable
  proof eventually_elim
    fix u
    assume section_integrable: "integrable lborel (\<lambda>c. F (c, u))"
    show
      "integral\<^sup>L lborel (\<lambda>c. F (c, u)) =
        ?J *\<^sub>R
          integral\<^sup>L lborel
            (\<lambda>x. F (a u + c *\<^sub>R x, u))"
      by (rule slp_lborel_scalar_affine_pullback(2)[
          where f = "\<lambda>x. F (x, u)"
            and c = c and t = "a u",
          OF c_nonzero section_integrable])
  qed
  let ?I = "\<lambda>u. integral\<^sup>L lborel (\<lambda>c. F (c, u))"
  let ?IT = "\<lambda>u. integral\<^sup>L lborel
    (\<lambda>x. F (a u + c *\<^sub>R x, u))"
  have I_integrable: "integrable lborel ?I"
    using lborel_pair.integrable_snd[
      where f = "curry F", OF F_product_case_integrable]
    by simp
  have IT_integrable: "integrable lborel ?IT"
    using lborel_pair.integrable_snd[
      where f = "curry
        (\<lambda>cu. F (a (snd cu) + c *\<^sub>R fst cu, snd cu))",
      OF T_product_case_integrable]
    by simp
  have outer_formula:
    "integral\<^sup>L lborel ?I =
      ?J *\<^sub>R integral\<^sup>L lborel ?IT"
  proof -
    have
      "integral\<^sup>L lborel ?I =
        integral\<^sup>L lborel (\<lambda>u. ?J *\<^sub>R ?IT u)"
      by (rule integral_cong_AE)
        (use I_integrable IT_integrable AE_section_formula in measurable)
    also have "... = ?J *\<^sub>R integral\<^sup>L lborel ?IT"
      by simp
    finally show ?thesis .
  qed
  have original_as_slices:
    "integral\<^sup>L lborel F = integral\<^sup>L lborel ?I"
  proof -
    have fubini:
      "integral\<^sup>L lborel ?I =
        integral\<^sup>L
          ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^'n) measure)) F"
      using lborel_pair.integral_snd[
        where f = "curry F", OF F_product_case_integrable]
      by simp
    show ?thesis
      using fubini[symmetric] by (simp only: lborel_prod)
  qed
  have transformed_as_slices:
    "integral\<^sup>L lborel
        (\<lambda>cu.
          F (a (snd cu) + c *\<^sub>R fst cu, snd cu)) =
      integral\<^sup>L lborel ?IT"
  proof -
    have fubini:
      "integral\<^sup>L lborel ?IT =
        integral\<^sup>L
          ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^'n) measure))
          (\<lambda>cu.
            F (a (snd cu) + c *\<^sub>R fst cu, snd cu))"
      using lborel_pair.integral_snd[
        where f = "curry
          (\<lambda>cu. F
            (a (snd cu) + c *\<^sub>R fst cu, snd cu))",
        OF T_product_case_integrable]
      by simp
    show ?thesis
      using fubini[symmetric] by (simp only: lborel_prod)
  qed
  show ?thesis
    using original_as_slices transformed_as_slices outer_formula by simp
qed

lemma slp_passive_affine_shear_tendsto_zero:
  fixes a :: "real^'n::finite \<Rightarrow> real^bool"
    and c :: real
    and H :: "real \<Rightarrow>
      ((real^bool) \<times> (real^'n)) \<Rightarrow> complex"
  assumes a_measurable: "a \<in> borel_measurable lborel"
    and c_nonzero: "c \<noteq> 0"
    and H_integrable: "\<And>omega. integrable lborel (H omega)"
    and H_decay:
      "((\<lambda>omega. integral\<^sup>L lborel (H omega))
        \<longlongrightarrow> 0) at_top"
  shows
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>cu. H omega
          (a (snd cu) + c *\<^sub>R fst cu, snd cu)))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?J = "\<bar>c\<bar> ^ DIM(real^bool)"
  have J_nonzero: "?J \<noteq> 0"
    using c_nonzero by simp
  have pullback_formula:
    "integral\<^sup>L lborel
        (\<lambda>cu. H omega
          (a (snd cu) + c *\<^sub>R fst cu, snd cu)) =
      inverse ?J *\<^sub>R integral\<^sup>L lborel (H omega)"
    for omega
  proof -
    have jacobian:
      "integral\<^sup>L lborel (H omega) =
        ?J *\<^sub>R integral\<^sup>L lborel
          (\<lambda>cu. H omega
            (a (snd cu) + c *\<^sub>R fst cu, snd cu))"
      by (rule slp_passive_affine_shear_integral[
          OF a_measurable c_nonzero H_integrable])
    have
      "inverse ?J *\<^sub>R integral\<^sup>L lborel (H omega) =
        inverse ?J *\<^sub>R
          (?J *\<^sub>R integral\<^sup>L lborel
            (\<lambda>cu. H omega
              (a (snd cu) + c *\<^sub>R fst cu, snd cu)))"
      using jacobian by (rule arg_cong)
    also have "... =
        integral\<^sup>L lborel
          (\<lambda>cu. H omega
            (a (snd cu) + c *\<^sub>R fst cu, snd cu))"
      using J_nonzero by (simp add: scaleR_scaleR)
    finally show ?thesis by (rule sym)
  qed
  have scaled_decay:
    "((\<lambda>omega. inverse ?J *\<^sub>R integral\<^sup>L lborel (H omega))
      \<longlongrightarrow> 0) at_top"
  proof -
    have
      "((\<lambda>omega. inverse ?J *\<^sub>R integral\<^sup>L lborel (H omega))
        \<longlongrightarrow> inverse ?J *\<^sub>R 0) at_top"
      by (rule tendsto_scaleR[OF tendsto_const H_decay])
    then show ?thesis by simp
  qed
  show ?thesis
    using scaled_decay by (simp only: pullback_formula)
qed

end
