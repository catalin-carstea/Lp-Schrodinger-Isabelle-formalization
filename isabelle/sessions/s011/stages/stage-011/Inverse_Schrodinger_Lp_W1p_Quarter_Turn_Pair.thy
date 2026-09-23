theory Inverse_Schrodinger_Lp_W1p_Quarter_Turn_Pair
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Rough_Dbar_Psi_Gain"
begin

section \<open>Local supports under both quarter-turn pullbacks\<close>

theorem slp_test_function_on_quarter_turn_domains:
  assumes f_test: "slp_test_function_on X f"
  shows "slp_test_function_on (image slp_quarter_turn X)
      (\<lambda>x. f (- slp_quarter_turn x)) \<and>
    slp_test_function_on (image (\<lambda>x. - slp_quarter_turn x) X)
      (\<lambda>x. f (slp_quarter_turn x))"
proof -
  have inverse_transport:
      "slp_test_function_on (image slp_quarter_turn Y)
        (\<lambda>x. h (- slp_quarter_turn x))"
    if h_test: "slp_test_function_on Y h"
    for Y :: "slp_point set" and h :: slp_scalar_field
  proof -
    let ?K = "closure {x. h x \<noteq> 0}"
    have h_global: "slp_test_function_on UNIV h"
      using h_test unfolding slp_test_function_on_def by auto
    have rotated_global:
        "slp_test_function_on UNIV (\<lambda>x. h (- slp_quarter_turn x))"
      by (rule slp_test_function_on_inverse_quarter_turn[OF h_global])
    have K_compact: "compact ?K" and K_subset: "?K \<subseteq> Y"
      using h_test unfolding slp_test_function_on_def by blast+
    have image_compact: "compact (image slp_quarter_turn ?K)"
      by (rule slp_quarter_turn_compact_image[OF K_compact])
    have nonzero_subset:
        "{x. h (- slp_quarter_turn x) \<noteq> 0} \<subseteq> image slp_quarter_turn ?K"
    proof
      fix x
      assume x_nonzero: "x \<in> {x. h (- slp_quarter_turn x) \<noteq> 0}"
      have source_in: "- slp_quarter_turn x \<in> ?K"
        by (rule subsetD[OF closure_subset]) (use x_nonzero in simp)
      show "x \<in> image slp_quarter_turn ?K"
        by (rule image_eqI[where x="- slp_quarter_turn x"])
          (use source_in in simp_all)
    qed
    have support_subset:
        "closure {x. h (- slp_quarter_turn x) \<noteq> 0} \<subseteq>
          image slp_quarter_turn ?K"
      by (rule closure_minimal[OF nonzero_subset
            compact_imp_closed[OF image_compact]])
    have support_in_domain:
        "closure {x. h (- slp_quarter_turn x) \<noteq> 0} \<subseteq>
          image slp_quarter_turn Y"
      by (rule subset_trans[OF support_subset image_mono[OF K_subset]])
    show ?thesis
      using rotated_global support_in_domain
      unfolding slp_test_function_on_def by blast
  qed
  have inverse_test:
      "slp_test_function_on (image slp_quarter_turn X)
        (\<lambda>x. f (- slp_quarter_turn x))"
    by (rule inverse_transport[OF f_test])
  have triple_inverse:
      "slp_test_function_on
        (image slp_quarter_turn (image slp_quarter_turn (image slp_quarter_turn X)))
        (\<lambda>x. f (- slp_quarter_turn
          (- slp_quarter_turn (- slp_quarter_turn x))))"
    by (rule inverse_transport[OF inverse_transport[OF inverse_test]])
  have forward_test:
      "slp_test_function_on (image (\<lambda>x. - slp_quarter_turn x) X)
        (\<lambda>x. f (slp_quarter_turn x))"
    using triple_inverse
    by (simp add: image_image
          linear_cmul[OF slp_quarter_turn_linear, of "-1", simplified])
  show ?thesis by (rule conjI[OF inverse_test forward_test])
qed

section \<open>Weak-gradient change of coordinates\<close>

theorem slp_w1p_pair_inverse_quarter_turn_weak_gradient:
  assumes pair: "slp_w1p_pair_on p X u Du"
  shows "slp_weak_gradient_on (image slp_quarter_turn X)
    (\<lambda>x. u (- slp_quarter_turn x))
    (\<lambda>x. \<chi> i. if i = 0 then - Du (- slp_quarter_turn x) $ 1
      else Du (- slp_quarter_turn x) $ 0)"
proof -
  let ?Q = slp_quarter_turn
  let ?Y = "image ?Q X"
  let ?v = "\<lambda>x. u (- ?Q x)"
  let ?Dv = "\<lambda>x. \<chi> i. if i = 0 then - Du (- ?Q x) $ 1
    else Du (- ?Q x) $ 0"
  have Q_measurable: "?Q \<in> measurable (lborel :: slp_point measure) borel"
    using slp_quarter_turn_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have forward_integrable: "integrable lborel (\<lambda>x. h (?Q x))"
    if h_int: "integrable lborel h" for h :: slp_scalar_field
    by (rule integrable_distr[OF Q_measurable])
      (simp add: slp_quarter_turn_distr_lborel h_int)
  have backward_integral:
      "integrable lborel h \<and>
        integral\<^sup>L lborel h = integral\<^sup>L lborel (\<lambda>x. h (?Q x))"
    if pullback_int: "integrable lborel (\<lambda>x. h (?Q x))"
    for h :: slp_scalar_field
  proof -
    have h_int: "integrable lborel h"
      using forward_integrable[OF forward_integrable[
        OF forward_integrable[OF pullback_int]]]
      by simp
    have h_measurable: "h \<in> borel_measurable (borel :: slp_point measure)"
      using borel_measurable_integrable[OF h_int]
      by (simp only: measurable_cong_sets[OF sets_lborel refl])
    have integral_eq:
        "integral\<^sup>L lborel h = integral\<^sup>L lborel (\<lambda>x. h (?Q x))"
      using integral_distr[OF Q_measurable h_measurable]
      by (simp only: slp_quarter_turn_distr_lborel)
    show ?thesis by (rule conjI[OF h_int integral_eq])
  qed
  have Q_injective: "inj ?Q"
  proof (rule injI)
    fix x y
    assume "?Q x = ?Q y"
    hence "?Q (?Q x) = ?Q (?Q y)" by simp
    thus "x = y" by simp
  qed
  have Q_membership: "?Q x \<in> ?Y \<longleftrightarrow> x \<in> X" for x
    using Q_injective unfolding inj_def by auto
  have index_cases: "i = (0::2) \<or> i = 1" for i
    using exhaust_2[of i] by auto
  have axis_zero: "?Q (axis 0 1) = axis 1 1"
    unfolding vec_eq_iff
  proof (intro allI)
    fix i :: 2
    show "?Q (axis 0 1) $ i = axis 1 1 $ i"
      using index_cases[of i]
      by (auto simp: axis_def slp_quarter_turn_def)
  qed
  have axis_one: "?Q (axis 1 1) = - axis 0 1"
    unfolding vec_eq_iff
  proof (intro allI)
    fix i :: 2
    show "?Q (axis 1 1) $ i = (- axis 0 1) $ i"
      using index_cases[of i]
      by (auto simp: axis_def slp_quarter_turn_def)
  qed
  have Q_diff: "?Q differentiable (at x)" for x
    by (rule linear_imp_differentiable[OF slp_quarter_turn_linear])
  have Q_derivative: "frechet_derivative ?Q (at x) = ?Q" for x
    using frechet_derivative_at[
      OF linear_imp_has_derivative[OF slp_quarter_turn_linear]] by simp
  show ?thesis
    unfolding slp_weak_gradient_on_def
  proof (intro allI impI)
    fix phi i
    assume phi_test: "slp_test_function_on ?Y phi"
    let ?psi = "\<lambda>x. phi (?Q x)"
    let ?j = "if i = (0::2) then 1 else 0"
    let ?s = "if i = (0::2) then (-1::complex) else 1"
    have psi_test: "slp_test_function_on X ?psi"
      using conjunct2[OF slp_test_function_on_quarter_turn_domains[OF phi_test]]
      by (simp add: image_image)
    have phi_smooth: "smooth_on UNIV phi"
      using phi_test unfolding slp_test_function_on_def by blast
    have phi_diff: "phi differentiable (at x)" for x
      using smooth_on_imp_differentiable_on[OF phi_smooth]
      by (simp add: differentiable_on_def)
    have chain:
        "frechet_derivative ?psi (at x) =
          frechet_derivative phi (at (?Q x)) \<circ> ?Q" for x
      using frechet_derivative_compose[OF Q_diff[of x] phi_diff[of "?Q x"]]
      by (simp add: comp_def Q_derivative)
    have partial_zero:
        "slp_complex_partial_derivative ?psi 0 x =
          slp_complex_partial_derivative phi 1 (?Q x)" for x
      unfolding slp_complex_partial_derivative_def
      by (simp add: chain axis_zero)
    have partial_one:
        "slp_complex_partial_derivative ?psi 1 x =
          - slp_complex_partial_derivative phi 0 (?Q x)" for x
      unfolding slp_complex_partial_derivative_def
      by (simp add: chain axis_one
            linear_neg[OF linear_frechet_derivative[OF phi_diff]])
    have source:
        "set_integrable lborel X
            (\<lambda>x. u x * slp_complex_partial_derivative ?psi ?j x) \<and>
          set_integrable lborel X (\<lambda>x. Du x $ ?j * ?psi x) \<and>
          set_lebesgue_integral lborel X
            (\<lambda>x. u x * slp_complex_partial_derivative ?psi ?j x) =
          - set_lebesgue_integral lborel X (\<lambda>x. Du x $ ?j * ?psi x)"
      using slp_w1p_pair_onD(1)[OF pair] psi_test
      unfolding slp_weak_gradient_on_def by blast
    let ?H = "\<lambda>x. indicator X x *\<^sub>R
      (u x * slp_complex_partial_derivative ?psi ?j x)"
    let ?G = "\<lambda>x. indicator X x *\<^sub>R (Du x $ ?j * ?psi x)"
    let ?A = "\<lambda>x. indicator ?Y x *\<^sub>R
      (?v x * slp_complex_partial_derivative phi i x)"
    let ?B = "\<lambda>x. indicator ?Y x *\<^sub>R (?Dv x $ i * phi x)"
    have first_pullback: "(\<lambda>x. ?A (?Q x)) = (\<lambda>x. ?s * ?H x)"
      by (rule ext)
        (insert index_cases[of i],
          auto simp: Q_membership partial_zero partial_one indicator_def)
    have second_pullback: "(\<lambda>x. ?B (?Q x)) = (\<lambda>x. ?s * ?G x)"
      by (rule ext)
        (insert index_cases[of i], auto simp: Q_membership indicator_def)
    have H_int: "integrable lborel ?H" and G_int: "integrable lborel ?G"
      using source unfolding set_integrable_def by blast+
    have signed_H_int: "integrable lborel (\<lambda>x. ?s * ?H x)"
      by (rule integrable_mult_right) (use H_int in simp)
    have signed_G_int: "integrable lborel (\<lambda>x. ?s * ?G x)"
      by (rule integrable_mult_right) (use G_int in simp)
    have A_pullback_int: "integrable lborel (\<lambda>x. ?A (?Q x))"
      using signed_H_int by (simp only: first_pullback)
    have B_pullback_int: "integrable lborel (\<lambda>x. ?B (?Q x))"
      using signed_G_int by (simp only: second_pullback)
    note A_transport = backward_integral[OF A_pullback_int]
    note B_transport = backward_integral[OF B_pullback_int]
    have source_identity: "integral\<^sup>L lborel ?H = - integral\<^sup>L lborel ?G"
      using source unfolding set_lebesgue_integral_def by blast
    have A_identity:
        "integral\<^sup>L lborel ?A = ?s * integral\<^sup>L lborel ?H"
      using conjunct2[OF A_transport]
      by (simp only: first_pullback integral_mult_right_zero)
    have B_identity:
        "integral\<^sup>L lborel ?B = ?s * integral\<^sup>L lborel ?G"
      using conjunct2[OF B_transport]
      by (simp only: second_pullback integral_mult_right_zero)
    have identity: "integral\<^sup>L lborel ?A = - integral\<^sup>L lborel ?B"
      by (simp only: A_identity B_identity source_identity mult_minus_right)
    show "set_integrable lborel ?Y
          (\<lambda>x. ?v x * slp_complex_partial_derivative phi i x) \<and>
        set_integrable lborel ?Y (\<lambda>x. ?Dv x $ i * phi x) \<and>
        set_lebesgue_integral lborel ?Y
          (\<lambda>x. ?v x * slp_complex_partial_derivative phi i x) =
          - set_lebesgue_integral lborel ?Y (\<lambda>x. ?Dv x $ i * phi x)"
      unfolding set_integrable_def set_lebesgue_integral_def
      by (rule conjI[OF conjunct1[OF A_transport]
            conjI[OF conjunct1[OF B_transport] identity]])
  qed
qed

section \<open>Preservation of the local Sobolev pair and norm\<close>

theorem slp_w1p_pair_inverse_quarter_turn:
  assumes pair: "slp_w1p_pair_on p X u Du"
  shows "slp_w1p_pair_on p (image slp_quarter_turn X)
      (\<lambda>x. u (- slp_quarter_turn x))
      (\<lambda>x. \<chi> i. if i = 0 then - Du (- slp_quarter_turn x) $ 1
        else Du (- slp_quarter_turn x) $ 0) \<and>
    slp_w1p_norm_on p (image slp_quarter_turn X)
      (\<lambda>x. u (- slp_quarter_turn x))
      (\<lambda>x. \<chi> i. if i = 0 then - Du (- slp_quarter_turn x) $ 1
        else Du (- slp_quarter_turn x) $ 0) =
      slp_w1p_norm_on p X u Du"
proof -
  let ?Q = slp_quarter_turn
  let ?Y = "image ?Q X"
  let ?v = "\<lambda>x. u (- ?Q x)"
  let ?Dv = "(\<lambda>x. \<chi> i. if i = 0 then - Du (- ?Q x) $ 1
    else Du (- ?Q x) $ 0) :: slp_gradient_field"
  have Q_measurable: "?Q \<in> measurable (lborel :: slp_point measure) borel"
    using slp_quarter_turn_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have power_turn:
      "integral\<^sup>L lborel (\<lambda>x. norm (h (?Q x)) powr p) =
        integral\<^sup>L lborel (\<lambda>x. norm (h x) powr p)"
    if h_lp: "aim_complex_lp_on_plane p h" for h :: slp_scalar_field
  proof -
    have h_lborel: "h \<in> borel_measurable (lborel :: slp_point measure)"
      using h_lp unfolding aim_complex_lp_on_plane_def by blast
    have h_measurable: "h \<in> borel_measurable (borel :: slp_point measure)"
      using h_lborel
      by (simp only: measurable_cong_sets[OF sets_lborel refl])
    have power_measurable:
        "(\<lambda>x. norm (h x) powr p) \<in>
          borel_measurable (borel :: slp_point measure)"
      using h_measurable by measurable
    show ?thesis
      using integral_distr[OF Q_measurable power_measurable]
      by (simp only: slp_quarter_turn_distr_lborel)
  qed
  have inverse_transport:
      "aim_complex_lp_on_plane p (\<lambda>x. h (- ?Q x)) \<and>
        integral\<^sup>L lborel (\<lambda>x. norm (h (- ?Q x)) powr p) =
          integral\<^sup>L lborel (\<lambda>x. norm (h x) powr p)"
    if h_lp: "aim_complex_lp_on_plane p h" for h :: slp_scalar_field
  proof -
    have first_lp: "aim_complex_lp_on_plane p (\<lambda>x. h (?Q x))"
      by (rule conjunct1[OF slp_aim_complex_lp_on_plane_quarter_turn[OF h_lp]])
    have second_lp: "aim_complex_lp_on_plane p (\<lambda>x. h (?Q (?Q x)))"
      by (rule conjunct1[OF slp_aim_complex_lp_on_plane_quarter_turn[OF first_lp]])
    have third_lp:
        "aim_complex_lp_on_plane p (\<lambda>x. h (?Q (?Q (?Q x))))"
      by (rule conjunct1[OF slp_aim_complex_lp_on_plane_quarter_turn[OF second_lp]])
    have third_power:
        "integral\<^sup>L lborel (\<lambda>x. norm (h (?Q (?Q (?Q x)))) powr p) =
          integral\<^sup>L lborel (\<lambda>x. norm (h x) powr p)"
      using power_turn[OF second_lp] power_turn[OF first_lp] power_turn[OF h_lp]
      by simp
    show ?thesis using third_lp third_power
      by (simp add: linear_neg[OF slp_quarter_turn_linear])
  qed
  have R_membership: "- ?Q x \<in> X \<longleftrightarrow> x \<in> ?Y" for x
  proof
    assume source: "- ?Q x \<in> X"
    have "?Q (- ?Q x) \<in> ?Y" by (rule imageI[OF source])
    thus "x \<in> ?Y" by simp
  next
    assume "x \<in> ?Y"
    then obtain y where "y \<in> X" "x = ?Q y" by blast
    thus "- ?Q x \<in> X" by simp
  qed
  have restrict_transport:
      "slp_restrict_field ?Y (\<lambda>x. h (- ?Q x)) =
        (\<lambda>x. slp_restrict_field X h (- ?Q x))"
    for h :: slp_scalar_field
    by (rule ext) (simp add: slp_restrict_field_def R_membership)
  have restrict_neg:
      "slp_restrict_field Y (\<lambda>x. - h x) =
        (\<lambda>x. - slp_restrict_field Y h x)"
    for Y and h :: slp_scalar_field
    by (rule ext) (simp add: slp_restrict_field_def)
  have value_field:
      "slp_restrict_field ?Y ?v = (\<lambda>x. slp_restrict_field X u (- ?Q x))"
    by (rule restrict_transport)
  have zero_field:
      "slp_restrict_field ?Y (\<lambda>x. ?Dv x $ 0) =
        (\<lambda>x. - slp_restrict_field X (\<lambda>y. Du y $ 1) (- ?Q x))"
    by (simp add: restrict_neg restrict_transport[of "\<lambda>y. Du y $ 1"])
  have one_field:
      "slp_restrict_field ?Y (\<lambda>x. ?Dv x $ 1) =
        (\<lambda>x. slp_restrict_field X (\<lambda>y. Du y $ 0) (- ?Q x))"
    by (simp add: restrict_transport[of "\<lambda>y. Du y $ 0"])
  have value_source: "aim_complex_lp_on_plane p (slp_restrict_field X u)"
    using slp_w1p_pair_onD(2)[OF pair] unfolding slp_complex_lp_on_def .
  have zero_source:
      "aim_complex_lp_on_plane p (slp_restrict_field X (\<lambda>x. Du x $ 0))"
    using slp_w1p_pair_onD(3)[OF pair] unfolding slp_complex_lp_on_def .
  have one_source:
      "aim_complex_lp_on_plane p (slp_restrict_field X (\<lambda>x. Du x $ 1))"
    using slp_w1p_pair_onD(4)[OF pair] unfolding slp_complex_lp_on_def .
  note value_transport = inverse_transport[OF value_source]
  note zero_transport = inverse_transport[OF zero_source]
  note one_transport = inverse_transport[OF one_source]
  have value_lp: "slp_complex_lp_on p ?Y ?v"
    unfolding slp_complex_lp_on_def
    using conjunct1[OF value_transport] by (simp only: value_field)
  have zero_lp: "slp_complex_lp_on p ?Y (\<lambda>x. ?Dv x $ 0)"
    unfolding slp_complex_lp_on_def
    using aim_complex_lp_on_plane_uminus[OF conjunct1[OF one_transport]]
    by (simp only: zero_field)
  have one_lp: "slp_complex_lp_on p ?Y (\<lambda>x. ?Dv x $ 1)"
    unfolding slp_complex_lp_on_def
    using conjunct1[OF zero_transport] by (simp only: one_field)
  have rotated_pair: "slp_w1p_pair_on p ?Y ?v ?Dv"
    using slp_w1p_pair_inverse_quarter_turn_weak_gradient[OF pair]
      value_lp zero_lp one_lp
    unfolding slp_w1p_pair_on_def by blast
  have norm_identity: "slp_w1p_norm_on p ?Y ?v ?Dv = slp_w1p_norm_on p X u Du"
    unfolding slp_w1p_norm_on_def
    by (simp only: value_field zero_field one_field norm_minus_cancel
          conjunct2[OF value_transport] conjunct2[OF zero_transport]
          conjunct2[OF one_transport]; simp add: algebra_simps)
  show ?thesis by (rule conjI[OF rotated_pair norm_identity])
qed

end
