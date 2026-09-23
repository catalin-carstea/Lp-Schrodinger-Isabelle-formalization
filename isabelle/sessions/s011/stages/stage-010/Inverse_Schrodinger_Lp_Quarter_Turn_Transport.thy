theory Inverse_Schrodinger_Lp_Quarter_Turn_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Planar_Pair_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Zero_Branch_Checked_Sign_Gain"
begin

section \<open>Quarter-turn transport on the project plane\<close>

definition slp_quarter_turn :: "slp_point \<Rightarrow> slp_point" where
  "slp_quarter_turn x =
    (\<chi> i. if i = (0 :: 2) then - x $ (1 :: 2) else x $ (0 :: 2))"

lemma slp_quarter_turn_zero [simp]:
  "slp_quarter_turn x $ (0 :: 2) = - x $ (1 :: 2)"
  by (simp add: slp_quarter_turn_def)

lemma slp_quarter_turn_one [simp]:
  "slp_quarter_turn x $ (1 :: 2) = x $ (0 :: 2)"
  by (simp add: slp_quarter_turn_def)

lemma slp_quarter_turn_twice [simp]:
  "slp_quarter_turn (slp_quarter_turn x) = - x"
  unfolding vec_eq_iff
proof (intro allI)
  fix i :: 2
  have two_is_zero: "(2 :: 2) = 0"
    by simp
  have i_cases: "i = 1 \<or> i = (2 :: 2)"
    by (rule exhaust_2)
  show "slp_quarter_turn (slp_quarter_turn x) $ i = (- x) $ i"
    using i_cases two_is_zero
    by (auto simp: slp_quarter_turn_def)
qed

lemma slp_quarter_turn_neg_inverse [simp]:
  "slp_quarter_turn (- slp_quarter_turn x) = x"
  unfolding vec_eq_iff
proof (intro allI)
  fix i :: 2
  have two_is_zero: "(2 :: 2) = 0"
    by simp
  have i_cases: "i = 1 \<or> i = (2 :: 2)"
    by (rule exhaust_2)
  show "slp_quarter_turn (- slp_quarter_turn x) $ i = x $ i"
    using i_cases two_is_zero
    by (auto simp: slp_quarter_turn_def)
qed

lemma slp_quarter_turn_linear:
  "linear slp_quarter_turn"
  by (rule linearI)
    (simp_all add: slp_quarter_turn_def vec_eq_iff)

lemma slp_quarter_turn_continuous:
  "continuous_on UNIV slp_quarter_turn"
proof -
  have bounded: "bounded_linear slp_quarter_turn"
    using slp_quarter_turn_linear
    by (simp add: linear_conv_bounded_linear)
  show ?thesis
    by (rule linear_continuous_on[OF bounded])
qed

lemma slp_quarter_turn_measurable:
  "slp_quarter_turn \<in>
    measurable (borel :: slp_point measure) borel"
  by (rule borel_measurable_continuous_onI[OF
        slp_quarter_turn_continuous])

lemma slp_quarter_turn_as_complex [simp]:
  "slp_point_as_complex (slp_quarter_turn x) =
    \<i> * slp_point_as_complex x"
  apply (rule complex_eqI)
  subgoal
    by (simp only: slp_point_as_complex_def slp_quarter_turn_zero
        complex.sel Re_i_times)
  subgoal
    by (simp only: slp_point_as_complex_def slp_quarter_turn_one
        complex.sel Im_i_times)
  done

lemma slp_quarter_turn_norm [simp]:
  "norm_class.norm (slp_quarter_turn x) = norm_class.norm x"
proof -
  have "norm_class.norm (slp_quarter_turn x) =
      norm_class.norm (slp_point_as_complex (slp_quarter_turn x))"
    by (simp only: slp_point_as_complex_norm)
  also have "... =
      norm_class.norm (\<i> * slp_point_as_complex x)"
    by (simp only: slp_quarter_turn_as_complex)
  also have "... = norm_class.norm (slp_point_as_complex x)"
    by (simp only: norm_mult norm_ii mult.left_neutral)
  also have "... = norm_class.norm x"
    by (simp only: slp_point_as_complex_norm)
  finally show ?thesis .
qed

lemma slp_center_phase_quarter_turn [simp]:
  "slp_center_phase (slp_quarter_turn c) (slp_quarter_turn z) =
    - slp_center_phase c z"
  unfolding slp_center_phase_def
  by (simp only: slp_quarter_turn_zero slp_quarter_turn_one
      minus_diff_minus power2_minus minus_diff_eq power2_commute)

lemma slp_quarter_turn_compact_image:
  assumes Z_compact: "compact Z"
  shows "compact (slp_quarter_turn ` Z)"
  by (rule compact_continuous_image[OF
        continuous_on_subset[OF slp_quarter_turn_continuous subset_UNIV]
        Z_compact])

lemma slp_quarter_turn_distr_lborel:
  "distr (lborel :: slp_point measure) borel slp_quarter_turn = lborel"
proof -
  let ?S = "\<lambda>xy::real \<times> real. (snd xy, fst xy)"
  let ?N = "\<lambda>xy::real \<times> real. (- fst xy, snd xy)"
  let ?Q = "\<lambda>xy::real \<times> real. (- snd xy, fst xy)"
  have S_measurable:
      "?S \<in> measurable (borel :: (real \<times> real) measure) borel"
  proof -
    have raw:
        "(\<lambda>(x::real, y::real). (y, x)) \<in>
          measurable
            ((borel :: real measure) \<Otimes>\<^sub>M borel)
            ((borel :: real measure) \<Otimes>\<^sub>M borel)"
      by (rule measurable_pair_swap')
    show ?thesis
      using raw by (simp only: borel_prod split_beta')
  qed
  have S_lborel_measurable:
      "?S \<in> measurable (lborel :: (real \<times> real) measure) borel"
    using S_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have N_measurable:
      "?N \<in> measurable (borel :: (real \<times> real) measure) borel"
  proof -
    have raw:
        "(\<lambda>(x::real, y::real). (- x, y)) \<in>
          measurable
            ((borel :: real measure) \<Otimes>\<^sub>M borel)
            ((borel :: real measure) \<Otimes>\<^sub>M borel)"
      by measurable
    show ?thesis
      using raw by (simp only: borel_prod split_beta')
  qed
  have Q_measurable:
      "?Q \<in> measurable (borel :: (real \<times> real) measure) borel"
  proof -
    have raw:
        "(\<lambda>(x::real, y::real). (- y, x)) \<in>
          measurable
            ((borel :: real measure) \<Otimes>\<^sub>M borel)
            ((borel :: real measure) \<Otimes>\<^sub>M borel)"
      by measurable
    show ?thesis
      using raw by (simp only: borel_prod split_beta')
  qed
  have S_distr:
      "distr (lborel :: (real \<times> real) measure) borel ?S = lborel"
  proof -
    have same_target:
        "distr (lborel :: (real \<times> real) measure) lborel ?S =
          (lborel :: (real \<times> real) measure)"
      using lborel_pair.distr_pair_swap[symmetric]
      by (simp only: lborel_prod split_beta')
    have target_change:
        "distr (lborel :: (real \<times> real) measure) borel ?S =
          distr (lborel :: (real \<times> real) measure) lborel ?S"
    proof (rule distr_cong)
      show "(lborel :: (real \<times> real) measure) = lborel"
        by (rule refl)
      show "sets (borel :: (real \<times> real) measure) = sets lborel"
        by (rule sym, rule sets_lborel)
      show "\<And>x. x \<in> space (lborel :: (real \<times> real) measure) \<Longrightarrow>
          ?S x = ?S x"
        by (rule refl)
    qed
    show ?thesis
      by (rule trans[OF target_change same_target])
  qed
  have N_distr:
      "distr (lborel :: (real \<times> real) measure) borel ?N = lborel"
  proof -
    have minus_measurable:
        "uminus \<in> measurable (lborel :: real measure) borel"
      by measurable
    have id_measurable:
        "(id :: real \<Rightarrow> real) \<in>
          measurable (lborel :: real measure) borel"
      by measurable
    have id_distr:
        "distr (lborel :: real measure) borel id = lborel"
      unfolding id_def
      by (rule distr_id2) (simp only: sets_lborel)
    have id_sigma:
        "sigma_finite_measure
          (distr (lborel :: real measure) borel id)"
      using sigma_finite_lborel
      by (simp only: id_distr)
    have paired:
        "distr (lborel :: real measure) borel uminus \<Otimes>\<^sub>M
            distr (lborel :: real measure) borel id =
          distr ((lborel :: real measure) \<Otimes>\<^sub>M lborel)
            (borel \<Otimes>\<^sub>M borel) ?N"
    proof -
      have raw:
          "distr (lborel :: real measure) borel uminus \<Otimes>\<^sub>M
              distr (lborel :: real measure) borel id =
            distr ((lborel :: real measure) \<Otimes>\<^sub>M lborel)
              (borel \<Otimes>\<^sub>M borel)
                (\<lambda>(x, y). (uminus x, id y))"
        by (rule pair_measure_distr[OF
              minus_measurable id_measurable id_sigma])
      show ?thesis
        using raw by (simp only: split_beta' id_apply)
    qed
    have product_target:
        "distr (lborel :: (real \<times> real) measure)
            ((borel :: real measure) \<Otimes>\<^sub>M borel) ?N =
          (lborel :: (real \<times> real) measure)"
      using paired[symmetric]
      by (simp only: lborel_distr_uminus id_distr lborel_prod)
    have target_change:
        "distr (lborel :: (real \<times> real) measure) borel ?N =
          distr (lborel :: (real \<times> real) measure)
            ((borel :: real measure) \<Otimes>\<^sub>M borel) ?N"
    proof (rule distr_cong)
      show "(lborel :: (real \<times> real) measure) = lborel"
        by (rule refl)
      show "sets (borel :: (real \<times> real) measure) =
          sets ((borel :: real measure) \<Otimes>\<^sub>M borel)"
        by (simp only: borel_prod)
      show "\<And>x. x \<in> space (lborel :: (real \<times> real) measure) \<Longrightarrow>
          ?N x = ?N x"
        by (rule refl)
    qed
    show ?thesis
      by (rule trans[OF target_change product_target])
  qed
  have Q_composition: "?Q = ?N \<circ> ?S"
    by (rule ext) auto
  have Q_distr:
      "distr (lborel :: (real \<times> real) measure) borel ?Q = lborel"
  proof -
    have composed:
        "distr (distr (lborel :: (real \<times> real) measure) borel ?S)
            borel ?N =
          distr (lborel :: (real \<times> real) measure) borel (?N \<circ> ?S)"
      by (rule distr_distr[OF N_measurable S_lborel_measurable])
    show ?thesis
      using composed
      by (simp only: S_distr N_distr Q_composition)
  qed
  have to_pair_measurable:
      "slp_point_to_pair \<in>
        measurable (borel :: slp_point measure) borel"
    by (rule slp_point_to_pair_measurable)
  have to_pair_lborel_measurable:
      "slp_point_to_pair \<in>
        measurable (lborel :: slp_point measure) borel"
    using to_pair_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have from_pair_measurable:
      "slp_pair_to_point \<in>
        measurable (borel :: (real \<times> real) measure) borel"
    by (rule slp_pair_to_point_measurable)
  have map_composition:
      "slp_quarter_turn = slp_pair_to_point \<circ> ?Q \<circ>
        slp_point_to_pair"
    by (rule ext)
      (simp add: slp_quarter_turn_def slp_pair_to_point_def
        slp_point_to_pair_def vec_eq_iff)
  have first_composition:
      "distr
          (distr (lborel :: slp_point measure) borel slp_point_to_pair)
          borel ?Q =
        distr (lborel :: slp_point measure) borel
          (?Q \<circ> slp_point_to_pair)"
    by (rule distr_distr[OF Q_measurable to_pair_lborel_measurable])
  have Q_to_pair_measurable:
      "(?Q \<circ> slp_point_to_pair) \<in>
        measurable (lborel :: slp_point measure) borel"
    by (rule measurable_comp[OF
          to_pair_lborel_measurable Q_measurable])
  have second_composition:
      "distr
          (distr (lborel :: slp_point measure) borel
            (?Q \<circ> slp_point_to_pair))
          borel slp_pair_to_point =
        distr (lborel :: slp_point measure) borel
          (slp_pair_to_point \<circ> ?Q \<circ> slp_point_to_pair)"
  proof -
    have raw:
        "distr
            (distr (lborel :: slp_point measure) borel
              (?Q \<circ> slp_point_to_pair))
            borel slp_pair_to_point =
          distr (lborel :: slp_point measure) borel
            (slp_pair_to_point \<circ> (?Q \<circ> slp_point_to_pair))"
      by (rule distr_distr[OF
            from_pair_measurable Q_to_pair_measurable])
    show ?thesis
      using raw by (simp only: comp_assoc)
  qed
  show ?thesis
    using first_composition second_composition
    by (simp only: map_composition slp_point_to_pair_distr_lborel
        Q_distr slp_pair_to_point_distr_lborel)
qed

lemma slp_aim_complex_lp_on_plane_quarter_turn:
  assumes f_lp: "aim_complex_lp_on_plane p f"
  shows
    "aim_complex_lp_on_plane p (\<lambda>x. f (slp_quarter_turn x)) \<and>
      aim_complex_lp_norm p (\<lambda>x. f (slp_quarter_turn x)) =
        aim_complex_lp_norm p f"
proof -
  have R_measurable:
      "slp_quarter_turn \<in>
        measurable (lborel :: slp_point measure) borel"
    using slp_quarter_turn_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have f_measurable: "f \<in> borel_measurable lborel"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (f x) powr p)"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast+
  have f_borel_measurable:
      "f \<in> borel_measurable (borel :: slp_point measure)"
    using f_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have pullback_measurable:
      "(\<lambda>x. f (slp_quarter_turn x)) \<in> borel_measurable lborel"
    using measurable_comp[OF R_measurable f_borel_measurable]
    by (simp only: comp_def)
  let ?u = "\<lambda>x. norm_class.norm (f x) powr p"
  have u_borel_measurable:
      "?u \<in> borel_measurable (borel :: slp_point measure)"
    using f_borel_measurable by measurable
  have pullback_power_integrable:
      "integrable lborel
        (\<lambda>x. norm_class.norm (f (slp_quarter_turn x)) powr p)"
  proof -
    have transported:
        "integrable (distr (lborel :: slp_point measure) borel
            slp_quarter_turn) ?u \<longleftrightarrow>
          integrable lborel (\<lambda>x. ?u (slp_quarter_turn x))"
      by (rule integrable_distr_eq[OF R_measurable u_borel_measurable])
    show ?thesis
      using transported f_power_integrable
      by (simp only: slp_quarter_turn_distr_lborel comp_def)
  qed
  have pullback_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. f (slp_quarter_turn x))"
    unfolding aim_complex_lp_on_plane_def
    by (rule conjI[OF pullback_measurable pullback_power_integrable])
  have pullback_power_integral:
      "integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (f (slp_quarter_turn x)) powr p) =
        integral\<^sup>L lborel (\<lambda>x. norm_class.norm (f x) powr p)"
  proof -
    have transported:
        "integral\<^sup>L
            (distr (lborel :: slp_point measure) borel slp_quarter_turn) ?u =
          integral\<^sup>L lborel (\<lambda>x. ?u (slp_quarter_turn x))"
      by (rule integral_distr[OF R_measurable u_borel_measurable])
    show ?thesis
      using transported
      by (simp only: slp_quarter_turn_distr_lborel comp_def)
  qed
  have pullback_norm:
      "aim_complex_lp_norm p (\<lambda>x. f (slp_quarter_turn x)) =
        aim_complex_lp_norm p f"
    unfolding aim_complex_lp_norm_def
    by (simp only: pullback_power_integral)
  show ?thesis
    by (rule conjI[OF pullback_lp pullback_norm])
qed

end
