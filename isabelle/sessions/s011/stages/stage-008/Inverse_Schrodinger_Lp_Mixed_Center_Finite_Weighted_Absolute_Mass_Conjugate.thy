theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_Conjugate
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Test_Two_Cauchy_Product_Half_HLS"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_One_Terminal"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Weighted absolute mass at conjugate center exponents\<close>

theorem slp_mixed_center_finite_weighted_absolute_mass_conjugate_finite:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B q r :: real
    and root_weight cutoff left_potential left_terminal_value
      right_potential right_terminal_value center_factor :: slp_scalar_field
  assumes q_lower: "1 < q"
    and r_lower: "1 < r"
    and conjugate: "1 / q + 1 / r = 1"
    and B_nonnegative: "0 \<le> B"
    and root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal_value \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal_value \<in> borel_measurable lborel"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm_class.norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm_class.norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm_class.norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm_class.norm x \<le> B"
    and density_Lq:
      "slp_positive_ennreal_lp_on_plane q
        (slp_mixed_center_density (2 * B) cutoff left_potential
          right_potential
          (\<lambda>x. ennreal (cmod (left_terminal_value x)))
          (\<lambda>x. ennreal (cmod (right_terminal_value x)))
          CARD('i) CARD('j) root_weight)"
    and center_factor_Lr:
      "aim_complex_lp_on_plane r center_factor"
  shows
    "(\<integral>\<^sup>+ center.
      slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight cutoff left_potential
        left_terminal_value cutoff right_potential right_terminal_value
        center_factor center \<partial>lborel) < top_class.top"
proof -
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>x. ennreal (cmod (left_terminal_value x)))
      (\<lambda>x. ennreal (cmod (right_terminal_value x)))
      CARD('i) CARD('j) root_weight"
  have fiber_bound:
      "slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential
          left_terminal_value cutoff right_potential right_terminal_value
          center_factor center \<le>
        ennreal (cmod (center_factor center)) * ?density center"
    for center
    by (rule
      slp_mixed_center_finite_weighted_absolute_fiber_mass_density_bound[OF
        B_nonnegative root_weight_measurable cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_potential_measurable right_terminal_measurable root_support
        cutoff_support left_potential_support right_potential_support])
  have pairing_finite:
      "(\<integral>\<^sup>+ center.
        ?density center * ennreal (norm_class.norm (center_factor center))
        \<partial>lborel) < top_class.top"
    by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[OF
          q_lower r_lower conjugate density_Lq center_factor_Lr])
  have mass_le:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential
          left_terminal_value cutoff right_potential right_terminal_value
          center_factor center \<partial>lborel) \<le>
        (\<integral>\<^sup>+ center.
          ?density center *
            ennreal (norm_class.norm (center_factor center))
          \<partial>lborel)"
    apply (rule nn_integral_mono)
    using fiber_bound by (simp add: mult.commute)
  show ?thesis
    by (rule le_less_trans[OF mass_le pairing_finite])
qed

end
