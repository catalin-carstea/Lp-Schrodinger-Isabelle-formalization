theory Inverse_Schrodinger_Lp_Squared_Radial_Annulus_Power_Geometric
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Squared_Radial_Annulus_Power_Shell"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Annulus_Logarithmic_Growth"
begin

section \<open>Geometric control of powered annuli\<close>

lemma slp_squared_radial_annulus_power_ratio_bounds:
  assumes exponent_strict: "1 < s"
  shows
    "0 < (2::real) powr (2 - 2 * s)"
    "(2::real) powr (2 - 2 * s) < 1"
proof -
  show "0 < (2::real) powr (2 - 2 * s)"
    by simp
  have exponent_negative: "2 - 2 * s < (0::real)"
    using exponent_strict by linarith
  have power_less:
    "(2::real) powr (2 - 2 * s) < 2 powr 0"
    by (rule powr_less_mono[OF exponent_negative]) simp
  show "(2::real) powr (2 - 2 * s) < 1"
    using power_less by simp
qed

lemma slp_squared_radial_annulus_power_unit_zero:
  assumes exponent_positive: "0 < s"
  shows
    "integral\<^sup>L lborel
      (slp_squared_radial_annulus_power s 1 1) = 0"
proof -
  have sphere_negligible: "negligible (sphere (0::slp_point) 1)"
    by (rule negligible_sphere)
  have sphere_null: "sphere (0::slp_point) 1 \<in> null_sets lborel"
    using sphere_negligible
    by (auto simp: negligible_iff_null_sets null_sets_completion_iff)
  have outside_sphere:
    "AE y in (lborel :: slp_point measure). y \<notin> sphere 0 1"
    by (rule AE_not_in[OF sphere_null])
  have ae_zero:
    "AE y in lborel.
      slp_squared_radial_annulus_power s 1 1 y = 0"
  proof (rule eventually_mono[OF outside_sphere])
    fix y :: slp_point
    assume outside: "y \<notin> sphere 0 1"
    have not_boundary: "norm y \<noteq> 1"
      using outside by (simp add: sphere_def dist_norm)
    show "slp_squared_radial_annulus_power s 1 1 y = 0"
      unfolding slp_squared_radial_annulus_power_def
        slp_squared_radial_annulus_def
      using exponent_positive not_boundary by auto
  qed
  show ?thesis
    by (rule integral_eq_zero_AE[OF ae_zero])
qed

lemma slp_squared_radial_annulus_power_dyadic_geometric:
  assumes exponent_lower: "1 \<le> s"
  shows
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s 1 ((2::real) ^ n)) =
      (\<Sum>k<n. ((2::real) powr (2 - 2 * s)) ^ k) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s 1 2)"
proof (induction n)
  case 0
  have exponent_positive: "0 < s"
    using exponent_lower by linarith
  show ?case
    using slp_squared_radial_annulus_power_unit_zero[
      OF exponent_positive]
    by simp
next
  case (Suc n)
  have power_lower: "1 \<le> (2::real) ^ n"
    by simp
  have recurrence:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power
          s 1 (((2::real) ^ n) * 2)) =
      integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s 1 ((2::real) ^ n)) +
        ((2::real) ^ n) powr (2 - 2 * s) *
          integral\<^sup>L lborel
            (slp_squared_radial_annulus_power s 1 2)"
    by (rule slp_squared_radial_annulus_power_multiplicative_recurrence[
          OF power_lower _ exponent_lower]) simp
  have natural_power_as_powr:
    "(2::real) ^ n = 2 powr (real n)"
    by (rule sym, rule powr_realpow) simp
  have left_coefficient:
    "((2::real) ^ n) powr (2 - 2 * s) =
      2 powr (real n * (2 - 2 * s))"
    by (simp only: natural_power_as_powr powr_powr)
  have right_coefficient:
    "((2::real) powr (2 - 2 * s)) ^ n =
      2 powr (real n * (2 - 2 * s))"
    by (rule powr_power) simp
  have coefficient:
    "((2::real) ^ n) powr (2 - 2 * s) =
      ((2::real) powr (2 - 2 * s)) ^ n"
    by (rule trans[OF left_coefficient right_coefficient[symmetric]])
  show ?case
    using recurrence Suc.IH coefficient
    by (simp add: power_Suc sum.lessThan_Suc algebra_simps)
qed

theorem slp_squared_radial_annulus_power_normalized_geometric_majorant:
  assumes radius_lower: "1 \<le> R"
    and exponent_strict: "1 < s"
  shows
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s 1 R) \<le>
      inverse (1 - (2::real) powr (2 - 2 * s)) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s 1 2)"
proof -
  let ?rho = "(2::real) powr (2 - 2 * s)"
  let ?n = "slp_dyadic_index R"
  let ?C =
    "integral\<^sup>L lborel
      (slp_squared_radial_annulus_power s 1 2)"
  have exponent_lower: "1 \<le> s"
    using exponent_strict by linarith
  have rho_positive: "0 < ?rho"
    by (rule slp_squared_radial_annulus_power_ratio_bounds(1)[
          OF exponent_strict])
  have rho_less_one: "?rho < 1"
    by (rule slp_squared_radial_annulus_power_ratio_bounds(2)[
          OF exponent_strict])
  have norm_rho_less_one: "norm ?rho < 1"
    using rho_positive rho_less_one by simp
  have geometric_summable: "summable (\<lambda>k. ?rho ^ k)"
    by (rule summable_geometric[OF norm_rho_less_one])
  have dyadic_upper: "R \<le> (2::real) ^ ?n"
    by (rule slp_dyadic_index_power_upper[OF radius_lower])
  have annulus_upper:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s 1 R) \<le>
      integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s 1 ((2::real) ^ ?n))"
    by (rule slp_squared_radial_annulus_power_upper_mono[
          OF zero_less_one exponent_lower dyadic_upper])
  have dyadic_identity:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s 1 ((2::real) ^ ?n)) =
      (\<Sum>k<?n. ?rho ^ k) * ?C"
    by (rule slp_squared_radial_annulus_power_dyadic_geometric[
          OF exponent_lower])
  have partial_sum_suminf:
    "(\<Sum>k<?n. ?rho ^ k) \<le> suminf (\<lambda>k. ?rho ^ k)"
  proof (rule sum_le_suminf[OF geometric_summable])
    show "finite {..<?n}"
      by simp
    fix k
    assume "k \<in> - {..<?n}"
    show "0 \<le> ?rho ^ k"
      using rho_positive by simp
  qed
  have geometric_value:
    "suminf (\<lambda>k. ?rho ^ k) = 1 / (1 - ?rho)"
    by (rule suminf_geometric[OF norm_rho_less_one])
  have division_inverse:
    "(1::real) / (1 - ?rho) = inverse (1 - ?rho)"
    by (simp add: divide_inverse)
  have suminf_value:
    "suminf (\<lambda>k. ?rho ^ k) = inverse (1 - ?rho)"
    by (rule trans[OF geometric_value division_inverse])
  have partial_sum_bound:
    "(\<Sum>k<?n. ?rho ^ k) \<le> inverse (1 - ?rho)"
    using partial_sum_suminf suminf_value by simp
  have constant_nonnegative: "0 \<le> ?C"
    by (rule Bochner_Integration.integral_nonneg) simp
  have weighted_sum_bound:
    "(\<Sum>k<?n. ?rho ^ k) * ?C \<le>
      inverse (1 - ?rho) * ?C"
    by (rule mult_right_mono[OF partial_sum_bound
          constant_nonnegative])
  have annulus_partial_sum:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s 1 R) \<le>
      (\<Sum>k<?n. ?rho ^ k) * ?C"
    using annulus_upper dyadic_identity by simp
  show ?thesis
    by (rule order_trans[OF annulus_partial_sum weighted_sum_bound])
qed

theorem slp_squared_radial_annulus_power_rescaled_geometric_majorant:
  assumes delta_positive: "0 < delta"
    and radius_lower: "delta \<le> R"
    and exponent_strict: "1 < s"
  shows
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s delta R) \<le>
      delta powr (2 - 2 * s) *
        (inverse (1 - (2::real) powr (2 - 2 * s)) *
          integral\<^sup>L lborel
            (slp_squared_radial_annulus_power s 1 2))"
proof -
  have exponent_lower: "1 \<le> s"
    using exponent_strict by linarith
  have normalized_radius_lower: "1 \<le> R / delta"
    using radius_lower
    by (simp only: le_divide_eq_1_pos[OF delta_positive])
  have normalized_bound:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s 1 (R / delta)) \<le>
      inverse (1 - (2::real) powr (2 - 2 * s)) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s 1 2)"
    by (rule
      slp_squared_radial_annulus_power_normalized_geometric_majorant[
        OF normalized_radius_lower exponent_strict])
  have normalization:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s delta R) =
      delta powr (2 - 2 * s) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s 1 (R / delta))"
    using slp_squared_radial_annulus_power_integral_scale[
        OF delta_positive zero_less_one exponent_lower, of "R / delta"]
      delta_positive
    by simp
  have scale_nonnegative: "0 \<le> delta powr (2 - 2 * s)"
    by simp
  have scaled_bound:
    "delta powr (2 - 2 * s) *
        integral\<^sup>L lborel
          (slp_squared_radial_annulus_power s 1 (R / delta)) \<le>
      delta powr (2 - 2 * s) *
        (inverse (1 - (2::real) powr (2 - 2 * s)) *
          integral\<^sup>L lborel
            (slp_squared_radial_annulus_power s 1 2))"
    by (rule mult_left_mono[OF normalized_bound scale_nonnegative])
  show ?thesis
    using normalization scaled_bound by simp
qed

theorem slp_squared_radial_annulus_power_rescaled_geometric_root_majorant:
  assumes delta_positive: "0 < delta"
    and radius_lower: "delta \<le> R"
    and exponent_strict: "1 < s"
  shows
    "(integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s delta R))
        powr (1 / s) \<le>
      delta powr (2 / s - 2) *
        (inverse (1 - (2::real) powr (2 - 2 * s)) *
          integral\<^sup>L lborel
            (slp_squared_radial_annulus_power s 1 2))
          powr (1 / s)"
proof -
  let ?rho = "(2::real) powr (2 - 2 * s)"
  let ?C =
    "inverse (1 - ?rho) *
      integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s 1 2)"
  have exponent_positive: "0 < s"
    using exponent_strict by linarith
  have exponent_nonzero: "s \<noteq> 0"
    using exponent_positive by simp
  have root_exponent_nonnegative: "0 \<le> 1 / s"
    using exponent_positive by simp
  have integral_nonnegative:
    "0 \<le> integral\<^sup>L lborel
      (slp_squared_radial_annulus_power s delta R)"
    by (rule Bochner_Integration.integral_nonneg) simp
  have rescaled_bound:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s delta R) \<le>
      delta powr (2 - 2 * s) * ?C"
    by (rule
      slp_squared_radial_annulus_power_rescaled_geometric_majorant[
        OF delta_positive radius_lower exponent_strict])
  have lifted_bound:
    "(integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s delta R))
        powr (1 / s) \<le>
      (delta powr (2 - 2 * s) * ?C) powr (1 / s)"
    by (rule powr_mono2[OF root_exponent_nonnegative
          integral_nonnegative rescaled_bound])
  have product_power:
    "(delta powr (2 - 2 * s) * ?C) powr (1 / s) =
      (delta powr (2 - 2 * s)) powr (1 / s) *
        ?C powr (1 / s)"
    by (rule powr_mult)
  have exponent_identity:
    "(2 - 2 * s) * (1 / s) = 2 / s - 2"
    using exponent_nonzero by (simp add: field_simps)
  have root_scale:
    "(delta powr (2 - 2 * s)) powr (1 / s) =
      delta powr (2 / s - 2)"
    by (simp only: powr_powr exponent_identity)
  have normalized:
    "(delta powr (2 - 2 * s)) powr (1 / s) *
        ?C powr (1 / s) =
      delta powr (2 / s - 2) * ?C powr (1 / s)"
    by (simp only: root_scale)
  have lifted_product:
    "(integral\<^sup>L lborel
        (slp_squared_radial_annulus_power s delta R))
        powr (1 / s) \<le>
      (delta powr (2 - 2 * s)) powr (1 / s) *
        ?C powr (1 / s)"
    using lifted_bound product_power by simp
  show ?thesis
    using lifted_product normalized by simp
qed

end
