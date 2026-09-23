theory Inverse_Schrodinger_Lp_Annular_Kernel_Reduction
  imports Inverse_Schrodinger_Lp_Far_Product_Bound
begin

section \<open>Pointwise reductions for the annular singular kernels\<close>

definition slp_radial_inverse :: "slp_point \<Rightarrow> real" where
  "slp_radial_inverse x = inverse (norm x)"

definition slp_radial_inverse_square :: "slp_point \<Rightarrow> real" where
  "slp_radial_inverse_square x = slp_radial_inverse x ^ 2"

lemma slp_radial_inverse_nonnegative [simp]:
  "0 \<le> slp_radial_inverse x"
  unfolding slp_radial_inverse_def by simp

lemma slp_radial_inverse_square_nonnegative [simp]:
  "0 \<le> slp_radial_inverse_square x"
  unfolding slp_radial_inverse_square_def by simp

lemma slp_radial_inverse_bound:
  assumes delta_positive: "0 < delta"
    and distance: "delta \<le> norm x"
  shows "slp_radial_inverse x \<le> 1 / delta"
proof -
  have reciprocal: "inverse (norm x) \<le> inverse delta"
    by (rule le_imp_inverse_le[OF distance delta_positive])
  show ?thesis
    unfolding slp_radial_inverse_def
    using reciprocal by (simp only: divide_inverse)
qed

lemma slp_radial_inverse_square_bound:
  assumes delta_positive: "0 < delta"
    and distance: "delta \<le> norm x"
  shows "slp_radial_inverse_square x \<le> 1 / delta ^ 2"
proof -
  have reciprocal: "slp_radial_inverse x \<le> 1 / delta"
    by (rule slp_radial_inverse_bound[OF delta_positive distance])
  have square:
    "slp_radial_inverse x ^ 2 \<le> (1 / delta) ^ 2"
    by (rule power_mono[OF reciprocal]) simp
  have normalize: "(1 / delta) ^ 2 = 1 / delta ^ 2"
    by (simp add: power2_eq_square)
  show ?thesis
    unfolding slp_radial_inverse_square_def
    using square normalize by linarith
qed

lemma slp_annular_I1_kernel_reduction:
  assumes delta_positive: "0 < delta"
    and annular_lower: "delta \<le> norm y"
  shows "slp_radial_inverse (z - y) * slp_radial_inverse y \<le>
    (1 / delta) * slp_radial_inverse (z - y)"
proof -
  have radial: "slp_radial_inverse y \<le> 1 / delta"
    by (rule slp_radial_inverse_bound[OF delta_positive annular_lower])
  have multiplied:
    "slp_radial_inverse y * slp_radial_inverse (z - y) \<le>
      (1 / delta) * slp_radial_inverse (z - y)"
    by (rule mult_right_mono[OF radial]) simp
  show ?thesis
    using multiplied by (simp only: mult.commute)
qed

lemma slp_annular_I2_kernel_reduction:
  assumes delta_positive: "0 < delta"
    and output_distance: "delta \<le> norm (z - y)"
  shows "slp_radial_inverse (z - y) * slp_radial_inverse y \<le>
    (1 / delta) * slp_radial_inverse y"
proof -
  have radial: "slp_radial_inverse (z - y) \<le> 1 / delta"
    by (rule slp_radial_inverse_bound[OF delta_positive output_distance])
  show ?thesis
    by (rule mult_right_mono[OF radial]) simp
qed

lemma slp_annular_J1_kernel_reduction:
  assumes delta_positive: "0 < delta"
    and annular_lower: "delta \<le> norm y"
  shows "slp_radial_inverse (z - y) * slp_radial_inverse_square y \<le>
    (1 / delta ^ 2) * slp_radial_inverse (z - y)"
proof -
  have radial: "slp_radial_inverse_square y \<le> 1 / delta ^ 2"
    by (rule slp_radial_inverse_square_bound[OF
          delta_positive annular_lower])
  have multiplied:
    "slp_radial_inverse_square y * slp_radial_inverse (z - y) \<le>
      (1 / delta ^ 2) * slp_radial_inverse (z - y)"
    by (rule mult_right_mono[OF radial]) simp
  show ?thesis
    using multiplied by (simp only: mult.commute)
qed

lemma slp_annular_J2_kernel_reduction:
  assumes delta_positive: "0 < delta"
    and output_distance: "delta \<le> norm (z - y)"
  shows "slp_radial_inverse (z - y) * slp_radial_inverse_square y \<le>
    (1 / delta) * slp_radial_inverse_square y"
proof -
  have radial: "slp_radial_inverse (z - y) \<le> 1 / delta"
    by (rule slp_radial_inverse_bound[OF delta_positive output_distance])
  show ?thesis
    by (rule mult_right_mono[OF radial]) simp
qed

end
