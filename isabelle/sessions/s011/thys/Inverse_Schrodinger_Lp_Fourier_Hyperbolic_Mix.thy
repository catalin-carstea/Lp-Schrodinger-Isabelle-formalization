theory Inverse_Schrodinger_Lp_Fourier_Hyperbolic_Mix
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Damped_Chirp_Integral_Product"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Affine_Transport"
begin

section \<open>Real hyperbolic coordinates for the paired damped chirp\<close>

definition slp_hyperbolic_mix :: "slp_point \<Rightarrow> slp_point"
where
  "slp_hyperbolic_mix u =
    (\<chi> i. if i = 0
      then (u $ 0 + u $ 1) / 2
      else (u $ 0 - u $ 1) / 2)"

lemma slp_hyperbolic_mix_linear:
  "linear slp_hyperbolic_mix"
proof (rule linearI)
  show "slp_hyperbolic_mix (x + y) =
      slp_hyperbolic_mix x + slp_hyperbolic_mix y" for x y
  proof (unfold vec_eq_iff, intro allI)
    fix i :: 2
    have two_is_zero: "(2 :: 2) = 0"
      by simp
    have raw_cases: "i = 1 \<or> i = (2 :: 2)"
      by (rule exhaust_2)
    have cases: "i = 0 \<or> i = 1"
      using raw_cases two_is_zero by blast
    have plus:
        "(x $ 0 + y $ 0 + (x $ 1 + y $ 1)) / 2 =
          (x $ 0 + x $ 1) / 2 + (y $ 0 + y $ 1) / 2"
      by (simp add: divide_simps algebra_simps)
    have minus:
        "(x $ 0 + y $ 0 - (x $ 1 + y $ 1)) / 2 =
          (x $ 0 - x $ 1) / 2 + (y $ 0 - y $ 1) / 2"
      by (simp add: divide_simps algebra_simps)
    show "slp_hyperbolic_mix (x + y) $ i =
        (slp_hyperbolic_mix x + slp_hyperbolic_mix y) $ i"
      using cases plus minus
      by (auto simp: slp_hyperbolic_mix_def)
  qed
  show "slp_hyperbolic_mix (r *\<^sub>R x) =
      r *\<^sub>R slp_hyperbolic_mix x" for r x
  proof (unfold vec_eq_iff, intro allI)
    fix i :: 2
    have two_is_zero: "(2 :: 2) = 0"
      by simp
    have raw_cases: "i = 1 \<or> i = (2 :: 2)"
      by (rule exhaust_2)
    have cases: "i = 0 \<or> i = 1"
      using raw_cases two_is_zero by blast
    have plus:
        "(r * (x $ 0) + r * (x $ 1)) / 2 =
          r * ((x $ 0 + x $ 1) / 2)"
      by (simp add: divide_simps algebra_simps)
    have minus:
        "(r * (x $ 0) - r * (x $ 1)) / 2 =
          r * ((x $ 0 - x $ 1) / 2)"
      by (simp add: divide_simps algebra_simps)
    show "slp_hyperbolic_mix (r *\<^sub>R x) $ i =
        (r *\<^sub>R slp_hyperbolic_mix x) $ i"
      using cases plus minus
      by (auto simp: slp_hyperbolic_mix_def)
  qed
qed

lemma slp_hyperbolic_mix_injective:
  "inj slp_hyperbolic_mix"
proof (rule injI)
  fix u v :: slp_point
  assume equal: "slp_hyperbolic_mix u = slp_hyperbolic_mix v"
  have zero:
      "(u $ 0 + u $ 1) / 2 = (v $ 0 + v $ 1) / 2"
    using arg_cong[OF equal, where f="\<lambda>x. x $ (0 :: 2)"]
    by (simp add: slp_hyperbolic_mix_def)
  have one:
      "(u $ 0 - u $ 1) / 2 = (v $ 0 - v $ 1) / 2"
    using arg_cong[OF equal, where f="\<lambda>x. x $ (1 :: 2)"]
    by (simp add: slp_hyperbolic_mix_def)
  show "u = v"
    unfolding vec_eq_iff
  proof
    fix i :: 2
    have two_is_zero: "(2 :: 2) = 0"
      by simp
    have raw_cases: "i = 1 \<or> i = (2 :: 2)"
      by (rule exhaust_2)
    have cases: "i = 0 \<or> i = 1"
      using raw_cases two_is_zero by blast
    then show "u $ i = v $ i"
      using zero one by auto
  qed
qed

lemma slp_hyperbolic_mix_abs_det:
  "\<bar>det (matrix slp_hyperbolic_mix)\<bar> = (1 / 2 :: real)"
  unfolding slp_hyperbolic_mix_def matrix_def det_2 axis_def
  by simp

lemma slp_hyperbolic_mix_norm_square:
  "(Real_Vector_Spaces.norm (slp_hyperbolic_mix u)) ^ 2 =
    ((u $ 0) ^ 2 + (u $ 1) ^ 2) / 2"
proof -
  have coordinates:
      "(Real_Vector_Spaces.norm (slp_hyperbolic_mix u)) ^ 2 =
        ((u $ 0 + u $ 1) / 2) ^ 2 +
        ((u $ 0 - u $ 1) / 2) ^ 2"
    unfolding slp_planar_norm_square slp_hyperbolic_mix_def
    by simp
  have scalar:
      "((a + b) / 2) ^ 2 + ((a - b) / 2) ^ 2 =
        (a ^ 2 + b ^ 2) / 2" for a b :: real
    by (simp add: divide_simps power2_eq_square algebra_simps)
  show ?thesis
    unfolding coordinates
    by (rule scalar)
qed

lemma slp_hyperbolic_mix_center_phase:
  "slp_center_phase 0 (slp_hyperbolic_mix u) =
    (u $ 0) * (u $ 1)"
proof -
  have scalar:
      "((a + b) / 2) ^ 2 - ((a - b) / 2) ^ 2 = a * b"
      for a b :: real
    by (simp add: divide_simps power2_eq_square algebra_simps)
  show ?thesis
    using scalar[of "u $ 0" "u $ 1"]
    by (simp add: slp_center_phase_def slp_hyperbolic_mix_def
        zero_vec_def)
qed

lemma slp_hyperbolic_mix_inner:
  "inner (slp_hyperbolic_mix u) xi =
    ((xi $ 0 + xi $ 1) / 2) * (u $ 0) +
    ((xi $ 0 - xi $ 1) / 2) * (u $ 1)"
proof -
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have scalar:
      "((a + b) / 2) * c + ((a - b) / 2) * d =
        ((c + d) / 2) * a + ((c - d) / 2) * b"
      for a b c d :: real
    by (simp add: divide_simps algebra_simps)
  show ?thesis
    using scalar[of "u $ 0" "u $ 1" "xi $ 0" "xi $ 1"]
    by (simp add: inner_vec_def universe_two slp_hyperbolic_mix_def)
qed

lemma slp_hyperbolic_mix_integrable:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
  shows "integrable lborel (\<lambda>u. f (slp_hyperbolic_mix u))"
  by (rule slp_lborel_linear_pullback(1)[OF
        slp_hyperbolic_mix_linear slp_hyperbolic_mix_injective
        f_integrable])

lemma slp_hyperbolic_mix_integral:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
  shows "integral\<^sup>L lborel f =
    (1 / 2) *\<^sub>R
      integral\<^sup>L lborel (\<lambda>u. f (slp_hyperbolic_mix u))"
  using slp_lborel_linear_pullback(2)[OF
      slp_hyperbolic_mix_linear slp_hyperbolic_mix_injective f_integrable]
    slp_hyperbolic_mix_abs_det
  by simp

end
