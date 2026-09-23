theory Inverse_Schrodinger_Lp_Quadratic_Phase
  imports Inverse_Schrodinger_Lp_AE_Interface
begin

section \<open>Signed quadratic normal form\<close>

text \<open>
  This is the enumeration-invariant finite-type presentation of official
  Lemma @{text "lem-signed-quadratic-normal-form"}.  A type with finitely many
  elements represents the indices @{text "0,\<dots>,N"}; the hypotheses below
  retain both the sign condition and the exact signed-sum normalization.
\<close>

definition slp_quadratic_phase :: "complex \<Rightarrow> complex \<Rightarrow> real"
where
  "slp_quadratic_phase z0 z = Re ((z - z0) ^ 2)"

definition slp_signed_output ::
  "('i::finite \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_signed_output epsilon y =
    (\<Sum>i\<in>UNIV. of_real (epsilon i) * y i)"

lemma slp_signed_output_sub:
  "slp_signed_output epsilon (\<lambda>i. u i - v i) =
    slp_signed_output epsilon u - slp_signed_output epsilon v"
  unfolding slp_signed_output_def
  by (simp add: sum_subtractf algebra_simps)

lemma slp_signed_output_const:
  "slp_signed_output epsilon (\<lambda>_. a) =
    (\<Sum>i\<in>UNIV. of_real (epsilon i)) * a"
  unfolding slp_signed_output_def
  by (simp add: sum_distrib_right)

definition slp_signed_residual ::
  "('i::finite \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> complex) \<Rightarrow> real"
where
  "slp_signed_residual epsilon y =
    Re ((\<Sum>i\<in>UNIV. of_real (epsilon i) * (y i) ^ 2) -
      (slp_signed_output epsilon y) ^ 2)"

definition slp_signed_bilinear ::
  "('i::finite \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> complex) \<Rightarrow>
    ('i \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_signed_bilinear epsilon u v =
    (\<Sum>i\<in>UNIV. of_real (epsilon i) * u i * v i)"

lemma slp_signed_bilinear_mult_right:
  "slp_signed_bilinear epsilon u (\<lambda>i. a * v i) =
    a * slp_signed_bilinear epsilon u v"
  unfolding slp_signed_bilinear_def
  by (simp add: sum_distrib_left mult_ac)

lemma slp_signed_bilinear_sub_right:
  "slp_signed_bilinear epsilon u (\<lambda>i. v i - w i) =
    slp_signed_bilinear epsilon u v -
    slp_signed_bilinear epsilon u w"
  unfolding slp_signed_bilinear_def
  by (simp add: sum_subtractf algebra_simps)

lemma slp_signed_bilinear_const_right:
  "slp_signed_bilinear epsilon u (\<lambda>_. a) =
    a * slp_signed_output epsilon u"
  unfolding slp_signed_bilinear_def slp_signed_output_def
  by (simp add: sum_distrib_left mult_ac)

definition slp_signed_residual_bilinear ::
  "('i::finite \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> complex) \<Rightarrow>
    ('i \<Rightarrow> complex) \<Rightarrow> real"
where
  "slp_signed_residual_bilinear epsilon u v =
    Re (slp_signed_bilinear epsilon u v -
      slp_signed_output epsilon u * slp_signed_output epsilon v)"

definition slp_signed_fiber_nondegenerate ::
  "('i::finite \<Rightarrow> real) \<Rightarrow> bool"
where
  "slp_signed_fiber_nondegenerate epsilon \<longleftrightarrow>
    (\<forall>u. slp_signed_output epsilon u = 0 \<longrightarrow>
      (\<forall>v. slp_signed_output epsilon v = 0 \<longrightarrow>
        slp_signed_residual_bilinear epsilon u v = 0) \<longrightarrow>
      u = 0)"

lemma slp_signed_residual_diagonal:
  "slp_signed_residual epsilon y =
    slp_signed_residual_bilinear epsilon y y"
  unfolding slp_signed_residual_def slp_signed_residual_bilinear_def
    slp_signed_bilinear_def
  by (simp add: power2_eq_square algebra_simps)

lemma slp_signed_residual_bilinear_on_tangent:
  assumes "slp_signed_output epsilon u = 0"
    and "slp_signed_output epsilon v = 0"
  shows "slp_signed_residual_bilinear epsilon u v =
    Re (slp_signed_bilinear epsilon u v)"
  using assms
  by (simp add: slp_signed_residual_bilinear_def)

lemma slp_signed_quadratic_identity:
  fixes epsilon :: "'i::finite \<Rightarrow> real"
    and y :: "'i \<Rightarrow> complex"
  assumes signed_sum: "(\<Sum>i\<in>UNIV. epsilon i) = 1"
  defines "c \<equiv> slp_signed_output epsilon y"
  shows "(\<Sum>i\<in>UNIV. epsilon i * slp_quadratic_phase z0 (y i)) =
    slp_quadratic_phase z0 c + slp_signed_residual epsilon y"
proof -
  have complex_signed_sum:
      "(\<Sum>i\<in>UNIV. of_real (epsilon i) :: complex) = 1"
    using signed_sum by (metis of_real_1 of_real_sum)
  have expanded:
      "(\<Sum>i\<in>UNIV. of_real (epsilon i) * (y i - z0) ^ 2) =
        (\<Sum>i\<in>UNIV. of_real (epsilon i) * (y i) ^ 2) -
        2 * z0 * (\<Sum>i\<in>UNIV. of_real (epsilon i) * y i) +
        z0 ^ 2 * (\<Sum>i\<in>UNIV. of_real (epsilon i))"
  proof -
    have pointwise:
        "\<And>i. of_real (epsilon i) * (y i - z0) ^ 2 =
          of_real (epsilon i) * (y i) ^ 2 -
          2 * z0 * (of_real (epsilon i) * y i) +
          z0 ^ 2 * of_real (epsilon i)"
    proof -
      fix i
      show "of_real (epsilon i) * (y i - z0) ^ 2 =
          of_real (epsilon i) * (y i) ^ 2 -
          2 * z0 * (of_real (epsilon i) * y i) +
          z0 ^ 2 * of_real (epsilon i)"
        by (simp add: power2_eq_square algebra_simps)
    qed
    show ?thesis
      by (simp only: pointwise sum.distrib sum_subtractf
            sum_distrib_left sum_distrib_right)
  qed
  have complex_identity:
      "(\<Sum>i\<in>UNIV. of_real (epsilon i) * (y i - z0) ^ 2) =
        (c - z0) ^ 2 +
        ((\<Sum>i\<in>UNIV. of_real (epsilon i) * (y i) ^ 2) - c ^ 2)"
    using expanded complex_signed_sum
    unfolding c_def slp_signed_output_def
    by (simp add: power2_eq_square algebra_simps)
  have phase_sum:
      "(\<Sum>i\<in>UNIV. epsilon i * slp_quadratic_phase z0 (y i)) =
        Re (\<Sum>i\<in>UNIV. of_real (epsilon i) * (y i - z0) ^ 2)"
    by (simp add: slp_quadratic_phase_def)
  show ?thesis
    using complex_identity phase_sum
    by (simp add: c_def slp_quadratic_phase_def slp_signed_residual_def)
qed

lemma slp_signed_fiber_nondegenerate:
  fixes epsilon :: "'i::finite \<Rightarrow> real"
  assumes signs: "\<And>i. epsilon i = -1 \<or> epsilon i = 1"
    and signed_sum: "(\<Sum>i\<in>UNIV. epsilon i) = 1"
  shows "slp_signed_fiber_nondegenerate epsilon"
proof (unfold slp_signed_fiber_nondegenerate_def, intro allI impI)
  fix u :: "'i \<Rightarrow> complex"
  assume u_tangent: "slp_signed_output epsilon u = 0"
    and residual_kernel:
      "\<forall>v. slp_signed_output epsilon v = 0 \<longrightarrow>
        slp_signed_residual_bilinear epsilon u v = 0"
  have complex_signed_sum:
      "(\<Sum>i\<in>UNIV. of_real (epsilon i) :: complex) = 1"
    using signed_sum by (metis of_real_1 of_real_sum)
  have complex_kernel:
      "slp_signed_bilinear epsilon u v = 0"
    if v_tangent: "slp_signed_output epsilon v = 0" for v
  proof -
    have iv_tangent:
        "slp_signed_output epsilon (\<lambda>i. \<i> * v i) = 0"
    proof -
      have "slp_signed_output epsilon (\<lambda>i. \<i> * v i) =
          \<i> * slp_signed_output epsilon v"
        unfolding slp_signed_output_def
        by (simp add: sum_distrib_left mult_ac)
      then show ?thesis using v_tangent by simp
    qed
    have real_zero:
        "Re (slp_signed_bilinear epsilon u v) = 0"
      using residual_kernel v_tangent u_tangent
      by (simp add: slp_signed_residual_bilinear_on_tangent)
    have imaginary_zero:
        "Im (slp_signed_bilinear epsilon u v) = 0"
    proof -
      have "Re (slp_signed_bilinear epsilon u (\<lambda>i. \<i> * v i)) = 0"
        using residual_kernel iv_tangent u_tangent
        by (simp add: slp_signed_residual_bilinear_on_tangent)
      then show ?thesis
        by (simp only: slp_signed_bilinear_mult_right; simp)
    qed
    show ?thesis
      using real_zero imaginary_zero by (simp add: complex_eq_iff)
  qed
  have bilinear_all_zero:
      "slp_signed_bilinear epsilon u w = 0" for w
  proof -
    let ?a = "slp_signed_output epsilon w"
    let ?v = "\<lambda>i. w i - ?a"
    have v_tangent: "slp_signed_output epsilon ?v = 0"
      using complex_signed_sum
      by (simp add: slp_signed_output_sub slp_signed_output_const)
    have uv_zero: "slp_signed_bilinear epsilon u ?v = 0"
      by (rule complex_kernel[OF v_tangent])
    show ?thesis
      using uv_zero u_tangent
      by (simp add: slp_signed_bilinear_sub_right
          slp_signed_bilinear_const_right)
  qed
  show "u = 0"
  proof
    fix i
    have epsilon_nonzero: "epsilon i \<noteq> 0"
      using signs[of i] by auto
    have basis_zero:
        "slp_signed_bilinear epsilon u
          (\<lambda>j. if j = i then 1 else 0) = 0"
      by (rule bilinear_all_zero)
    have basis_eval:
        "slp_signed_bilinear epsilon u
          (\<lambda>j. if j = i then 1 else 0) =
        of_real (epsilon i) * u i"
      unfolding slp_signed_bilinear_def
    proof -
      have "(\<Sum>j\<in>UNIV.
          of_real (epsilon j) * u j * (if j = i then 1 else 0)) =
          (\<Sum>j\<in>UNIV.
            if j = i then of_real (epsilon j) * u j else 0)"
        by (rule sum.cong) auto
      also have "\<dots> = of_real (epsilon i) * u i"
        by simp
      finally show "(\<Sum>j\<in>UNIV.
          of_real (epsilon j) * u j * (if j = i then 1 else 0)) =
          of_real (epsilon i) * u i" .
    qed
    have coordinate_zero: "of_real (epsilon i) * u i = 0"
      using basis_zero basis_eval by simp
    show "u i = 0 i"
      using coordinate_zero epsilon_nonzero by simp
  qed
qed

theorem slp_signed_quadratic_normal_form:
  fixes epsilon :: "'i::finite \<Rightarrow> real"
    and y :: "'i \<Rightarrow> complex"
  assumes signs: "\<And>i. epsilon i = -1 \<or> epsilon i = 1"
    and signed_sum: "(\<Sum>i\<in>UNIV. epsilon i) = 1"
  defines "c \<equiv> slp_signed_output epsilon y"
  shows "(\<Sum>i\<in>UNIV. epsilon i * slp_quadratic_phase z0 (y i)) =
      slp_quadratic_phase z0 c + slp_signed_residual epsilon y"
    and "slp_signed_fiber_nondegenerate epsilon"
proof -
  show "(\<Sum>i\<in>UNIV. epsilon i * slp_quadratic_phase z0 (y i)) =
      slp_quadratic_phase z0 c + slp_signed_residual epsilon y"
    unfolding c_def
    by (rule slp_signed_quadratic_identity[OF signed_sum])
  show "slp_signed_fiber_nondegenerate epsilon"
    by (rule slp_signed_fiber_nondegenerate[OF signs signed_sum])
qed

end
