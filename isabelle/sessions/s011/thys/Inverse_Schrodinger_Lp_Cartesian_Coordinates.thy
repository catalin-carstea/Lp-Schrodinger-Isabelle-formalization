theory Inverse_Schrodinger_Lp_Cartesian_Coordinates
  imports Inverse_Schrodinger_Lp_Signed_Coordinates
begin

section \<open>Real Cartesian coordinates for finite complex families\<close>

text \<open>
  A Boolean coordinate records the real or imaginary component.  The packing
  below is a fixed real-linear bijection from a finite complex family to a
  Cartesian real vector.  Conjugating the checked signed-output split by this
  packing supplies the real-linear bijection required by the later
  change-of-variables packet, without yet choosing a product-measure bridge or
  calculating a determinant.
\<close>

definition slp_complex_family_pack ::
  "('a::finite \<Rightarrow> complex) \<Rightarrow> real^('a \<times> bool)"
where
  "slp_complex_family_pack z =
    (\<chi> ib. if snd ib then Im (z (fst ib)) else Re (z (fst ib)))"

definition slp_complex_family_unpack ::
  "real^('a::finite \<times> bool) \<Rightarrow> ('a \<Rightarrow> complex)"
where
  "slp_complex_family_unpack x =
    (\<lambda>i. Complex (x $ (i, False)) (x $ (i, True)))"

lemma slp_complex_family_unpack_pack:
  "slp_complex_family_unpack (slp_complex_family_pack z) = z"
  by (rule ext)
    (simp add: slp_complex_family_unpack_def slp_complex_family_pack_def)

lemma slp_complex_family_pack_unpack:
  "slp_complex_family_pack (slp_complex_family_unpack x) = x"
  unfolding vec_eq_iff
proof
  fix ib :: "'a \<times> bool"
  obtain i b where ib: "ib = (i, b)"
    by (cases ib)
  show "slp_complex_family_pack (slp_complex_family_unpack x) $ ib = x $ ib"
    by (cases b)
      (simp_all add: ib slp_complex_family_pack_def
        slp_complex_family_unpack_def)
qed

lemma slp_complex_family_pack_linear:
  "linear (slp_complex_family_pack ::
    ('a::finite \<Rightarrow> complex) \<Rightarrow> real^('a \<times> bool))"
proof (rule linearI)
  show "slp_complex_family_pack (x + y) =
      slp_complex_family_pack x + slp_complex_family_pack y"
    for x y :: "'a \<Rightarrow> complex"
    unfolding vec_eq_iff
  proof
    fix ib :: "'a \<times> bool"
    obtain i b where ib: "ib = (i, b)"
      by (cases ib)
    show "slp_complex_family_pack (x + y) $ ib =
        (slp_complex_family_pack x + slp_complex_family_pack y) $ ib"
      by (cases b)
        (simp_all add: ib slp_complex_family_pack_def)
  qed
  show "slp_complex_family_pack (r *\<^sub>R x) =
      r *\<^sub>R slp_complex_family_pack x"
    for r and x :: "'a \<Rightarrow> complex"
    unfolding vec_eq_iff
  proof
    fix ib :: "'a \<times> bool"
    obtain i b where ib: "ib = (i, b)"
      by (cases ib)
    show "slp_complex_family_pack (r *\<^sub>R x) $ ib =
        (r *\<^sub>R slp_complex_family_pack x) $ ib"
      by (cases b)
        (simp_all add: ib slp_complex_family_pack_def)
  qed
qed

lemma slp_complex_family_unpack_linear:
  "linear (slp_complex_family_unpack ::
    real^('a::finite \<times> bool) \<Rightarrow> ('a \<Rightarrow> complex))"
proof (rule linearI)
  show "slp_complex_family_unpack (x + y) =
      slp_complex_family_unpack x + slp_complex_family_unpack y"
    for x y :: "real^('a \<times> bool)"
    by (rule ext)
      (simp add: slp_complex_family_unpack_def complex_eq_iff)
  show "slp_complex_family_unpack (r *\<^sub>R x) =
      r *\<^sub>R slp_complex_family_unpack x"
    for r and x :: "real^('a \<times> bool)"
    by (rule ext)
      (simp add: slp_complex_family_unpack_def complex_eq_iff)
qed

lemma slp_complex_family_pack_bij:
  "bij (slp_complex_family_pack ::
    ('a::finite \<Rightarrow> complex) \<Rightarrow> real^('a \<times> bool))"
proof (rule bijI)
  show "inj (slp_complex_family_pack ::
      ('a \<Rightarrow> complex) \<Rightarrow> real^('a \<times> bool))"
  proof (rule injI)
    fix x y :: "'a \<Rightarrow> complex"
    assume packed_equal:
      "slp_complex_family_pack x = slp_complex_family_pack y"
    have "slp_complex_family_unpack (slp_complex_family_pack x) =
        slp_complex_family_unpack (slp_complex_family_pack y)"
      using packed_equal by (rule arg_cong)
    then show "x = y"
      by (simp only: slp_complex_family_unpack_pack)
  qed
  show "surj (slp_complex_family_pack ::
      ('a \<Rightarrow> complex) \<Rightarrow> real^('a \<times> bool))"
  proof (rule surjI
      [where f = "slp_complex_family_unpack"])
    fix x :: "real^('a \<times> bool)"
    show "slp_complex_family_pack (slp_complex_family_unpack x) = x"
      by (rule slp_complex_family_pack_unpack)
  qed
qed

lemma slp_complex_family_unpack_bij:
  "bij (slp_complex_family_unpack ::
    real^('a::finite \<times> bool) \<Rightarrow> ('a \<Rightarrow> complex))"
proof (rule bijI)
  show "inj (slp_complex_family_unpack ::
      real^('a \<times> bool) \<Rightarrow> ('a \<Rightarrow> complex))"
  proof (rule injI)
    fix x y :: "real^('a \<times> bool)"
    assume unpacked_equal:
      "slp_complex_family_unpack x = slp_complex_family_unpack y"
    have "slp_complex_family_pack (slp_complex_family_unpack x) =
        slp_complex_family_pack (slp_complex_family_unpack y)"
      using unpacked_equal by (rule arg_cong)
    then show "x = y"
      by (simp only: slp_complex_family_pack_unpack)
  qed
  show "surj (slp_complex_family_unpack ::
      real^('a \<times> bool) \<Rightarrow> ('a \<Rightarrow> complex))"
  proof (rule surjI
      [where f = "slp_complex_family_pack"])
    fix z :: "'a \<Rightarrow> complex"
    show "slp_complex_family_unpack (slp_complex_family_pack z) = z"
      by (rule slp_complex_family_unpack_pack)
  qed
qed

definition slp_signed_pair_to_family ::
  "(complex \<times> ('i \<Rightarrow> complex)) \<Rightarrow>
    (unit + 'i) \<Rightarrow> complex"
where
  "slp_signed_pair_to_family cu =
    case_sum (\<lambda>_. fst cu) (snd cu)"

definition slp_signed_family_to_pair ::
  "((unit + 'i) \<Rightarrow> complex) \<Rightarrow>
    complex \<times> ('i \<Rightarrow> complex)"
where
  "slp_signed_family_to_pair y =
    (y (Inl ()), \<lambda>i. y (Inr i))"

lemma slp_signed_family_to_pair_pair_to_family:
  "slp_signed_family_to_pair (slp_signed_pair_to_family cu) = cu"
  by (cases cu)
    (simp add: slp_signed_family_to_pair_def slp_signed_pair_to_family_def)

lemma slp_signed_pair_to_family_family_to_pair:
  "slp_signed_pair_to_family (slp_signed_family_to_pair y) = y"
  by (rule ext)
    (simp add: slp_signed_family_to_pair_def slp_signed_pair_to_family_def
      split: sum.splits)

lemma slp_signed_pair_to_family_linear:
  "linear (slp_signed_pair_to_family ::
    (complex \<times> ('i \<Rightarrow> complex)) \<Rightarrow>
      (unit + 'i) \<Rightarrow> complex)"
proof (rule linearI)
  show "slp_signed_pair_to_family (x + y) =
      slp_signed_pair_to_family x + slp_signed_pair_to_family y"
    for x y :: "complex \<times> ('i \<Rightarrow> complex)"
    by (rule ext)
      (simp add: slp_signed_pair_to_family_def split: sum.splits)
  show "slp_signed_pair_to_family (r *\<^sub>R x) =
      r *\<^sub>R slp_signed_pair_to_family x"
    for r and x :: "complex \<times> ('i \<Rightarrow> complex)"
    by (rule ext)
      (simp add: slp_signed_pair_to_family_def split: sum.splits)
qed

lemma slp_signed_pair_to_family_bij:
  "bij (slp_signed_pair_to_family ::
    (complex \<times> ('i \<Rightarrow> complex)) \<Rightarrow>
      (unit + 'i) \<Rightarrow> complex)"
proof (rule bijI)
  show "inj (slp_signed_pair_to_family ::
      (complex \<times> ('i \<Rightarrow> complex)) \<Rightarrow>
        (unit + 'i) \<Rightarrow> complex)"
  proof (rule injI)
    fix x y :: "complex \<times> ('i \<Rightarrow> complex)"
    assume family_equal:
      "slp_signed_pair_to_family x = slp_signed_pair_to_family y"
    have "slp_signed_family_to_pair (slp_signed_pair_to_family x) =
        slp_signed_family_to_pair (slp_signed_pair_to_family y)"
      using family_equal by (rule arg_cong)
    then show "x = y"
      by (simp only: slp_signed_family_to_pair_pair_to_family)
  qed
  show "surj (slp_signed_pair_to_family ::
      (complex \<times> ('i \<Rightarrow> complex)) \<Rightarrow>
        (unit + 'i) \<Rightarrow> complex)"
  proof (rule surjI
      [where f = "slp_signed_family_to_pair"])
    fix y :: "(unit + 'i) \<Rightarrow> complex"
    show "slp_signed_pair_to_family (slp_signed_family_to_pair y) = y"
      by (rule slp_signed_pair_to_family_family_to_pair)
  qed
qed

lemma slp_signed_output_linear:
  fixes epsilon :: "'a::finite \<Rightarrow> real"
  shows "linear (slp_signed_output epsilon)"
proof (rule linearI)
  show "slp_signed_output epsilon (x + y) =
      slp_signed_output epsilon x + slp_signed_output epsilon y"
    for x y :: "'a \<Rightarrow> complex"
    unfolding slp_signed_output_def
    by (simp add: sum.distrib algebra_simps)
  show "slp_signed_output epsilon (r *\<^sub>R x) =
      r *\<^sub>R slp_signed_output epsilon x"
    for r and x :: "'a \<Rightarrow> complex"
    unfolding slp_signed_output_def
    by (simp add: scaleR_conv_of_real sum_distrib_left algebra_simps)
qed

lemma slp_signed_coordinate_split_linear:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  shows "linear (slp_signed_coordinate_split epsilon)"
proof (rule linearI)
  have output_linear: "linear (slp_signed_output epsilon)"
    by (rule slp_signed_output_linear)
  interpret out_lin: linear "slp_signed_output epsilon"
    by (rule output_linear)
  show "slp_signed_coordinate_split epsilon (x + y) =
      slp_signed_coordinate_split epsilon x +
        slp_signed_coordinate_split epsilon y"
    for x y :: "(unit + 'i) \<Rightarrow> complex"
    by (simp add: slp_signed_coordinate_split_def out_lin.add fun_eq_iff)
  show "slp_signed_coordinate_split epsilon (r *\<^sub>R x) =
      r *\<^sub>R slp_signed_coordinate_split epsilon x"
    for r and x :: "(unit + 'i) \<Rightarrow> complex"
    by (simp add: slp_signed_coordinate_split_def out_lin.scale fun_eq_iff)
qed

definition slp_signed_cartesian_split ::
  "((unit + 'i::finite) \<Rightarrow> real) \<Rightarrow>
    real^((unit + 'i) \<times> bool) \<Rightarrow>
      real^((unit + 'i) \<times> bool)"
where
  "slp_signed_cartesian_split epsilon =
    slp_complex_family_pack \<circ>
      (slp_signed_pair_to_family \<circ>
        (slp_signed_coordinate_split epsilon \<circ>
          slp_complex_family_unpack))"

lemma slp_signed_cartesian_split_linear:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  shows "linear (slp_signed_cartesian_split epsilon)"
proof -
  have unpack_linear:
    "linear (slp_complex_family_unpack ::
      real^((unit + 'i) \<times> bool) \<Rightarrow>
        ((unit + 'i) \<Rightarrow> complex))"
    by (rule slp_complex_family_unpack_linear)
  have split_linear: "linear (slp_signed_coordinate_split epsilon)"
    by (rule slp_signed_coordinate_split_linear)
  have pair_linear:
    "linear (slp_signed_pair_to_family ::
      (complex \<times> ('i \<Rightarrow> complex)) \<Rightarrow>
        (unit + 'i) \<Rightarrow> complex)"
    by (rule slp_signed_pair_to_family_linear)
  have pack_linear:
    "linear (slp_complex_family_pack ::
      ((unit + 'i) \<Rightarrow> complex) \<Rightarrow>
        real^((unit + 'i) \<times> bool))"
    by (rule slp_complex_family_pack_linear)
  have inner_linear:
    "linear (slp_signed_coordinate_split epsilon \<circ>
      slp_complex_family_unpack)"
    by (rule linear_compose[OF unpack_linear split_linear])
  have middle_linear:
    "linear (slp_signed_pair_to_family \<circ>
      (slp_signed_coordinate_split epsilon \<circ>
        slp_complex_family_unpack))"
    by (rule linear_compose[OF inner_linear pair_linear])
  show ?thesis
    unfolding slp_signed_cartesian_split_def
    by (rule linear_compose[OF middle_linear pack_linear])
qed

theorem slp_signed_cartesian_split_bij:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes distinguished_nonzero: "epsilon (Inl ()) \<noteq> 0"
  shows "bij (slp_signed_cartesian_split epsilon)"
proof -
  have unpack_bij:
    "bij (slp_complex_family_unpack ::
      real^((unit + 'i) \<times> bool) \<Rightarrow>
        ((unit + 'i) \<Rightarrow> complex))"
    by (rule slp_complex_family_unpack_bij)
  have split_bij: "bij (slp_signed_coordinate_split epsilon)"
    by (rule slp_signed_coordinate_split_bij
        [where epsilon = epsilon])
      (rule distinguished_nonzero)
  have pair_bij:
    "bij (slp_signed_pair_to_family ::
      (complex \<times> ('i \<Rightarrow> complex)) \<Rightarrow>
        (unit + 'i) \<Rightarrow> complex)"
    by (rule slp_signed_pair_to_family_bij)
  have pack_bij:
    "bij (slp_complex_family_pack ::
      ((unit + 'i) \<Rightarrow> complex) \<Rightarrow>
        real^((unit + 'i) \<times> bool))"
    by (rule slp_complex_family_pack_bij)
  have inner_bij:
    "bij (slp_signed_coordinate_split epsilon \<circ>
      slp_complex_family_unpack)"
    by (rule bij_comp[OF unpack_bij split_bij])
  have middle_bij:
    "bij (slp_signed_pair_to_family \<circ>
      (slp_signed_coordinate_split epsilon \<circ>
        slp_complex_family_unpack))"
    by (rule bij_comp[OF inner_bij pair_bij])
  show ?thesis
    unfolding slp_signed_cartesian_split_def
    by (rule bij_comp[OF middle_bij pack_bij])
qed

corollary slp_signed_cartesian_split_linear_injective_of_signs:
  fixes epsilon :: "(unit + 'i::finite) \<Rightarrow> real"
  assumes signs: "\<And>k. epsilon k = -1 \<or> epsilon k = 1"
  shows "linear (slp_signed_cartesian_split epsilon) \<and>
    inj (slp_signed_cartesian_split epsilon)"
proof
  show "linear (slp_signed_cartesian_split epsilon)"
    by (rule slp_signed_cartesian_split_linear)
  show "inj (slp_signed_cartesian_split epsilon)"
  proof -
    have split_bij: "bij (slp_signed_cartesian_split epsilon)"
      by (rule slp_signed_cartesian_split_bij
          [where epsilon = epsilon])
        (use signs[of "Inl ()"] in auto)
    show ?thesis
      by (rule bij_is_inj[OF split_bij])
  qed
qed

end
