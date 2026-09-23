theory Inverse_Schrodinger_Lp_Outer_Conjugated_Source_Weak_Wirtinger
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Neumann_Affine_Source_Bridge"
begin

section \<open>Exact outer conjugated-source fields\<close>

definition slp_left_outer_conjugated_field ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_left_outer_conjugated_field tau c cutoff coefficient W =
    slp_partial_psi_inverse tau c
      (\<lambda>x. cutoff x *
        slp_left_conjugated_cauchy_source tau c coefficient
          (\<lambda>y. coefficient y * W y) x)"

definition slp_left_outer_conjugated_gradient ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_gradient_field"
where
  "slp_left_outer_conjugated_gradient tau c cutoff coefficient W =
    slp_partial_inverse_gradient
      (slp_oscillatory_modulation tau c
        (\<lambda>x. cutoff x *
          slp_left_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x))"

definition slp_right_outer_conjugated_field ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_right_outer_conjugated_field tau c cutoff coefficient W =
    slp_dbar_psi_inverse (- tau) c
      (\<lambda>x. cutoff x *
        slp_right_conjugated_cauchy_source tau c coefficient
          (\<lambda>y. coefficient y * W y) x)"

definition slp_right_outer_conjugated_gradient ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_gradient_field"
where
  "slp_right_outer_conjugated_gradient tau c cutoff coefficient W =
    slp_dbar_inverse_gradient
      (slp_oscillatory_modulation tau c
        (\<lambda>x. cutoff x *
          slp_right_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x))"

context aim_planar_cauchy_beurling_derivatives
begin

theorem slp_both_outer_conjugated_sources_weak_wirtinger:
  fixes cutoff coefficient W :: slp_scalar_field
  assumes exponent_lower: "1 < (p::real)"
    and left_source_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. cutoff x *
          slp_left_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x)"
    and left_source_support:
      "bounded {x. cutoff x *
          slp_left_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x \<noteq> 0}"
    and right_source_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. cutoff x *
          slp_right_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x)"
    and right_source_support:
      "bounded {x. cutoff x *
          slp_right_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x \<noteq> 0}"
  shows
    "slp_weak_gradient_on UNIV
        (slp_left_outer_conjugated_field tau c cutoff coefficient W)
        (slp_left_outer_conjugated_gradient tau c cutoff coefficient W)
      \<and>
      slp_gradient_wirtinger_partial
        (slp_left_outer_conjugated_gradient tau c cutoff coefficient W) =
        slp_oscillatory_modulation tau c
          (\<lambda>x. cutoff x *
            slp_left_conjugated_cauchy_source tau c coefficient
              (\<lambda>y. coefficient y * W y) x)
      \<and>
      slp_weak_gradient_on UNIV
        (slp_right_outer_conjugated_field tau c cutoff coefficient W)
        (slp_right_outer_conjugated_gradient tau c cutoff coefficient W)
      \<and>
      slp_gradient_wirtinger_dbar
        (slp_right_outer_conjugated_gradient tau c cutoff coefficient W) =
        slp_oscillatory_modulation tau c
          (\<lambda>x. cutoff x *
            slp_right_conjugated_cauchy_source tau c coefficient
              (\<lambda>y. coefficient y * W y) x)"
proof -
  let ?left_source =
    "\<lambda>x. cutoff x *
      slp_left_conjugated_cauchy_source tau c coefficient
        (\<lambda>y. coefficient y * W y) x"
  let ?right_source =
    "\<lambda>x. cutoff x *
      slp_right_conjugated_cauchy_source tau c coefficient
        (\<lambda>y. coefficient y * W y) x"
  let ?left_modulated = "slp_oscillatory_modulation tau c ?left_source"
  let ?right_modulated = "slp_oscillatory_modulation tau c ?right_source"

  have left_modulated_lp: "aim_complex_lp_on_plane p ?left_modulated"
    using left_source_lp by simp
  have left_modulated_support: "bounded {x. ?left_modulated x \<noteq> 0}"
    using left_source_support by simp
  note left_data = slp_both_cauchy_weak_wirtinger_right_inverse[OF
    exponent_lower left_modulated_lp left_modulated_support]
  have left_weak:
      "slp_weak_gradient_on UNIV
        (slp_partial_inverse ?left_modulated)
        (slp_partial_inverse_gradient ?left_modulated)"
    using left_data by blast
  have left_identity:
      "slp_gradient_wirtinger_partial
        (slp_partial_inverse_gradient ?left_modulated) = ?left_modulated"
    using left_data by blast

  have right_modulated_lp: "aim_complex_lp_on_plane p ?right_modulated"
    using right_source_lp by simp
  have right_modulated_support: "bounded {x. ?right_modulated x \<noteq> 0}"
    using right_source_support by simp
  note right_data = slp_both_cauchy_weak_wirtinger_right_inverse[OF
    exponent_lower right_modulated_lp right_modulated_support]
  have right_weak:
      "slp_weak_gradient_on UNIV
        (slp_dbar_inverse ?right_modulated)
        (slp_dbar_inverse_gradient ?right_modulated)"
    using right_data by blast
  have right_identity:
      "slp_gradient_wirtinger_dbar
        (slp_dbar_inverse_gradient ?right_modulated) = ?right_modulated"
    using right_data by blast

  have left_field_weak:
      "slp_weak_gradient_on UNIV
        (slp_left_outer_conjugated_field tau c cutoff coefficient W)
        (slp_left_outer_conjugated_gradient tau c cutoff coefficient W)"
    using left_weak
    unfolding slp_left_outer_conjugated_field_def
      slp_left_outer_conjugated_gradient_def slp_partial_psi_inverse_def .
  have left_field_identity:
      "slp_gradient_wirtinger_partial
          (slp_left_outer_conjugated_gradient tau c cutoff coefficient W) =
        ?left_modulated"
    using left_identity
    unfolding slp_left_outer_conjugated_gradient_def .
  have right_field_weak:
      "slp_weak_gradient_on UNIV
        (slp_right_outer_conjugated_field tau c cutoff coefficient W)
        (slp_right_outer_conjugated_gradient tau c cutoff coefficient W)"
    using right_weak
    unfolding slp_right_outer_conjugated_field_def
      slp_right_outer_conjugated_gradient_def slp_dbar_psi_inverse_def
    by simp
  have right_field_identity:
      "slp_gradient_wirtinger_dbar
          (slp_right_outer_conjugated_gradient tau c cutoff coefficient W) =
        ?right_modulated"
    using right_identity
    unfolding slp_right_outer_conjugated_gradient_def .

  show ?thesis
    using left_field_weak left_field_identity right_field_weak
      right_field_identity by blast
qed

end

end
