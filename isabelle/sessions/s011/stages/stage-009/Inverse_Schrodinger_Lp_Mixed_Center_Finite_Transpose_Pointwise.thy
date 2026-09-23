theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Transpose_Pointwise
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Right_Graph_Natural_Recursive_Branch_Identity"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Integrand"
begin

section \<open>Pointwise finite mixed-transpose factorization\<close>

theorem slp_mixed_center_finite_transpose_integrand_factorization:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_center_kernel tau target center *
        slp_mixed_center_finite_oscillatory_integrand tau root_weight
          left_cutoff left_potential right_cutoff right_potential center
          coordinates =
      root_weight (fst coordinates) *
        slp_center_kernel (- tau) target (fst coordinates) *
        slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          left_cutoff left_potential (\<lambda>_. 1) (fst coordinates)
          (fst (snd coordinates)) *
        slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          right_cutoff right_potential (\<lambda>_. 1) (fst coordinates)
          (snd (snd coordinates),
            slp_mixed_center_finite_right_terminal center coordinates)"
proof -
  let ?root = "fst coordinates"
  let ?left_arrays = "fst (fst (snd coordinates))"
  let ?left_terminal = "snd (fst (snd coordinates))"
  let ?right_arrays = "snd (snd coordinates)"
  let ?right_terminal =
    "slp_mixed_center_finite_right_terminal center coordinates"
  let ?left_pairs =
    "slp_finite_branch_pair_list
      (\<lambda>i. fst ?left_arrays $ i) (\<lambda>i. snd ?left_arrays $ i)"
  let ?right_pairs =
    "slp_finite_branch_pair_list
      (\<lambda>i. fst ?right_arrays $ i) (\<lambda>i. snd ?right_arrays $ i)"
  have reconstruct:
      "slp_mixed_branch_center ?root ?left_pairs ?left_terminal
          ?right_pairs ?right_terminal = center"
    by (rule slp_mixed_center_finite_right_terminal_reconstructs_center)
  have residual:
      "slp_mixed_branch_residual ?root ?left_pairs ?left_terminal
          ?right_pairs ?right_terminal =
        slp_mixed_center_finite_residual center coordinates"
    unfolding slp_mixed_center_finite_residual_def
    by (simp only: prod.sel)
  note target_split = slp_mixed_branch_phase_split[
    of target ?root ?left_pairs ?left_terminal ?right_pairs ?right_terminal]
  have phase_identity:
      "slp_center_phase target center +
          slp_mixed_center_finite_residual center coordinates =
        - slp_center_phase target ?root +
          slp_left_branch_phase target ?left_pairs ?left_terminal +
          slp_right_branch_phase target ?right_pairs ?right_terminal"
    using target_split
    unfolding slp_mixed_branch_phase_def
    by (simp only: reconstruct residual)
  have real_exponent_identity:
      "tau * slp_center_phase target center +
          tau * slp_mixed_center_finite_residual center coordinates =
        (- tau) * slp_center_phase target ?root +
          tau * slp_left_branch_phase target ?left_pairs ?left_terminal +
          tau * slp_right_branch_phase target ?right_pairs ?right_terminal"
  proof -
    have scaled:
        "tau * (slp_center_phase target center +
            slp_mixed_center_finite_residual center coordinates) =
          tau * (- slp_center_phase target ?root +
            slp_left_branch_phase target ?left_pairs ?left_terminal +
            slp_right_branch_phase target ?right_pairs ?right_terminal)"
      by (rule arg_cong[OF phase_identity,
            of "(\<lambda>x::real. tau * x)"])
    show ?thesis
      using scaled by (simp add: algebra_simps)
  qed
  have complex_phase_identity:
      "\<i> * of_real (tau * slp_center_phase target center) +
          \<i> * of_real
            (tau * slp_mixed_center_finite_residual center coordinates) =
        \<i> * of_real ((- tau) * slp_center_phase target ?root) +
          \<i> * of_real
            (tau * slp_left_branch_phase target ?left_pairs ?left_terminal) +
          \<i> * of_real
              (tau * slp_right_branch_phase target ?right_pairs
                ?right_terminal)"
  proof -
    have lifted:
        "(\<i> :: complex) * of_real
            (tau * slp_center_phase target center +
              tau * slp_mixed_center_finite_residual center coordinates) =
          \<i> * of_real
            ((- tau) * slp_center_phase target ?root +
              tau * slp_left_branch_phase target ?left_pairs ?left_terminal +
              tau * slp_right_branch_phase target ?right_pairs ?right_terminal)"
      by (rule arg_cong[OF real_exponent_identity,
            of "(\<lambda>x::real. (\<i> :: complex) * of_real x)"])
    show ?thesis
      using lifted by (simp add: algebra_simps)
  qed
  have oscillation:
      "slp_center_kernel tau target center *
          exp (\<i> * of_real
            (tau * slp_mixed_center_finite_residual center coordinates)) =
        slp_center_kernel (- tau) target ?root *
          exp (\<i> * of_real
            (tau * slp_left_branch_phase target ?left_pairs
              ?left_terminal)) *
          exp (\<i> * of_real
            (tau * slp_right_branch_phase target ?right_pairs
              ?right_terminal))"
    unfolding slp_center_kernel_def
    by (simp only: exp_add[symmetric] complex_phase_identity)
  have left_direct:
      "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          left_cutoff left_potential (\<lambda>_. 1) ?root
          (fst (snd coordinates)) =
        exp (\<i> * of_real
          (tau * slp_left_branch_phase target ?left_pairs ?left_terminal)) *
        slp_left_branch_complex_kernel_joint left_cutoff left_potential
          (\<lambda>_. 1) (?root, fst (snd coordinates))"
    unfolding
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_def
      slp_left_branch_oscillatory_graph_kernel_def
      slp_left_branch_complex_kernel_joint_def
      slp_left_branch_complex_kernel_finite_def
    by (simp only: prod.sel)
  have right_direct:
      "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          right_cutoff right_potential (\<lambda>_. 1) ?root
          (?right_arrays, ?right_terminal) =
        exp (\<i> * of_real
          (tau * slp_right_branch_phase target ?right_pairs
            ?right_terminal)) *
        slp_right_branch_complex_kernel_joint right_cutoff right_potential
          (\<lambda>_. 1) (?root, (?right_arrays, ?right_terminal))"
    by (simp only:
      slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_direct
      prod.sel)
  have multiplication_transport:
      "\<And>a b c d e left_kernel right_kernel root_factor :: complex.
        a * b = c * d * e \<Longrightarrow>
        a * (b * (root_factor * left_kernel * right_kernel)) =
          root_factor * c * (d * left_kernel) * (e * right_kernel)"
  proof -
    fix a b c d e left_kernel right_kernel root_factor :: complex
    assume factor: "a * b = c * d * e"
    have regroup_left:
        "a * (b * (root_factor * left_kernel * right_kernel)) =
          (a * b) * (root_factor * left_kernel * right_kernel)"
      by (simp only: mult.assoc[symmetric])
    have transported:
        "(a * b) * (root_factor * left_kernel * right_kernel) =
          (c * d * e) * (root_factor * left_kernel * right_kernel)"
      by (rule arg_cong[OF factor,
            of "(\<lambda>x::complex.
              x * (root_factor * left_kernel * right_kernel))"])
    have regroup_right:
        "(c * d * e) * (root_factor * left_kernel * right_kernel) =
          root_factor * c * (d * left_kernel) * (e * right_kernel)"
      by (simp only: mult.assoc mult.left_commute mult.commute)
    have first_two:
        "a * (b * (root_factor * left_kernel * right_kernel)) =
          (c * d * e) * (root_factor * left_kernel * right_kernel)"
      by (rule trans[OF regroup_left transported])
    show
        "a * (b * (root_factor * left_kernel * right_kernel)) =
          root_factor * c * (d * left_kernel) * (e * right_kernel)"
      by (rule trans[OF first_two regroup_right])
  qed
  show ?thesis
    unfolding slp_mixed_center_finite_oscillatory_integrand_def
      slp_parameterized_real_phase_integrand_def
      slp_mixed_center_finite_complex_amplitude_def
      slp_mixed_center_finite_inserted_coordinates_def
    apply (simp only: prod.sel left_direct right_direct)
    apply (rule multiplication_transport)
    by (rule oscillation)
qed

end
