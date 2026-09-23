theory Evans_Compact_Support_W1p_Zero_Density_Interface
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Semantics"
begin

section \<open>Compact-support density in planar complex W1p\<close>

definition evans_compact_support_w1p_zero_density_claim :: bool
where
  "evans_compact_support_w1p_zero_density_claim \<longleftrightarrow>
    (\<forall>p X u Du K.
      1 \<le> p \<and>
      open X \<and>
      compact K \<and>
      K \<subseteq> X \<and>
      slp_w1p_pair_on p X u Du \<and>
      (\<forall>x \<in> X - K. u x = 0 \<and> (\<forall>i. Du x $ i = 0))
      \<longrightarrow> slp_w1p_zero_pair_on p X u Du)"

text \<open>
  This is the planar complex compact-support consequence of Evans's local
  Sobolev mollifier approximation at k=1 and finite p.  Compact containment of
  the common support lets one use a single sequence of sufficiently small
  mollifier scales; the weak-derivative/convolution identity supplies
  simultaneous convergence of the function and both gradient components.
  Real and imaginary parts use the same scale before recombination.

  The pointwise representative-level support premise is deliberately stronger
  than an equivalence-class support assertion.  The conclusion is only the
  project's already defined smooth-test-function closure.  No trace,
  extension, embedding, Rellich, domain-regularity, endpoint, or inverse-
  problem claim is included.
\<close>

locale evans_compact_support_w1p_zero_density =
  assumes evans_compact_support_w1p_zero_density:
    "evans_compact_support_w1p_zero_density_claim"

end
