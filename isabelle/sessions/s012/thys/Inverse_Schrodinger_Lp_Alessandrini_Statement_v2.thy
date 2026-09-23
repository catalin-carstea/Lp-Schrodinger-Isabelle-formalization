theory Inverse_Schrodinger_Lp_Alessandrini_Statement_v2
  imports Paper_Inverse_Schrodinger_Lp_Uniqueness.Inverse_Schrodinger_Lp_Setup
begin

section \<open>Universal solution-pair orthogonality\<close>

text \<open>
  The zero interior pairing is explicitly guarded by integrability because
  Isabelle's Bochner integral is totalized.  The pairing is complex bilinear:
  no conjugation occurs.  Weak-solution data retain their recorded weak
  gradients, while only their scalar representatives occur in this product.
\<close>

definition slp_alessandrini_orthogonality ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> bool"
where
  "slp_alessandrini_orthogonality Omega V V_tilde \<longleftrightarrow>
    (\<forall>F G.
      slp_weak_solution Omega V F \<and>
      slp_weak_solution Omega V_tilde G
      \<longrightarrow>
      set_integrable lborel Omega
        (\<lambda>x. (V x - V_tilde x) * fst F x * fst G x) \<and>
      set_lebesgue_integral lborel Omega
        (\<lambda>x. (V x - V_tilde x) * fst F x * fst G x) = 0)"

section \<open>Replacement conditional uniqueness target\<close>

text \<open>
  This versioned candidate is a user-requested intermediate target, not the
  manuscript's Dirichlet-to-Neumann theorem.  It retains the manuscript domain,
  exponent, potential, bilinear, and almost-everywhere conventions, and assumes
  directly the universal zero pairing that the manuscript derives from the
  forward problem and equality of boundary maps.
\<close>

definition slp_alessandrini_uniqueness_claim ::
  "real \<Rightarrow> slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> bool"
where
  "slp_alessandrini_uniqueness_claim p Omega V V_tilde \<longleftrightarrow>
    (1 < p \<and>
     slp_bounded_smooth_domain Omega \<and>
     slp_complex_lp_on p Omega V \<and>
     slp_complex_lp_on p Omega V_tilde \<and>
     slp_alessandrini_orthogonality Omega V V_tilde)
    \<longrightarrow> slp_potential_ae_equal Omega V V_tilde"

end
