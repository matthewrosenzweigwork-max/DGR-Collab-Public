import Batteries.Tactic.Alias
import DGRHS.Kinetic.KineticSingularGibbs

/-! Packet P15: Original aliases for the kinetic Gibbs identification of the singular laws
(Remark 2.1 `rem:torus-kinetic-variants`, kinetic half, TeX 495; Remark 2.12, TeX 833):
the kinetic canonical collision-zero ensemble of `H_N + Σ|v_i|²/2` (Lebesgue velocity
reference) equals `Q_{N,β}(μ) ⊗ Maxwellian`. Each alias has exactly the type of the
underlying declaration. -/

/-- rem:torus-kinetic-variants (kinetic half), derived kinetic partition function
`Z^{kin}_{N,β} = Z_{N,β} (√(2π/β))^{N d}`. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularPartition_eq := DGRHS.Kinetic.kineticCanonicalSingularPartition_eq

/-- rem:torus-kinetic-variants (kinetic half), (A): generic tensorization
`kinetic canonical singular law = canonical singular law ⊗ Maxwellian`. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularLaw_eq_prod := DGRHS.Kinetic.kineticCanonicalSingularLaw_eq_prod

/-- rem:torus-kinetic-variants (kinetic half), (A) with the premises of
`canonicalSingularLaw_eq_tilted`. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularLaw_eq_prod_of_integrable := DGRHS.Kinetic.kineticCanonicalSingularLaw_eq_prod_of_integrable

/-- rem:torus-kinetic-variants (kinetic half), (B) logarithmic case. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_sourceLogGibbs_prod_eq_tilted := DGRHS.Kinetic.kinetic_sourceLogGibbs_prod_eq_tilted

/-- rem:torus-kinetic-variants (kinetic half), (B) Riesz case. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_sourceRieszGibbs_prod_eq_tilted := DGRHS.Kinetic.kinetic_sourceRieszGibbs_prod_eq_tilted

/-- rem:torus-kinetic-variants (kinetic half), (C) logarithmic case:
kinetic canonical ensemble of `H_N + KE` equals `Q_{N,β}(μ) ⊗ Maxwellian`. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularLaw_log_eq := DGRHS.Kinetic.kineticCanonicalSingularLaw_log_eq

/-- rem:torus-kinetic-variants (kinetic half), (C) Riesz case (`sourceT28Gibbs`, `β : ℝ≥0`). -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularLaw_riesz_eq := DGRHS.Kinetic.kineticCanonicalSingularLaw_riesz_eq

/-- rem:torus-kinetic-variants (kinetic half), (C) Riesz case, real `β` as in the P3 export. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularLaw_riesz_eq_real := DGRHS.Kinetic.kineticCanonicalSingularLaw_riesz_eq_real

#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularPartition_eq
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularLaw_eq_prod
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularLaw_eq_prod_of_integrable
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_sourceLogGibbs_prod_eq_tilted
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_sourceRieszGibbs_prod_eq_tilted
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularLaw_log_eq
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularLaw_riesz_eq
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kineticCanonicalSingularLaw_riesz_eq_real
