import Batteries.Tactic.Alias
import DGRHS.Gaussian.PeriodicRieszEquilibrium
import DGRHS.Gaussian.PeriodicLogEquilibrium
import DGRHS.Gaussian.PeriodicRieszEntropicCommutatorPrinted
import DGRHS.Gaussian.PeriodicLogEntropicCommutator

/-! Source-facing export (packet P9h) of the commutator/free-energy results on the flat torus `𝕋^d`
(Remark 2.1 `rem:torus-kinetic-variants`, TeX 492-496).

Each `alias` creates a new declaration with EXACTLY the type of an existing root declaration (no
premise added or removed).  The module is not imported by `Release.lean`; the coordinator wires it.

Unit 3: Theorem 2.8 for the torus LOG kernel with the printed constants and every probability competitor.

Unit 2: Theorem 2.8 (`thm:entropicCommutator`, TeX 691-736) for the torus Riesz kernel with the printed
constants.

Unit 1: Corollary 2.3 (`cor:equilibriumFreeEnergyCorrection`, TeX 558-595) for the torus Riesz kernel
(combined thermal free energy: integrability of `βV + log μ` is a conclusion, owner convention,
printed rate `(log(e+N))^{-(d-2s)/(2s)}` for the full range `0<s<d/2` from the P9f full-range torus
Theorem 2.2(ii)) and for the torus LOG kernel (separate-integral free energy, `V ∈ L¹(μ)` and the
entropy derived, power rate `(e+N)^{-c_log}`). -/

/-- cor:equilibriumFreeEnergyCorrection (source 558-595), torus Riesz, exact reduction
`Z_{N,β} = e^{-βN F_{β,V}(μ_β)} K_{N,β}(μ_β)` with the combined thermal cost; matches
`DGRHS.CLT.sourceRiesz_thermal_equilibrium_macroscopic` (packet P9h). -/
alias DGRHS.Original.cor_equilibriumFreeEnergyCorrection.riesz_torus_macroscopic :=
  DGRHS.Periodic.periodicRiesz_thermal_equilibrium_macroscopic

/-- cor:equilibriumFreeEnergyCorrection (source 558-595), torus Riesz, free-energy expansion with
rate `(log(e+N))^{-(d-2s)/(2s)}`; matches `DGRHS.CLT.sourceRiesz_thermal_equilibrium_correction`
(packet P9h). -/
alias DGRHS.Original.cor_equilibriumFreeEnergyCorrection.riesz_torus :=
  DGRHS.Periodic.periodicRiesz_thermal_equilibrium_correction

/-- cor:equilibriumFreeEnergyCorrection (source 558-595), torus LOG, exact reduction with the
separate-integral free energy; matches `DGRHS.CLT.sourceLog_equilibrium_macroscopic_original`
(packet P9h). -/
alias DGRHS.Original.cor_equilibriumFreeEnergyCorrection.log_torus_macroscopic :=
  DGRHS.Periodic.periodicLog_equilibrium_macroscopic

/-- cor:equilibriumFreeEnergyCorrection (source 558-595), torus LOG, free-energy expansion with the
power rate `(e+N)^{-c_log}`; matches `DGRHS.CLT.sourceLog_equilibrium_correction_original`
(packet P9h). -/
alias DGRHS.Original.cor_equilibriumFreeEnergyCorrection.log_torus :=
  DGRHS.Periodic.periodicLog_equilibrium_correction

/-- cor:equilibriumFreeEnergyCorrection, torus LOG, with the printed hypotheses
`eq:logRateExtraAssumptions` restated literally (unused; automatic on the torus; packet P9h). -/
alias DGRHS.Original.cor_equilibriumFreeEnergyCorrection.log_torus_printed :=
  DGRHS.Periodic.periodicLog_equilibrium_correction_printed

/-- thm:entropicCommutator (source 691-736), torus Riesz branch `0 < s < d/2` (Remark 2.1), with the
printed constants of Remark A.1 (`C_em = e + L` for `β ≤ β_loc`, `C_em = e^{-β I_μ} (e+L)^{1/2}
C_ub^{1/2}` for `β > β_loc`); matches
`DGRHS.Commutator.exists_sourceRiesz_entropic_commutator_printed_constants`.  The partition constants
`C_ub`, `C_pf` and the printed constant `C_em` are chosen after the background density `ρ ≤ M` (as in the
printed `C_pf(β,μ)`, `C_em(β,μ,v,n)`); `β_loc` and `ε` do not depend on `ρ` (packet P9h, unit 2). -/
alias DGRHS.Original.thm_entropicCommutator.riesz_torus :=
  DGRHS.Periodic.exists_periodicRiesz_entropic_commutator_printed_constants

/-- thm:entropicCommutator (source 691-736), torus LOG branch (Remark 2.1), with the printed constants
of Remark A.1 (`C_em = e^{-β I_μ}(e+L)` for `β ≤ β_loc`, `C_em = e^{-β I_μ}(e+L)^{1/2} C_ub^{1/2}` for
`β > β_loc`) and the printed piecewise `ε_{β,n}`; matches `DGRHS.Commutator.exists_sourceLog_entropic_commutator`
with the same quantifier order (`C_sr`, then `K, v, ρ, M`, then `β_loc`, then `β`, then `C_ub, C_pf`) and
every probability competitor `ν` (extended free energy keeping `+∞`).  Packet P9h, unit 3. -/
alias DGRHS.Original.thm_entropicCommutator.log_torus :=
  DGRHS.Periodic.exists_periodicLog_entropic_commutator

#print axioms DGRHS.Original.cor_equilibriumFreeEnergyCorrection.riesz_torus_macroscopic
#print axioms DGRHS.Original.cor_equilibriumFreeEnergyCorrection.riesz_torus
#print axioms DGRHS.Original.cor_equilibriumFreeEnergyCorrection.log_torus_macroscopic
#print axioms DGRHS.Original.cor_equilibriumFreeEnergyCorrection.log_torus
#print axioms DGRHS.Original.cor_equilibriumFreeEnergyCorrection.log_torus_printed
#print axioms DGRHS.Original.thm_entropicCommutator.riesz_torus
#print axioms DGRHS.Original.thm_entropicCommutator.log_torus
