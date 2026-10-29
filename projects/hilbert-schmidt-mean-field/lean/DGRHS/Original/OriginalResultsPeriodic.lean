import Batteries.Tactic.Alias
import DGRHS.Gaussian.PeriodicAttractiveOriginalProposition
import DGRHS.Gaussian.PeriodicD11GlobalThreshold
import DGRHS.Gaussian.PeriodicD11Pressure
import DGRHS.Gaussian.PeriodicD1DysonSourceBridge
import DGRHS.Gaussian.PeriodicD1EntropyEnergy
import DGRHS.Gaussian.PeriodicD1GlobalThreshold
import DGRHS.Gaussian.PeriodicD1PhysicalLimit

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). Source-facing export suite, area: Periodic.

Each `alias` creates a new declaration with EXACTLY the type of an existing
root declaration (no premise added or removed). The source label, lines and the
row disposition from reports/DISPOSITIONS_253.json are recorded beside it; a
row marked SOURCE_DISCREPANCY or UNRESOLVED exports only the valid corrected or
partial statement named in that row's qualification, never the printed
auxiliary claim. Target bytes/status are bound by the gate records cited in the
disposition, not by this file. -/

/-- prop:periodicAttractiveLowerBounds (source 3089–3110); row disposition REUSED. -/
alias DGRHS.Original.prop_periodicAttractiveLowerBounds.Periodic_periodicAttractiveLowerBounds_source := DGRHS.Periodic.periodicAttractiveLowerBounds_source

/-- rem:d11CriticalExponential (source 3242–3250); row disposition REUSED. -/
alias DGRHS.Original.rem_d11CriticalExponential.Periodic_periodic_d11_critical_pressure := DGRHS.Periodic.periodic_d11_critical_pressure

/-- rem:d11CriticalExponential (source 3242–3250); row disposition REUSED. -/
alias DGRHS.Original.rem_d11CriticalExponential.Periodic_periodic_d11_global_threshold_strict := DGRHS.Periodic.periodic_d11_global_threshold_strict

/-- sent:periodicD1BetaGm (source 3087–3087); row disposition REUSED (coordinator-owned physical d1; root Stage6 PASS supplement; review status per gate). -/
alias DGRHS.Original.sent_periodicD1BetaGm.Periodic_periodicD1_globalMinimizationThreshold := DGRHS.Periodic.periodicD1_globalMinimizationThreshold

/-- sent:periodicD1BetaGm (source 3087–3087); row disposition REUSED (coordinator-owned physical d1; root Stage6 PASS supplement; review status per gate). -/
alias DGRHS.Original.sent_periodicD1BetaGm.Periodic_periodicD1_entropy_energy_extended := DGRHS.Periodic.periodicD1_entropy_energy_extended

/-- sent:periodicD1BetaGm (source 3087–3087); row disposition REUSED (coordinator-owned physical d1; root Stage6 PASS supplement; review status per gate). -/
alias DGRHS.Original.sent_periodicD1BetaGm.Periodic_periodicD1_attractive_partition_exact := DGRHS.Periodic.periodicD1_attractive_partition_exact

/-- sent:periodicD1BetaGm (source 3087–3087); row disposition REUSED (coordinator-owned physical d1; root Stage6 PASS supplement; review status per gate). -/
alias DGRHS.Original.sent_periodicD1BetaGm.Periodic_periodicD1_attractive_partition_tendsto := DGRHS.Periodic.periodicD1_attractive_partition_tendsto
