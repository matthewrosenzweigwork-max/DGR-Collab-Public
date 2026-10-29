/-!
# Wave 0 namespace marker

Core-only module (no Mathlib import) that fixes the campaign's top-level namespace `DGPS`.
Every campaign declaration lives under `DGPS`; see `Campaign/tools/isolation_check.sh`.
-/

namespace DGPS

/-- Checkpoint the campaign branch was cut from. -/
def campaignCheckpoint : String := "d880f61501024eacf8cdb0c6a7de5c821c02d412"

end DGPS
