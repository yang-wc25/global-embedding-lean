import Lake
open Lake DSL

package globalEmbedding

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

lean_lib AuxNormBridge where
  srcDir := "src/Analysis"
  globs := #[.andSubmodules `AuxNormBridge]

lean_lib CollarCompletion where
  srcDir := "src/Geometry"
  globs := #[.andSubmodules `CollarCompletion]

lean_lib CompletionIntegration where
  srcDir := "src/Increments"
  globs := #[.andSubmodules `CompletionIntegration]

lean_lib FaithfulCollars where
  srcDir := "src/Geometry"
  globs := #[.andSubmodules `FaithfulCollars]

lean_lib FaithfulIncrements where
  srcDir := "src/Increments"
  globs := #[.andSubmodules `FaithfulIncrements]

lean_lib FaithfulIntegration where
  srcDir := "src/Increments"
  globs := #[.andSubmodules `FaithfulIntegration]

lean_lib FaithfulRepair where
  srcDir := "src/Repair"
  globs := #[.andSubmodules `FaithfulRepair]

@[default_target]
lean_lib GlobalEmbedding where
  srcDir := "src/Foundations"
  globs := #[.andSubmodules `GlobalEmbedding]

lean_lib IncrementsBridge where
  srcDir := "src/Increments"
  globs := #[.andSubmodules `IncrementsBridge]

lean_lib IncrementsCompletion where
  srcDir := "src/Increments"
  globs := #[.andSubmodules `IncrementsCompletion]

lean_lib Initialization where
  srcDir := "src/Initialization"
  globs := #[.andSubmodules `Initialization]

lean_lib Main where
  srcDir := "src/Main"
  globs := #[.andSubmodules `Main]

lean_lib NormalPolar where
  srcDir := "src/Probes"
  globs := #[.andSubmodules `NormalPolar]

lean_lib OriginalAuxiliary where
  srcDir := "src/Analysis"
  globs := #[.andSubmodules `OriginalAuxiliary]

lean_lib OriginalCollars where
  srcDir := "src/Geometry"
  globs := #[.andSubmodules `OriginalCollars]

lean_lib OriginalIncrements where
  srcDir := "src/Increments"
  globs := #[.andSubmodules `OriginalIncrements]

lean_lib OriginalIntegration where
  srcDir := "src/Increments"
  globs := #[.andSubmodules `OriginalIntegration]

lean_lib Probes where
  srcDir := "src/Probes"
  globs := #[.andSubmodules `Probes]

lean_lib ProbesClosure where
  srcDir := "src/Probes"
  globs := #[.andSubmodules `ProbesClosure]

lean_lib Repair where
  srcDir := "src/Repair"
  globs := #[.andSubmodules `Repair]

lean_lib RepairClosure where
  srcDir := "src/Repair"
  globs := #[.andSubmodules `RepairClosure]

lean_lib Round2 where
  srcDir := "src/Upgrade"
  globs := #[.andSubmodules `Round2]

lean_lib Smoothing where
  srcDir := "src/Analysis"
  globs := #[.andSubmodules `Smoothing]

lean_lib SourceCollarsBridge where
  srcDir := "src/Geometry"
  globs := #[.andSubmodules `SourceCollarsBridge]

lean_lib Upgrade where
  srcDir := "src/Upgrade"
  globs := #[.andSubmodules `Upgrade]

lean_lib UpgradeContinuation where
  srcDir := "src/Upgrade"
  globs := #[.andSubmodules `UpgradeContinuation]
