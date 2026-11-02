# global-embedding W2 port

Source: wxkj99/calabi-yau at 91b1ddf000c7028bc42ae6102eba0e2042eb37ff.
The original per-file qinz1yang/differential-geometry provenance headers remain intact.
Apache-2.0 LICENSE, repository NOTICE and referenced upstream licenses/notices are preserved.
The copied NOTICE's `licenses/...` paths correspond to `upstream-licenses/...` here.

Selected closure: 25 modules, 12560 original source lines. Exact source/candidate paths,
SHA256 and per-file modifications: ../../../constant-schauder-port-native-manifest.json
(relative to this directory in the sandbox). The manifest and review report are authoritative.

Changes:
- Internal imports `CalabiYau.*` become `GlobalEmbedding.External.CalabiYau.*`.
- Each file states `set_option maxSynthPendingDepth 3`, exactly preserving the pinned
  source lakefile.toml setting without changing this project's Lake configuration.
- Holder.Basic: close a residual `gcongr` goal with `exact sub_nonneg.mpr halphaReal`.
- ConstantCoefficient.Estimate: remove its unused ConstantCoefficient.Operator import,
  retaining every original mathematical declaration and proof in Estimate.

No target, theorem hypothesis, mathematical definition, dependency version, Lean version,
axiom or existing Mathlib instance is changed. No new instance aliases are present in this
canonical candidate. Earlier instance-alias and 30-module drafts remain separate evidence.

Certification here is the scope-isolated single-file compile on the project's pinned
Lean/Mathlib4.35.0: exit0, 27.5s, no errors/warnings/sorry, both final estimates standard
three axioms. Root must still independently review, ordinarily import-compile, land and
verify with its global build. W2 has not performed those integration actions.

Root integration: removed two duplicate private Holder shift helper declarations from ThirdDerivative and HeatPotential.Schauder; inlined their unchanged elementary distance/Holder proofs at actual uses because the previous same statement is private to another source module. Public statements and all remaining proofs unchanged. Exact M adaptations and source manifests retained.
