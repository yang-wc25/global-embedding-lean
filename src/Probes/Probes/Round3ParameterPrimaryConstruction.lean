import Probes.ActualSecondaryRawMetricData

/-! # Same actual primary construction on a general parameter space

The finite spatial solver never differentiates the parameter variable.  This
file makes that fact explicit: the parameter has only a topology, while every
local source, finite polynomial, full reconstruction, supported extension,
actual wave and actual mean is still the original literal construction.
No successful output or norm estimate is a field of the primitive family.
-/

noncomputable section
open Manifold Filter
open scoped ContDiff Topology BigOperators ComplexConjugate

namespace GlobalEmbedding.Continuation

open GlobalEmbedding.Paper

variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]


/-- Same literal primary construction for an arbitrary topological parameter space.
Original fields and actual produced
charts/subcutoffs only. Normal membership is required only on actual targets;
outside values impose no inactive normality condition. No output field occurs.
Source: original primary data and subordinate charts, main.tex594–650. -/
structure Round3ParameterPrimaryFamily (F : P → M → (EuclideanSpace ℝ (Fin N))) where
  phase : Λ → P × M → ℝ
  cutoff : Λ → P × M → ℝ
  normal : Λ → P × M → (EuclideanSpace ℝ (Fin N))
  linearArgument : Λ → (t : P) → (x : M) →
    LinearMap.BilinForm ℝ (TangentSpace I x) →ₗ[ℝ] ℝ
  eta : Λ → Β → P × M → ℝ
  chart : Λ → Β → OpenPartialHomeomorph (P × M) (P × (EuclideanSpace ℝ (Fin (m + 1))))
  inverse : Λ → Β → P → (EuclideanSpace ℝ (Fin (m + 1))) → M
  normal_mem : ∀ ν β z, z ∈ (chart ν β).target →
    normal ν (z.1, inverse ν β z.1 z.2) ∈
      normalSpace (I := I) (F z.1) (inverse ν β z.1 z.2)

variable (F : P → M → (EuclideanSpace ℝ (Fin N)))
  (hF : ∀ t, ContMDiff I 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞ (F t))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)

/-- Original b=chi*sqrt(ell(A)), on the SAME native tensor field. Source:594–599. -/
def round3ParameterPrimaryB
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (ν : Λ) (z : P × M) : ℝ :=
  g.cutoff ν z * Real.sqrt (g.linearArgument ν z.1 z.2 (input z.1 z.2))

/-- The actual normalized global free amplitude, not an assumed correction.
Source: sqrt2*tau*b*n in main.tex646–650. -/
def round3ParameterPrimaryFree
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (tau : ℝ) (ν : Λ) (z : P × M) : (EuclideanSpace ℝ (Fin N)) :=
  (Real.sqrt 2 * tau * round3ParameterPrimaryB F g input ν z) • g.normal ν z

/-- The actual local normal free datum. On the actual target it is eta times
the original free amplitude. Outside the target the normal datum is zero,
without imposing normality of arbitrary original outside extensions. Source:645–650. -/
def round3ParameterPrimaryLocalFree
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (tau : ℝ)
    (ν : Λ) (β : Β) (t : P) (x : (EuclideanSpace ℝ (Fin (m + 1)))) :
    normalSpace (I := I) (F t) (g.inverse ν β t x) := by
  classical
  exact if hz : (t, x) ∈ (g.chart ν β).target then
    (g.eta ν β (t, g.inverse ν β t x) *
      (Real.sqrt 2 * tau * round3ParameterPrimaryB F g input ν
        (t, g.inverse ν β t x))) •
      ⟨g.normal ν (t, g.inverse ν β t x), g.normal_mem ν β (t, x) hz⟩
    else 0

/-- SAME original h=0 source, with the subcutoff INSIDE the free datum.
Source: main.tex621–650; no independent source/solver is supplied. -/
def round3ParameterPrimarySource
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (tau : ℝ)
    (ν : Λ) (β : Β) (z : P × (EuclideanSpace ℝ (Fin (m + 1)))) : (Fin (m + 1) → ℂ) :=
  incrementsModeComplexInclude (incrementsModeSource (F z.1) (hF z.1)
    (g.inverse ν β z.1) (fun _ _ _ ↦ 0)
    (round3ParameterPrimaryLocalFree F g input tau ν β z.1) z.2)

/-- Literal finite polynomial with the canonical actual A/B and source.
Source: main.tex641–650. Length is fixed before any observation order. -/
def round3ParameterPrimaryFiniteU
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (ν : Λ) (β : Β) (t : P) : (EuclideanSpace ℝ (Fin (m + 1))) → (Fin (m + 1) → ℂ) :=
  incrementsActualModeSum
    (incrementsModeComplexFirstOrderA (F t) (hF t) (g.inverse ν β t))
    (incrementsModeComplexFirstOrderB (F t) (hF t) (g.inverse ν β t))
    ((tau : ℂ) / Complex.I) length
    (fun x ↦ round3ParameterPrimarySource F hF g input tau ν β (t, x))

/-- Canonical fullZ of a fixed real/imaginary channel of SAME finite u.
Only the real channel has the original free datum. Source:617–650. -/
def round3ParameterPrimaryLocalZ
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (realChannel : Bool) (ν : Λ) (β : Β) (z : P × (EuclideanSpace ℝ (Fin (m + 1)))) :
    (EuclideanSpace ℝ (Fin N)) :=
  let ch := if realChannel then incrementsModeRealPart else incrementsModeImagPart
  incrementsModeFullReconstruction (F z.1) (hF z.1) (g.inverse ν β z.1)
    (fun x ↦ ch (round3ParameterPrimaryFiniteU F hF g input length tau ν β z.1 x))
    (fun _ _ _ ↦ 0)
    (fun x ↦ if realChannel then
      round3ParameterPrimaryLocalFree F g input tau ν β z.1 x else 0) z.2

/-- SAME supported pullback, with no cutoff multiplied onto its output.
Source: actual relative-W pullback9c522, original645–650. -/
def round3ParameterPrimaryExtension
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (realChannel : Bool) (ν : Λ) (β : Β) (z : P × M) : (EuclideanSpace ℝ (Fin N)) := by
  classical
  exact if z ∈ (g.chart ν β).source then
    round3ParameterPrimaryLocalZ F hF g input length tau realChannel ν β (g.chart ν β z)
    else 0

/-- Group actual subordinate amplitudes by ORIGINAL primary phase before any
coefficient extraction. Source:645–655; same-phase cross terms are retained. -/
def round3ParameterPrimaryAmplitude
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (realChannel : Bool) (ν : Λ) (z : P × M) : (EuclideanSpace ℝ (Fin N)) :=
  ∑ β, round3ParameterPrimaryExtension F hF g input length tau realChannel ν β z

/-- Literal normalized global real primary wave from these SAME fullZ amplitudes.
Source: U1(A), main.tex646–655. No observation-order or supplied U occurs. -/
def round3ParameterPrimaryWave
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (z : P × M) : (EuclideanSpace ℝ (Fin N)) :=
  ∑ ν, (Real.cos (g.phase ν z / tau) •
      round3ParameterPrimaryAmplitude F hF g input length tau true ν z -
    Real.sin (g.phase ν z / tau) •
      round3ParameterPrimaryAmplitude F hF g input length tau false ν z)

/-- Real/imaginary coefficient maps dR-dphi*I/tau and dI+dphi*R/tau of SAME
global amplitude. These are native CLMs, not prescribed derivative identities.
Source: original primary first jets, main.tex646–655. -/
def round3ParameterPrimaryCoefficient
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (realChannel : Bool) (ν : Λ) (z : P × M) :
    TangentSpace I z.2 →L[ℝ] (EuclideanSpace ℝ (Fin N)) :=
  let own := round3ParameterPrimaryAmplitude F hF g input length tau realChannel ν
  let other := round3ParameterPrimaryAmplitude F hF g input length tau (!realChannel) ν
  let slow := incrementsGlobalSpatialDerivative (I := I) own z
  let fast := (incrementsGlobalScalarDerivative (I := I) (g.phase ν) z).smulRight
    ((tau⁻¹) • other z)
  if realChannel then slow - fast else slow + fast

/-- Native real symmetric mean candidate from the ACTUAL global coefficient maps.
The original zero-germ hypotheses must identify it with the true zero coefficient.
No mean oracle or independent chart matrix is supplied. Source: main.tex651–655. -/
def round3ParameterPrimaryMean
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (t : P) (x : M) : LinearMap.BilinForm ℝ (TangentSpace I x) :=
  (1 / 2 : ℝ) • ∑ ν, (
    LinearMap.BilinForm.comp (innerₗ (EuclideanSpace ℝ (Fin N)))
      (round3ParameterPrimaryCoefficient F hF g input length tau true ν (t, x)).toLinearMap
      (round3ParameterPrimaryCoefficient F hF g input length tau true ν (t, x)).toLinearMap +
    LinearMap.BilinForm.comp (innerₗ (EuclideanSpace ℝ (Fin N)))
      (round3ParameterPrimaryCoefficient F hF g input length tau false ν (t, x)).toLinearMap
      (round3ParameterPrimaryCoefficient F hF g input length tau false ν (t, x)).toLinearMap)

/-- The SAME native tensor T(A)=M(A)-A, not an independent data field or bound.
Source: original main.tex651–667. -/
def round3ParameterPrimaryMeanError
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ) :
    (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x) :=
  fun t x ↦ round3ParameterPrimaryMean F hF g input length tau t x - input t x


end GlobalEmbedding.Continuation
