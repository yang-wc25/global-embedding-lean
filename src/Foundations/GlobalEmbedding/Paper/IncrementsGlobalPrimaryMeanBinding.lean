import GlobalEmbedding.Paper.IncrementsActualFullMeanCoefficient
import GlobalEmbedding.Paper.IncrementsModeSupportedChartPullback
import GlobalEmbedding.Paper.IncrementsFullNormalizedPrimaryError
import GlobalEmbedding.Paper.IncrementsOriginalNativeCoordinates
import GlobalEmbedding.Paper.IncrementsModeJointSourceRegularity
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Stage2: the same global primary wave and native mean tensor

Source: original main.tex641–667. DAG: increments-global-primary-mean-binding.
ROOT04:05 authorized coherent literal definitions and ONE named theorem hole
only. No proof implementation before exact ROOT lock. The family below is an
explicit INTERNAL primitive chart/source family, not a new original datum or
an opaque bundle of successful outputs. It supplies no R/Z/U/T, desired support,
coefficient identity, estimate or finite-reserve result. All amplitudes are the
SAME canonical finite fullZ, pulled back through their actual joint charts.
Original full-target/profile/radius uniformity remains unlocked.
-/

noncomputable section
open Manifold Filter
open scoped ContDiff Topology BigOperators ComplexConjugate

namespace GlobalEmbedding.Paper

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]


/-- Explicit INTERNAL primitive family: original fields and actual produced
charts/subcutoffs only. Normal membership is required only on actual targets;
outside values impose no inactive normality condition. No output field occurs.
Source: original primary data and subordinate charts, main.tex594–650. -/
structure IncrementsGlobalPrimaryFamily (F : Ep → M → (EuclideanSpace ℝ (Fin N))) where
  phase : Λ → Ep × M → ℝ
  cutoff : Λ → Ep × M → ℝ
  normal : Λ → Ep × M → (EuclideanSpace ℝ (Fin N))
  linearArgument : Λ → (t : Ep) → (x : M) →
    LinearMap.BilinForm ℝ (TangentSpace I x) →ₗ[ℝ] ℝ
  eta : Λ → Β → Ep × M → ℝ
  chart : Λ → Β → OpenPartialHomeomorph (Ep × M) (Ep × (EuclideanSpace ℝ (Fin (m + 1))))
  inverse : Λ → Β → Ep → (EuclideanSpace ℝ (Fin (m + 1))) → M
  normal_mem : ∀ ν β z, z ∈ (chart ν β).target →
    normal ν (z.1, inverse ν β z.1 z.2) ∈
      normalSpace (I := I) (F z.1) (inverse ν β z.1 z.2)

variable (F : Ep → M → (EuclideanSpace ℝ (Fin N)))
  (hF : ∀ t, ContMDiff I 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞ (F t))
  (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)

/-- Native relative support of a primitive joint scalar on W, not ambient
closedness or a support assertion about a constructed output. Source:607–609. -/
def incrementsGlobalRelativeSupport (W : Set (Ep × M)) (f : Ep × M → ℝ) : Set (Ep × M) :=
  Subtype.val '' tsupport (fun z : W ↦ f z.val)

/-- Original b=chi*sqrt(ell(A)), on the SAME native tensor field. Source:594–599. -/
def incrementsGlobalPrimaryB
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (ν : Λ) (z : Ep × M) : ℝ :=
  g.cutoff ν z * Real.sqrt (g.linearArgument ν z.1 z.2 (input z.1 z.2))

/-- The actual normalized global free amplitude, not an assumed correction.
Source: sqrt2*tau*b*n in main.tex646–650. -/
def incrementsGlobalPrimaryFree
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (tau : ℝ) (ν : Λ) (z : Ep × M) : (EuclideanSpace ℝ (Fin N)) :=
  (Real.sqrt 2 * tau * incrementsGlobalPrimaryB F g input ν z) • g.normal ν z

/-- The actual local normal free datum. On the actual target it is eta times
the original free amplitude. Outside the target the normal datum is zero,
without imposing normality of arbitrary original outside extensions. Source:645–650. -/
def incrementsGlobalPrimaryLocalFree
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (tau : ℝ)
    (ν : Λ) (β : Β) (t : Ep) (x : (EuclideanSpace ℝ (Fin (m + 1)))) :
    normalSpace (I := I) (F t) (g.inverse ν β t x) := by
  classical
  exact if hz : (t, x) ∈ (g.chart ν β).target then
    (g.eta ν β (t, g.inverse ν β t x) *
      (Real.sqrt 2 * tau * incrementsGlobalPrimaryB F g input ν
        (t, g.inverse ν β t x))) •
      ⟨g.normal ν (t, g.inverse ν β t x), g.normal_mem ν β (t, x) hz⟩
    else 0

/-- SAME original h=0 source, with the subcutoff INSIDE the free datum.
Source: main.tex621–650; no independent source/solver is supplied. -/
def incrementsGlobalPrimarySource
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (tau : ℝ)
    (ν : Λ) (β : Β) (z : Ep × (EuclideanSpace ℝ (Fin (m + 1)))) : (Fin (m + 1) → ℂ) :=
  incrementsModeComplexInclude (incrementsModeSource (F z.1) (hF z.1)
    (g.inverse ν β z.1) (fun _ _ _ ↦ 0)
    (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1) z.2)

/-- Literal finite polynomial with the canonical actual A/B and source.
Source: main.tex641–650. Length is fixed before any observation order. -/
def incrementsGlobalPrimaryFiniteU
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (ν : Λ) (β : Β) (t : Ep) : (EuclideanSpace ℝ (Fin (m + 1))) → (Fin (m + 1) → ℂ) :=
  incrementsActualModeSum
    (incrementsModeComplexFirstOrderA (F t) (hF t) (g.inverse ν β t))
    (incrementsModeComplexFirstOrderB (F t) (hF t) (g.inverse ν β t))
    ((tau : ℂ) / Complex.I) length
    (fun x ↦ incrementsGlobalPrimarySource F hF g input tau ν β (t, x))

/-- Canonical fullZ of a fixed real/imaginary channel of SAME finite u.
Only the real channel has the original free datum. Source:617–650. -/
def incrementsGlobalPrimaryLocalZ
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (realChannel : Bool) (ν : Λ) (β : Β) (z : Ep × (EuclideanSpace ℝ (Fin (m + 1)))) :
    (EuclideanSpace ℝ (Fin N)) :=
  let ch := if realChannel then incrementsModeRealPart else incrementsModeImagPart
  incrementsModeFullReconstruction (F z.1) (hF z.1) (g.inverse ν β z.1)
    (fun x ↦ ch (incrementsGlobalPrimaryFiniteU F hF g input length tau ν β z.1 x))
    (fun _ _ _ ↦ 0)
    (fun x ↦ if realChannel then
      incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 x else 0) z.2

/-- SAME supported pullback, with no cutoff multiplied onto its output.
Source: actual relative-W pullback9c522, original645–650. -/
def incrementsGlobalPrimaryExtension
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (realChannel : Bool) (ν : Λ) (β : Β) (z : Ep × M) : (EuclideanSpace ℝ (Fin N)) := by
  classical
  exact if z ∈ (g.chart ν β).source then
    incrementsGlobalPrimaryLocalZ F hF g input length tau realChannel ν β (g.chart ν β z)
    else 0

/-- Group actual subordinate amplitudes by ORIGINAL primary phase before any
coefficient extraction. Source:645–655; same-phase cross terms are retained. -/
def incrementsGlobalPrimaryAmplitude
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (realChannel : Bool) (ν : Λ) (z : Ep × M) : (EuclideanSpace ℝ (Fin N)) :=
  ∑ β, incrementsGlobalPrimaryExtension F hF g input length tau realChannel ν β z

/-- Literal normalized global real primary wave from these SAME fullZ amplitudes.
Source: U1(A), main.tex646–655. No observation-order or supplied U occurs. -/
def incrementsGlobalPrimaryWave
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (z : Ep × M) : (EuclideanSpace ℝ (Fin N)) :=
  ∑ ν, (Real.cos (g.phase ν z / tau) •
      incrementsGlobalPrimaryAmplitude F hF g input length tau true ν z -
    Real.sin (g.phase ν z / tau) •
      incrementsGlobalPrimaryAmplitude F hF g input length tau false ν z)

/-- Actual spatial differential with the SAME target tangent cast as inducedMetric.
Source: original source-only metric differentiation. -/
def incrementsGlobalSpatialDerivative (f : Ep × M → (EuclideanSpace ℝ (Fin N))) (z : Ep × M) :
    TangentSpace I z.2 →L[ℝ] (EuclideanSpace ℝ (Fin N)) :=
  (tangentSpaceCastModel 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) (f z)).toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) (fun x ↦ f (z.1, x)) z.2)

/-- Actual spatial differential of the original given phase, not a parameter
derivative or a supplied covector. Source: main.tex599–650. -/
def incrementsGlobalScalarDerivative (f : Ep × M → ℝ) (z : Ep × M) :
    TangentSpace I z.2 →L[ℝ] ℝ :=
  (tangentSpaceCastModel 𝓘(ℝ, ℝ) (f z)).toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, ℝ) (fun x ↦ f (z.1, x)) z.2)

/-- Real/imaginary coefficient maps dR-dphi*I/tau and dI+dphi*R/tau of SAME
global amplitude. These are native CLMs, not prescribed derivative identities.
Source: original primary first jets, main.tex646–655. -/
def incrementsGlobalPrimaryCoefficient
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (realChannel : Bool) (ν : Λ) (z : Ep × M) :
    TangentSpace I z.2 →L[ℝ] (EuclideanSpace ℝ (Fin N)) :=
  let own := incrementsGlobalPrimaryAmplitude F hF g input length tau realChannel ν
  let other := incrementsGlobalPrimaryAmplitude F hF g input length tau (!realChannel) ν
  let slow := incrementsGlobalSpatialDerivative (I := I) own z
  let fast := (incrementsGlobalScalarDerivative (I := I) (g.phase ν) z).smulRight
    ((tau⁻¹) • other z)
  if realChannel then slow - fast else slow + fast

/-- Native real symmetric mean candidate from the ACTUAL global coefficient maps.
The original zero-germ hypotheses must identify it with the true zero coefficient.
No mean oracle or independent chart matrix is supplied. Source: main.tex651–655. -/
def incrementsGlobalPrimaryMean
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (t : Ep) (x : M) : LinearMap.BilinForm ℝ (TangentSpace I x) :=
  (1 / 2 : ℝ) • ∑ ν, (
    LinearMap.BilinForm.comp (innerₗ (EuclideanSpace ℝ (Fin N)))
      (incrementsGlobalPrimaryCoefficient F hF g input length tau true ν (t, x)).toLinearMap
      (incrementsGlobalPrimaryCoefficient F hF g input length tau true ν (t, x)).toLinearMap +
    LinearMap.BilinForm.comp (innerₗ (EuclideanSpace ℝ (Fin N)))
      (incrementsGlobalPrimaryCoefficient F hF g input length tau false ν (t, x)).toLinearMap
      (incrementsGlobalPrimaryCoefficient F hF g input length tau false ν (t, x)).toLinearMap)

/-- The SAME native tensor T(A)=M(A)-A, not an independent data field or bound.
Source: original main.tex651–667. -/
def incrementsGlobalPrimaryMeanError
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ) :
    (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x) :=
  fun t x ↦ incrementsGlobalPrimaryMean F hF g input length tau t x - input t x

/-- Original observation-chart tangent directions, with no new basis/norm choice.
Source: literal pullback components of the original target tensor. -/
def incrementsGlobalObservationVector
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 1))))
    (y : (EuclideanSpace ℝ (Fin (m + 1))))
    (r : Fin (m + 1)) :
    TangentSpace I (e.symm y) :=
  mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin (m + 1)))) I e.symm y
    ((tangentSpaceCastModel 𝓘(ℝ, (EuclideanSpace ℝ (Fin (m + 1)))) y).symm
      (EuclideanSpace.single r 1))

/-- Actual observed coefficient of the SAME globally pulled-back fullZ pieces.
Source: physical primary first jet before zero extraction, main.tex646–655. -/
def incrementsGlobalObservedCoefficient
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 1))))
    (t : Ep) (y : (EuclideanSpace ℝ (Fin (m + 1)))) :
    Λ → Fin (m + 1) → Fin N → ℂ :=
  fun ν r ↦ incrementsPrimaryDerivativeCoefficient
    (fun x ↦ g.phase ν (t, e.symm x)) tau (fun _ _ ↦ 1)
    (fun β x ↦ incrementsGlobalPrimaryExtension F hF g input length tau true ν β (t, e.symm x))
    (fun β x ↦ incrementsGlobalPrimaryExtension F hF g input length tau false ν β (t, e.symm x))
    y (EuclideanSpace.single r 1)

/-- Canonical leading coefficient from SAME original b, unit normal and phase.
Source: i*sqrt2*b*n*dphi in main.tex646–655. -/
def incrementsGlobalObservedLeading
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 1))))
    (t : Ep) (y : (EuclideanSpace ℝ (Fin (m + 1)))) :
    Λ → Fin (m + 1) → Fin N → ℂ :=
  fun ν ↦ incrementsLeadingCoefficient 1 (incrementsGlobalPrimaryB F g input ν (t, e.symm y))
    (g.normal ν (t, e.symm y))
    (fun r ↦ fderiv ℝ (fun x ↦ g.phase ν (t, e.symm x)) y (EuclideanSpace.single r 1))

/-- Actual transported correction error, including free slow terms. Real correction
is SAME fullZ minus its primitive eta*free datum, not a second reconstructed map.
Source: original main.tex650–661 and accepted generic primary error formula. -/
def incrementsGlobalObservedError
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (length : ℕ) (tau : ℝ)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 1))))
    (t : Ep) (y : (EuclideanSpace ℝ (Fin (m + 1)))) :
    Λ → Fin (m + 1) → Fin N → ℂ :=
  fun ν r ↦ incrementsPrimaryErrorCoefficient 1 tau
    (fun x ↦ incrementsGlobalPrimaryB F g input ν (t, e.symm x))
    (fun x ↦ g.phase ν (t, e.symm x)) (fun x ↦ g.normal ν (t, e.symm x))
    (fun β x ↦ incrementsGlobalPrimaryExtension F hF g input length tau true ν β (t, e.symm x) -
      g.eta ν β (t, e.symm x) • incrementsGlobalPrimaryFree F g input tau ν (t, e.symm x))
    (fun β x ↦ incrementsGlobalPrimaryExtension F hF g input length tau false ν β (t, e.symm x))
    y (EuclideanSpace.single r 1)

/-- TRUE all-label zero-germ coefficient of the SAME observed physical wave.
Source: original coefficient extraction651–655; never spatial averaging. -/
def incrementsGlobalObservedZero
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau delta : ℝ)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 1))))
    (t : Ep) (y : (EuclideanSpace ℝ (Fin (m + 1))))
    (r s : Fin (m + 1)) : ℂ :=
  ∑ ν, ∑ μ, incrementsFourPhaseZeroGermPair
    (fun ν x ↦ g.phase ν (t, e.symm x) / tau)
    (delta • incrementsGlobalObservedCoefficient F hF g input length tau e t y) y ν μ r s

/-- Stage2 ONLY: bind the SAME actual global fullZ primary wave, its leading
coefficient and native mean tensor to the TRUE REAL all-original-label mean.

Source: original main.tex641–667. The explicit family is an INTERNAL produced
chart/source family, not a new original lemma input. The support supplier is
the relative support of the PRIMITIVE combined cutoff eta*chi, contained in
the corresponding actual chart source. There is no hypothesis on desired Z/U
support, source smoothness, a coefficient/leading identity, or any mean bound.
Geometry smoothness refers to actual canonical fields and is supplied by the
sole W2 geometry producer. Original primitives are smooth only on their actual
primary opens inside W; outside extensions and inactive labels are unrestricted.
The helper's per-p spatial hF can use the original slices on valid parameters
and constant-zero slices elsewhere; no joint extension at the parameter boundary
is required. W itself is any original open validity neighborhood, not assumed
to be a whole parameter product. Its construction/finite validity is separate.

Natural-language proof plan for the single named hole: on each actual joint
target use the original inverse identity and primitive smooth fields to obtain
the actual eta*chi*sqrt(ell(A))*normal free field. Positive square roots are
needed only on the original cutoff support; reuse supported-amplitude smooth
glue, with zero germs off that support. The accepted actual source split gives
joint source smoothness from actual second-form rows and this free field, and
its support from the combined cutoff; neither is an extra hypothesis. Native
chart locality converts that primitive support supplier to the hypotheses of
the accepted relative fullZ pullback theorem. Thus the literal extensions are
smooth on W, retain original primary supports and agree with SAME local fullZ.
The primary exponential wave is smooth on its active primary open; off the
relative support it has a zero germ, irrespective of the outside phase values.
Regroup pieces by ORIGINAL phase before differentiating or extracting zero.
In an actual observation chart the generic primary first-jet theorem gives
the actual coefficient. Apply the existing leading identity only where the
primary cutoff is active; the ordinary eta sum is a neighborhood germ there.
Use zero germs on inactive labels, without extra partition/Good/reserve input.
The existing generic phase-germ theorem then identifies the ENTIRE zero part
with the opposite-primary contribution. Unit normals and the original positive
decomposition remove its leading term, and native finite sum/REAL projection
gives the all-label Unit remainder, including same-phase subordinate cross terms.
Native manifold chain rules through the SAME observation inverse identify that
coefficient with CR+iCI. The existing real/complex opposite-coefficient algebra
identifies its real part with the defined native M on all ordered directions;
T=M-A follows. Native inner symmetry gives IsSymm. Finally real homogeneity of
the finite expression gives delta first jets and delta-squared mean, including
delta zero. No new quadratic estimate, generic extension theory, norm, reserve,
U2 or observation-dependent algorithm is introduced.

This is NOT a proof delivery, full-profile lock or original-target acceptance.
Empty primary/piece sets, zero parameter dimension, m=0, and delta=0 remain
covered whenever the displayed original decomposition and active partition hold. -/
theorem increments_global_primary_mean_binding

    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (q : ℕ) (_hq : 1 ≤ q) (tau : ℝ) (_htau : 0 < tau)
    (W : Set (Ep × M)) (_hW : IsOpen W) (primary : Λ → Set (Ep × M))
    (_hPrimary : ∀ ν, IsOpen (primary ν))
    (_hPrimarySupport : ∀ ν, incrementsGlobalRelativeSupport W (g.cutoff ν) ⊆ primary ν)
    (_hSourceW : ∀ ν β, (g.chart ν β).source ⊆ W ∩ primary ν)
    (_hChart : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) ∞
      (g.chart ν β) (g.chart ν β).source)
    (_hChartInv : ∀ ν β, ContMDiffOn 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) 
      ((𝓘(ℝ, Ep)).prod I) ∞ (g.chart ν β).symm (g.chart ν β).target)
    (_hInverse : ∀ ν β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1, g.inverse ν β z.1 z.2))
    (_hCombinedSupport : ∀ ν β,
      incrementsGlobalRelativeSupport W (fun z ↦ g.eta ν β z * g.cutoff ν z) ⊆
        (g.chart ν β).source)
    (_hPhase : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (g.phase ν) (W ∩ primary ν))
    (_hCut : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (g.cutoff ν) (W ∩ primary ν))
    (_hNormal : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞
      (g.normal ν) (W ∩ primary ν))
    (_hArgument : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ g.linearArgument ν z.1 z.2 (input z.1 z.2)) (W ∩ primary ν))
    (_hEta : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ (g.eta ν β) W)
    (_hPositive : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      0 < g.linearArgument ν z.1 z.2 (input z.1 z.2))
    (_hUnit : ∀ ν z, z ∈ W → g.cutoff ν z ≠ 0 → ‖g.normal ν z‖ = 1)
    (_hPartition : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      ∀ᶠ w in 𝓝 z, ∑ β, g.eta ν β w = 1)
    (_hSymm : ∀ z ∈ W, (input z.1 z.2).IsSymm)
    (_hDecomp : ∀ z ∈ W, ∀ v w : TangentSpace I z.2,
      ∑ ν, (incrementsGlobalPrimaryB F g input ν z) ^ 2 *
        incrementsGlobalScalarDerivative (I := I) (g.phase ν) z v *
        incrementsGlobalScalarDerivative (I := I) (g.phase ν) z w = input z.1 z.2 v w)
    (_hDouble : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      incrementsGlobalScalarDerivative (I := I) (fun w ↦ g.phase ν w + g.phase ν w) z ≠ 0)
    (_hInteraction : ∀ ν μ, ν ≠ μ → ∀ z,
      z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      z ∈ incrementsGlobalRelativeSupport W (g.cutoff μ) →
      incrementsGlobalScalarDerivative (I := I) (fun w ↦ g.phase ν w + g.phase μ w) z ≠ 0 ∧
      incrementsGlobalScalarDerivative (I := I) (fun w ↦ g.phase ν w - g.phase μ w) z ≠ 0)
    (_hG : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (_hJ : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (_hT0 : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (_hA : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target)
    (_hB : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target)
    (_hSecond : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 i :
        (EuclideanSpace ℝ (Fin N))))
      (g.chart ν β).target) :
    ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞
      (incrementsGlobalPrimaryWave F hF g input (q + 2) tau) W ∧
    (∀ z ∈ W, (incrementsGlobalPrimaryMeanError F hF g input (q + 2) tau z.1 z.2).IsSymm) ∧
    ∀ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 1))))
      (_he : ContMDiffOn I 𝓘(ℝ, (EuclideanSpace ℝ (Fin (m + 1)))) ∞ e e.source)
      (_heInv : ContMDiffOn 𝓘(ℝ, (EuclideanSpace ℝ (Fin (m + 1)))) I ∞ e.symm e.target)
      (t : Ep) (y : (EuclideanSpace ℝ (Fin (m + 1)))), y ∈ e.target → (t, e.symm y) ∈ W →
      let coeff := incrementsGlobalObservedCoefficient F hF g input (q + 2) tau e t y
      let lead := incrementsGlobalObservedLeading F g input e t y
      let err := incrementsGlobalObservedError F hF g input (q + 2) tau e t y
      let zero := incrementsGlobalObservedZero F hF g input (q + 2) tau 1 e t y
      let v := incrementsGlobalObservationVector (I := I) e y
      coeff = lead + err ∧
      (∀ (delta : ℝ) r, fderiv ℝ (fun x ↦ delta •
        incrementsGlobalPrimaryWave F hF g input (q + 2) tau (t, e.symm x)) y
          (EuclideanSpace.single r 1) =
        delta • incrementsGroupedRealDerivative (fun ν ↦ g.phase ν (t, e.symm y) / tau)
          coeff r) ∧
      (∀ r s, zero r s - (input t (e.symm y) (v r) (v s) : ℂ) =
        incrementsMeanRemainder lead err r s) ∧
      (∀ r s, incrementsMeanRealCoordinate
          (zero r s - (input t (e.symm y) (v r) (v s) : ℂ)) =
        (fun _ : Fin 1 ↦
          incrementsGlobalPrimaryMeanError F hF g input (q + 2) tau t (e.symm y) (v r) (v s)) ∧
        incrementsMeanRealCoordinate
          (zero r s - (input t (e.symm y) (v r) (v s) : ℂ)) =
        ∑ ν, incrementsMeanRealCoordinate (incrementsMeanRemainder
          (fun _ : Unit ↦ lead ν) (fun _ : Unit ↦ err ν) r s)) ∧
      (∀ (delta : ℝ) r s, incrementsMeanRealCoordinate
          (incrementsGlobalObservedZero F hF g input (q + 2) tau delta e t y r s) =
        (fun _ : Fin 1 ↦ delta ^ 2 *
          (input t (e.symm y) (v r) (v s) +
            incrementsGlobalPrimaryMeanError F hF g input (q + 2) tau
              t (e.symm y) (v r) (v s)))) := by
  classical
  have hRelative (f : Ep × M → ℝ) :
      incrementsGlobalRelativeSupport W f = W ∩ tsupport f := by
    unfold incrementsGlobalRelativeSupport
    change Subtype.val '' closure (Subtype.val ⁻¹' Function.support f : Set W) =
      W ∩ closure (Function.support f)
    rw [← _hW.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (Function.support f), Set.image_preimage_eq_inter_range]
    simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, Set.inter_comm]
  have hBfree (ν : Λ) :
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
        (incrementsGlobalPrimaryB F g input ν) W := by
    intro z hzW
    by_cases hz : z ∈ tsupport (g.cutoff ν)
    · have hzS : z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) := by
        rw [hRelative]
        exact ⟨hzW, hz⟩
      have hloc := (_hW.inter (_hPrimary ν)).mem_nhds
        ⟨hzW, _hPrimarySupport ν hzS⟩
      have hsqrt := (Real.contDiffAt_sqrt (_hPositive ν z hzS).ne').contMDiffAt.comp z
        ((_hArgument ν).contMDiffAt hloc)
      exact (((_hCut ν).contMDiffAt hloc).mul hsqrt).contMDiffWithinAt
    · apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (g.cutoff ν)).isOpen_compl.mem_nhds hz] with w hw
      simp [incrementsGlobalPrimaryB, image_eq_zero_of_notMem_tsupport hw]
  have hFree (ν : Λ) :
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (incrementsGlobalPrimaryFree F g input tau ν) W := by
    intro z hzW
    by_cases hz : z ∈ tsupport (g.cutoff ν)
    · have hzS : z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) := by
        rw [hRelative]
        exact ⟨hzW, hz⟩
      have hloc := (_hW.inter (_hPrimary ν)).mem_nhds
        ⟨hzW, _hPrimarySupport ν hzS⟩
      exact ((contMDiffAt_const (c := Real.sqrt 2 * tau)).mul
        ((hBfree ν).contMDiffAt (_hW.mem_nhds hzW))).smul
          ((_hNormal ν).contMDiffAt hloc) |>.contMDiffWithinAt
    · apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin N)))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (g.cutoff ν)).isOpen_compl.mem_nhds hz] with w hw
      simp [incrementsGlobalPrimaryFree, incrementsGlobalPrimaryB,
        image_eq_zero_of_notMem_tsupport hw]
  have hLocalFree (ν : Λ) (β : Β) : ContDiffOn ℝ ∞
      (fun z : Ep × EuclideanSpace ℝ (Fin (m + 1)) ↦
        (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 z.2 :
          EuclideanSpace ℝ (Fin N))) (g.chart ν β).target := by
    have h := ((_hEta ν β).smul (hFree ν)).comp (_hChartInv ν β)
      (fun z hz ↦ (_hSourceW ν β ((g.chart ν β).map_target hz)).1)
    apply h.contDiffOn.congr
    intro z hz
    simp [incrementsGlobalPrimaryLocalFree, hz, _hInverse ν β z hz,
      incrementsGlobalPrimaryFree, smul_smul]
  have hSource (ν : Λ) (β : Β) : ContDiffOn ℝ ∞
      (incrementsGlobalPrimarySource F hF g input tau ν β) (g.chart ν β).target := by
    have hs := incrementsModeSource_joint_contDiffOn F hF (g.inverse ν β)
      (fun _ _ _ ↦ 0) (incrementsGlobalPrimaryLocalFree F g input tau ν β)
      (g.chart ν β).target (_hSecond ν β) (_hJ ν β) contDiffOn_const (hLocalFree ν β)
    exact incrementsModeComplexInclude.contDiff.comp_contDiffOn hs
  have hZeroSource (ν : Λ) (β : Β) (z : Ep × EuclideanSpace ℝ (Fin (m + 1))) :
      incrementsModeSource (F z.1) (hF z.1) (g.inverse ν β z.1)
        (fun _ _ _ ↦ 0) (fun _ ↦ 0) z.2 = 0 := by
    simpa only [zero_smul] using incrementsModeSource_zero_smul (F z.1) (hF z.1)
      (g.inverse ν β z.1) (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1) z.2 0
  have hSourceOfZero (ν : Λ) (β : Β)
      (z : Ep × EuclideanSpace ℝ (Fin (m + 1)))
      (hz : (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 z.2 :
        EuclideanSpace ℝ (Fin N)) = 0) :
      incrementsGlobalPrimarySource F hF g input tau ν β z = 0 := by
    unfold incrementsGlobalPrimarySource
    rw [incrementsModeSource_eq_zeroFree_add, hZeroSource, hz, map_zero,
      smul_zero, add_zero, map_zero]
  have hLocalFreeZero (ν : Λ) (β : Β)
      (z : Ep × EuclideanSpace ℝ (Fin (m + 1))) (hz : z ∈ (g.chart ν β).target)
      (hn : (g.chart ν β).symm z ∉
        incrementsGlobalRelativeSupport W (fun w ↦ g.eta ν β w * g.cutoff ν w)) :
      (fun w : Ep × EuclideanSpace ℝ (Fin (m + 1)) ↦
        (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 :
          EuclideanSpace ℝ (Fin N))) =ᶠ[𝓝 z] 0 := by
    have hnT : (g.chart ν β).symm z ∉
        tsupport (fun w ↦ g.eta ν β w * g.cutoff ν w) := by
      intro h
      apply hn
      rw [hRelative]
      exact ⟨(_hSourceW ν β ((g.chart ν β).map_target hz)).1, h⟩
    have hc := (g.chart ν β).symm.continuousOn.continuousAt
      ((g.chart ν β).open_target.mem_nhds hz)
    filter_upwards [(g.chart ν β).open_target.mem_nhds hz,
      hc.eventually ((isClosed_tsupport
        (fun w ↦ g.eta ν β w * g.cutoff ν w)).isOpen_compl.mem_nhds hnT)] with w hw hw0
    have hmul : g.eta ν β (w.1, g.inverse ν β w.1 w.2) *
        g.cutoff ν (w.1, g.inverse ν β w.1 w.2) = 0 := by
      simpa only [_hInverse ν β w hw] using image_eq_zero_of_notMem_tsupport hw0
    rcases mul_eq_zero.mp hmul with he | he
    · simp [incrementsGlobalPrimaryLocalFree, hw, he]
    · simp [incrementsGlobalPrimaryLocalFree, hw, incrementsGlobalPrimaryB, he]
  have hPiece (ν : Λ) (β : Β) :
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (incrementsGlobalPrimaryExtension F hF g input (q + 2) tau true ν β) W ∧
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (incrementsGlobalPrimaryExtension F hF g input (q + 2) tau false ν β) W ∧
      tsupport (fun w : W ↦ incrementsGlobalPrimaryExtension
        F hF g input (q + 2) tau true ν β w) ⊆
        Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν) ∧
      tsupport (fun w : W ↦ incrementsGlobalPrimaryExtension
        F hF g input (q + 2) tau false ν β w) ⊆
        Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν) := by
    let K := incrementsGlobalRelativeSupport W (fun w ↦ g.eta ν β w * g.cutoff ν w)
    have hK : IsClosed (Subtype.val ⁻¹' K : Set W) := by
      dsimp only [K]
      rw [hRelative]
      simpa only [Set.preimage_inter, Subtype.coe_preimage_self, Set.univ_inter] using
        (isClosed_tsupport (fun w ↦ g.eta ν β w * g.cutoff ν w)).preimage
          continuous_subtype_val
    have hsub : K ⊆ incrementsGlobalRelativeSupport W (g.cutoff ν) := by
      rw [show K = W ∩ tsupport (fun w ↦ g.eta ν β w * g.cutoff ν w) from hRelative _,
        hRelative]
      exact Set.inter_subset_inter_right W tsupport_mul_subset_right
    have hs : (fun z : Ep × EuclideanSpace ℝ (Fin (m + 1)) ↦
        incrementsGlobalPrimarySource F hF g input tau ν β z + Complex.I •
          incrementsModeComplexInclude
            (incrementsModeSource (F z.1) (hF z.1) (g.inverse ν β z.1)
              (fun _ _ _ ↦ 0) (fun _ ↦ 0) z.2)) =
        incrementsGlobalPrimarySource F hF g input tau ν β := by
      funext z
      rw [hZeroSource, map_zero, smul_zero, add_zero]
    have hout := incrementsModeFullReconstruction_supported_chart_pullback F hF
      (g.inverse ν β) (fun _ _ _ ↦ 0) (fun _ _ _ ↦ 0)
      (incrementsGlobalPrimaryLocalFree F g input tau ν β) (fun _ _ ↦ 0)
      (q + 2) tau (g.chart ν β) W _hW (fun z hz ↦ (_hSourceW ν β hz).1)
      K hK (_hCombinedSupport ν β) (_hChart ν β) (_hInverse ν β)
      (_hG ν β) (_hJ ν β) (_hT0 ν β) (_hA ν β) (_hB ν β)
      contDiffOn_const contDiffOn_const (hLocalFree ν β) contDiffOn_const
    unfold incrementsGlobalPrimarySource at hs
    rw [hs] at hout
    have hloc (z : Ep × EuclideanSpace ℝ (Fin (m + 1)))
        (hz : z ∈ (g.chart ν β).target) (hn : (g.chart ν β).symm z ∉ K) :
        z ∉ tsupport (incrementsGlobalPrimarySource F hF g input tau ν β) ∧
        z ∉ tsupport (fun w : Ep × EuclideanSpace ℝ (Fin (m + 1)) ↦
          (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 :
            EuclideanSpace ℝ (Fin N))) := by
      have hv := hLocalFreeZero ν β z hz hn
      exact ⟨notMem_tsupport_iff_eventuallyEq.mpr (by
        filter_upwards [hv] with w hw
        exact hSourceOfZero ν β w hw), notMem_tsupport_iff_eventuallyEq.mpr hv⟩
    have hi := hout (hSource ν β) (by
      intro z hz hin
      by_contra hn
      have ht := hloc z hz hn
      have hEmpty : tsupport (fun _ : Ep × EuclideanSpace ℝ (Fin (m + 1)) ↦
          fun _ : Fin (m + 1) ↦ fun _ : Fin (m + 1) ↦ (0 : ℝ)) = ∅ :=
        tsupport_fun_zero
      rw [hEmpty] at hin
      simp only [Submodule.coe_zero, tsupport_fun_zero, Set.mem_union,
        Set.mem_empty_iff_false, false_or, or_false] at hin
      exact hin.elim ht.1 ht.2)
    refine ⟨hi.1, hi.2.1, hi.2.2.1.trans (Set.preimage_mono hsub),
      hi.2.2.2.1.trans (Set.preimage_mono hsub)⟩
  have hRestricted (f : Ep × M → EuclideanSpace ℝ (Fin N)) :
      tsupport (fun w : W ↦ f w) = Subtype.val ⁻¹' tsupport f := by
    change closure (Subtype.val ⁻¹' Function.support f : Set W) =
      Subtype.val ⁻¹' closure (Function.support f)
    exact (_hW.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (Function.support f)).symm
  have hPieceZero (ch : Bool) (ν : Λ) (β : Β) (z : Ep × M) (hzW : z ∈ W)
      (hn : z ∉ incrementsGlobalRelativeSupport W (g.cutoff ν)) :
      incrementsGlobalPrimaryExtension F hF g input (q + 2) tau ch ν β =ᶠ[𝓝 z] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hz
    have hres : (⟨z, hzW⟩ : W) ∈ tsupport (fun w : W ↦
        incrementsGlobalPrimaryExtension F hF g input (q + 2) tau ch ν β w) := by
      rw [hRestricted]
      exact hz
    cases ch
    · exact hn ((hPiece ν β).2.2.2 hres)
    · exact hn ((hPiece ν β).2.2.1 hres)
  have hAmplitude (ch : Bool) (ν : Λ) :
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (incrementsGlobalPrimaryAmplitude F hF g input (q + 2) tau ch ν) W := by
    intro z hz
    apply ContMDiffWithinAt.sum
    intro β _
    cases ch
    · exact (hPiece ν β).2.1 z hz
    · exact (hPiece ν β).1 z hz
  have hAmplitudeZero (ch : Bool) (ν : Λ) (z : Ep × M) (hzW : z ∈ W)
      (hn : z ∉ incrementsGlobalRelativeSupport W (g.cutoff ν)) :
      incrementsGlobalPrimaryAmplitude F hF g input (q + 2) tau ch ν =ᶠ[𝓝 z] 0 := by
    filter_upwards [eventually_all.mpr (fun β ↦ hPieceZero ch ν β z hzW hn)] with w hw
    simp [incrementsGlobalPrimaryAmplitude, hw]
  have hWave : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (incrementsGlobalPrimaryWave F hF g input (q + 2) tau) W := by
    intro z hzW
    apply ContMDiffWithinAt.sum
    intro ν _
    apply ContMDiffAt.contMDiffWithinAt
    by_cases hz : z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)
    · have hp := ((_hPhase ν).contMDiffAt
        ((_hW.inter (_hPrimary ν)).mem_nhds ⟨hzW, _hPrimarySupport ν hz⟩)).div_const
        (c := tau)
      exact ((Real.contDiff_cos.contDiffAt.comp_contMDiffAt hp).smul
        ((hAmplitude true ν).contMDiffAt (_hW.mem_nhds hzW))).sub
        ((Real.contDiff_sin.contDiffAt.comp_contMDiffAt hp).smul
          ((hAmplitude false ν).contMDiffAt (_hW.mem_nhds hzW)))
    · apply (contMDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin N)))).congr_of_eventuallyEq
      filter_upwards [hAmplitudeZero true ν z hzW hz,
        hAmplitudeZero false ν z hzW hz] with w hR hI
      simp only [hR, hI, Pi.zero_apply, smul_zero, sub_zero]
  have hSym : ∀ z ∈ W,
      (incrementsGlobalPrimaryMeanError F hF g input (q + 2) tau z.1 z.2).IsSymm := by
    intro z hz
    apply LinearMap.BilinForm.IsSymm.sub _ (_hSymm z hz)
    constructor
    intro v w
    simp only [incrementsGlobalPrimaryMean, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.add_apply, LinearMap.BilinForm.comp_apply,
      ContinuousLinearMap.coe_coe, innerₗ_apply_apply, smul_eq_mul]
    simp_rw [real_inner_comm]
  refine ⟨hWave, hSym, ?_⟩
  intro e he heInv t y hy hzW
  have hobsCont : ContinuousAt
      (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ (t, e.symm x)) y :=
    continuousAt_const.prodMk (e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hy))
  have hObserve {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (f : Ep × M → Y)
      (hf : ContMDiffAt ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, Y) ∞ f (t, e.symm y)) :
      ContDiffAt ℝ ∞ (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ f (t, e.symm x)) y := by
    exact (hf.comp y ((contMDiffAt_const (c := t)).prodMk
      (heInv.contMDiffAt (e.open_target.mem_nhds hy)))).contDiffAt
  have hObserveJet {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (f : Ep × M → Y)
      (hf : ContMDiffAt ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, Y) ∞ f (t, e.symm y))
      (v : EuclideanSpace ℝ (Fin (m + 1))) :
      fderiv ℝ (fun x ↦ f (t, e.symm x)) y v =
        (tangentSpaceCastModel 𝓘(ℝ, Y) (f (t, e.symm y)))
          (mfderiv I 𝓘(ℝ, Y) (fun x ↦ f (t, x)) (e.symm y)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I e.symm y
              ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) y).symm v))) := by
    have hslice := (hf.comp (e.symm y)
      ((contMDiffAt_const (c := t)).prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
    have hchain := mfderiv_comp y hslice
      ((heInv.contMDiffAt (e.open_target.mem_nhds hy)).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hchain
    exact congrArg (fun L ↦ L v) hchain
  have hScalarNonzero (f : Ep × M → ℝ)
      (hf : ContMDiffAt ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ f (t, e.symm y))
      (hn : incrementsGlobalScalarDerivative (I := I) f (t, e.symm y) ≠ 0) :
      fderiv ℝ (fun x ↦ f (t, e.symm x)) y ≠ 0 := by
    intro hz
    apply hn
    have hout : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) 𝓘(ℝ, ℝ)
        (fun x ↦ f (t, e.symm x)) (e (e.symm y)) := by
      rw [e.right_inv hy]
      exact ((hObserve f hf).differentiableAt (by simp)).mdifferentiableAt
    have hin := (he.contMDiffAt (e.open_source.mem_nhds (e.map_target hy))).mdifferentiableAt
      (by simp)
    have hchain := mfderiv_comp (e.symm y) hout hin
    have heq : (fun x ↦ f (t, x)) =ᶠ[𝓝 (e.symm y)]
        (fun x ↦ f (t, e.symm (e x))) := by
      filter_upwards [e.open_source.mem_nhds (e.map_target hy)] with x hx
      rw [e.left_inv hx]
    have hh := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))
    rw [mfderiv_eq_fderiv, e.right_inv hy, hz] at hchain
    dsimp only [Function.comp_def] at hchain
    rw [hchain] at hh
    unfold incrementsGlobalScalarDerivative
    rw [hh]
    ext v
    rfl
  let phi := fun ν (x : EuclideanSpace ℝ (Fin (m + 1))) ↦ g.phase ν (t, e.symm x)
  let b := fun ν (x : EuclideanSpace ℝ (Fin (m + 1))) ↦
    incrementsGlobalPrimaryB F g input ν (t, e.symm x)
  let nf := fun ν (x : EuclideanSpace ℝ (Fin (m + 1))) ↦ g.normal ν (t, e.symm x)
  let eta := fun ν β (x : EuclideanSpace ℝ (Fin (m + 1))) ↦ g.eta ν β (t, e.symm x)
  let R := fun ν β (x : EuclideanSpace ℝ (Fin (m + 1))) ↦
    incrementsGlobalPrimaryExtension F hF g input (q + 2) tau true ν β (t, e.symm x)
  let Q := fun ν β (x : EuclideanSpace ℝ (Fin (m + 1))) ↦
    incrementsGlobalPrimaryExtension F hF g input (q + 2) tau false ν β (t, e.symm x)
  let P := fun ν β (x : EuclideanSpace ℝ (Fin (m + 1))) ↦ R ν β x -
    eta ν β x • incrementsGlobalPrimaryFree F g input tau ν (t, e.symm x)
  have hb (ν : Λ) : DifferentiableAt ℝ (b ν) y :=
    (hObserve (incrementsGlobalPrimaryB F g input ν) ((hBfree ν).contMDiffAt (_hW.mem_nhds
      hzW))).differentiableAt (by simp)
  have hEta (ν : Λ) (β : Β) : DifferentiableAt ℝ (eta ν β) y :=
    (hObserve (g.eta ν β) ((_hEta ν β).contMDiffAt (_hW.mem_nhds hzW))).differentiableAt (by simp)
  have hR (ν : Λ) (β : Β) : DifferentiableAt ℝ (R ν β) y :=
    (hObserve (incrementsGlobalPrimaryExtension F hF g input (q + 2) tau true ν β)
      ((hPiece ν β).1.contMDiffAt (_hW.mem_nhds hzW))).differentiableAt (by simp)
  have hQ (ν : Λ) (β : Β) : DifferentiableAt ℝ (Q ν β) y :=
    (hObserve (incrementsGlobalPrimaryExtension F hF g input (q + 2) tau false ν β)
      ((hPiece ν β).2.1.contMDiffAt (_hW.mem_nhds hzW))).differentiableAt (by simp)
  have hP (ν : Λ) (β : Β) : DifferentiableAt ℝ (P ν β) y :=
    (hR ν β).sub ((hEta ν β).smul
      ((hObserve (incrementsGlobalPrimaryFree F g input tau ν) ((hFree ν).contMDiffAt
        (_hW.mem_nhds hzW))).differentiableAt (by simp)))
  have hPF (ν : Λ) : (fun β x ↦ eta ν β x •
      incrementsPrimaryFreeAmplitude 1 tau (b ν) (nf ν) x + P ν β x) = R ν := by
    funext β x
    simp only [P, incrementsPrimaryFreeAmplitude, mul_one, b, nf,
      incrementsGlobalPrimaryFree]
    abel
  have hCoeff : incrementsGlobalObservedCoefficient F hF g input (q + 2) tau e t y =
      incrementsGlobalObservedLeading F g input e t y +
        incrementsGlobalObservedError F hF g input (q + 2) tau e t y := by
    funext ν r co
    by_cases hz : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)
    · have hn : DifferentiableAt ℝ (nf ν) y :=
        (hObserve (g.normal ν) ((_hNormal ν).contMDiffAt
          ((_hW.inter (_hPrimary ν)).mem_nhds
            ⟨hzW, _hPrimarySupport ν hz⟩))).differentiableAt (by simp)
      have hp := increments_primary_coefficient_leading 1 tau _htau.ne'
        (b ν) (phi ν) (nf ν) (eta ν) (P ν) (Q ν) y
        (EuclideanSpace.single r 1) co (hb ν) hn (hEta ν) (hP ν)
        (hobsCont.eventually (_hPartition ν (t, e.symm y) hz))
      rw [hPF] at hp
      exact hp
    · have hzcut : (t, e.symm y) ∉ tsupport (g.cutoff ν) := by
        intro h
        apply hz
        rw [hRelative]
        exact ⟨hzW, h⟩
      have hbZero : b ν =ᶠ[𝓝 y] 0 := by
        have hn : incrementsGlobalPrimaryB F g input ν =ᶠ[𝓝 (t, e.symm y)] 0 := by
          filter_upwards [(isClosed_tsupport (g.cutoff ν)).isOpen_compl.mem_nhds hzcut]
            with w hw
          simp [incrementsGlobalPrimaryB, image_eq_zero_of_notMem_tsupport hw]
        exact hn.comp_tendsto hobsCont
      have heq (β : Β) : R ν β =ᶠ[𝓝 y] P ν β := by
        filter_upwards [hbZero] with x hx
        change R ν β x = R ν β x - eta ν β x •
          incrementsGlobalPrimaryFree F g input tau ν (t, e.symm x)
        change R ν β x = R ν β x - eta ν β x •
          ((Real.sqrt 2 * tau * b ν x) • nf ν x)
        simp [hx]
      have hD : incrementsGlobalObservedCoefficient F hF g input (q + 2) tau e t y ν r co =
          incrementsPrimaryDerivativeCoefficient (phi ν) tau (fun _ _ ↦ 1)
            (P ν) (Q ν) y (EuclideanSpace.single r 1) co := by
        change incrementsPrimaryDerivativeCoefficient (phi ν) tau (fun _ _ ↦ 1)
          (R ν) (Q ν) y (EuclideanSpace.single r 1) co = _
        unfold incrementsPrimaryDerivativeCoefficient
        simp only [(heq _).eq_of_nhds, (heq _).fderiv_eq (𝕜 := ℝ)]
      change incrementsGlobalObservedCoefficient F hF g input (q + 2) tau e t y ν r co =
        incrementsLeadingCoefficient 1 (b ν y) (nf ν y)
          (fun r ↦ fderiv ℝ (phi ν) y (EuclideanSpace.single r 1)) r co +
        incrementsPrimaryErrorCoefficient 1 tau (b ν) (phi ν) (nf ν)
          (P ν) (Q ν) y (EuclideanSpace.single r 1) co
      rw [hD]
      simp [incrementsLeadingCoefficient, incrementsPrimaryErrorCoefficient,
        hbZero.eq_of_nhds, hbZero.fderiv_eq (𝕜 := ℝ)]
  let coeff := incrementsGlobalObservedCoefficient F hF g input (q + 2) tau e t y
  let lead := incrementsGlobalObservedLeading F g input e t y
  let err := incrementsGlobalObservedError F hF g input (q + 2) tau e t y
  let v := incrementsGlobalObservationVector (I := I) e y
  have hPhaseAt (ν : Λ)
      (hz : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)) :
      ContMDiffAt ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ (g.phase ν) (t, e.symm y) :=
    (_hPhase ν).contMDiffAt ((_hW.inter (_hPrimary ν)).mem_nhds
      ⟨hzW, _hPrimarySupport ν hz⟩)
  have hInactive (ν : Λ)
      (hn : (t, e.symm y) ∉ incrementsGlobalRelativeSupport W (g.cutoff ν)) :
      coeff ν = 0 := by
    have hRzero (β : Β) : R ν β =ᶠ[𝓝 y] 0 :=
      (hPieceZero true ν β (t, e.symm y) hzW hn).comp_tendsto hobsCont
    have hQzero (β : Β) : Q ν β =ᶠ[𝓝 y] 0 :=
      (hPieceZero false ν β (t, e.symm y) hzW hn).comp_tendsto hobsCont
    have hRv (β : Β) : R ν β y = 0 := (hRzero β).eq_of_nhds
    have hQv (β : Β) : Q ν β y = 0 := (hQzero β).eq_of_nhds
    have hRd (β : Β) : fderiv ℝ (R ν β) y = 0 := by
      simpa using (hRzero β).fderiv_eq (𝕜 := ℝ)
    have hQd (β : Β) : fderiv ℝ (Q ν β) y = 0 := by
      simpa using (hQzero β).fderiv_eq (𝕜 := ℝ)
    funext r co
    change incrementsPrimaryDerivativeCoefficient (phi ν) tau (fun _ _ ↦ 1)
      (R ν) (Q ν) y (EuclideanSpace.single r 1) co = 0
    simp [incrementsPrimaryDerivativeCoefficient, hRv, hQv, hRd, hQd]
  have hDoubleObs (ν : Λ)
      (hz : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)) :
      fderiv ℝ (fun x ↦ phi ν x + phi ν x) y ≠ 0 :=
    hScalarNonzero (fun z ↦ g.phase ν z + g.phase ν z)
      ((hPhaseAt ν hz).add (hPhaseAt ν hz)) (_hDouble ν (t, e.symm y) hz)
  have hInteractionObs (ν μ : Λ) (hne : ν ≠ μ)
      (hν : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν))
      (hμ : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff μ)) :
      fderiv ℝ (fun x ↦ phi ν x + phi μ x) y ≠ 0 ∧
      fderiv ℝ (fun x ↦ phi ν x - phi μ x) y ≠ 0 :=
    ⟨hScalarNonzero (fun z ↦ g.phase ν z + g.phase μ z)
      ((hPhaseAt ν hν).add (hPhaseAt μ hμ))
      (_hInteraction ν μ hne (t, e.symm y) hν hμ).1,
     hScalarNonzero (fun z ↦ g.phase ν z - g.phase μ z)
      ((hPhaseAt ν hν).sub (hPhaseAt μ hμ))
      (_hInteraction ν μ hne (t, e.symm y) hν hμ).2⟩
  have hZero (r s : Fin (m + 1)) :
      incrementsGlobalObservedZero F hF g input (q + 2) tau 1 e t y r s =
        incrementsOppositePrimaryContribution coeff r s := by
    unfold incrementsGlobalObservedZero
    simp only [one_smul]
    change (∑ ν, ∑ μ, incrementsFourPhaseZeroGermPair
      (fun ν x ↦ phi ν x / tau) coeff y ν μ r s) = _
    simp_rw [increments_four_phase_zero_germ_pair_div phi tau _htau.ne']
    exact increments_four_phase_zero_germ_eq_opposite phi coeff
      (fun ν ↦ {x | (t, e.symm x) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)}) y
      (fun ν hn r ↦ congrFun (hInactive ν hn) r) hDoubleObs hInteractionObs r s
  have hLeading (r s : Fin (m + 1)) :
      incrementsOppositePrimaryContribution lead r s =
        (input t (e.symm y) (v r) (v s) : ℂ) := by
    have hterm (ν : Λ) : (1 / 4 : ℂ) *
        ((lead ν r ⬝ᵥ (fun co ↦ conj (lead ν s co))) +
          ((fun co ↦ conj (lead ν r co)) ⬝ᵥ lead ν s)) =
        ((b ν y) ^ 2 *
          incrementsGlobalScalarDerivative (I := I) (g.phase ν) (t, e.symm y) (v r) *
          incrementsGlobalScalarDerivative (I := I) (g.phase ν) (t, e.symm y) (v s) : ℝ) := by
      by_cases hz : g.cutoff ν (t, e.symm y) = 0
      · simp [lead, incrementsGlobalObservedLeading, incrementsLeadingCoefficient, b,
          incrementsGlobalPrimaryB, hz, dotProduct]
      · have hzS : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) := by
          rw [hRelative]
          exact ⟨hzW, subset_tsupport (g.cutoff ν) hz⟩
        have hr := hObserveJet (g.phase ν) (hPhaseAt ν hzS) (EuclideanSpace.single r 1)
        have hs := hObserveJet (g.phase ν) (hPhaseAt ν hzS) (EuclideanSpace.single s 1)
        change fderiv ℝ (phi ν) y (EuclideanSpace.single r 1) =
          incrementsGlobalScalarDerivative (I := I) (g.phase ν) (t, e.symm y) (v r) at hr
        change fderiv ℝ (phi ν) y (EuclideanSpace.single s 1) =
          incrementsGlobalScalarDerivative (I := I) (g.phase ν) (t, e.symm y) (v s) at hs
        have ht := increments_leading_opposite_coefficient 1 (b ν y) (nf ν y)
          (_hUnit ν (t, e.symm y) hzW hz)
          (fun r ↦ fderiv ℝ (phi ν) y (EuclideanSpace.single r 1)) r s
        rw [hr, hs] at ht
        dsimp only [lead, incrementsGlobalObservedLeading, b, nf, phi] at ht ⊢
        simpa only [one_pow, one_mul] using ht
    unfold incrementsOppositePrimaryContribution
    simp_rw [hterm]
    rw [← Complex.ofReal_sum]
    exact congrArg (fun a : ℝ ↦ (a : ℂ)) (_hDecomp (t, e.symm y) hzW (v r) (v s))
  have hMean (r s : Fin (m + 1)) :
      incrementsGlobalObservedZero F hF g input (q + 2) tau 1 e t y r s -
        (input t (e.symm y) (v r) (v s) : ℂ) = incrementsMeanRemainder lead err r s := by
    rw [hZero, ← hLeading]
    rw [show coeff = lead + err from hCoeff]
    rfl
  have hAmpJet (ch : Bool) (ν : Λ) (r : Fin (m + 1)) :
      fderiv ℝ (fun x ↦ incrementsGlobalPrimaryAmplitude F hF g input (q + 2)
        tau ch ν (t, e.symm x)) y (EuclideanSpace.single r 1) =
      incrementsGlobalSpatialDerivative (I := I)
        (incrementsGlobalPrimaryAmplitude F hF g input (q + 2) tau ch ν)
          (t, e.symm y) (v r) :=
    hObserveJet _ ((hAmplitude ch ν).contMDiffAt (_hW.mem_nhds hzW))
      (EuclideanSpace.single r 1)
  have hCoeffNative (ν : Λ) (r : Fin (m + 1)) (co : Fin N) : coeff ν r co =
      (incrementsGlobalPrimaryCoefficient F hF g input (q + 2) tau true ν
        (t, e.symm y) (v r) co : ℂ) + Complex.I *
      (incrementsGlobalPrimaryCoefficient F hF g input (q + 2) tau false ν
        (t, e.symm y) (v r) co : ℂ) := by
    by_cases hz : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)
    · let AR := fun x ↦ incrementsGlobalPrimaryAmplitude F hF g input (q + 2)
        tau true ν (t, e.symm x)
      let AI := fun x ↦ incrementsGlobalPrimaryAmplitude F hF g input (q + 2)
        tau false ν (t, e.symm x)
      let C := incrementsFreeComplexCoordinate co
      have hAR : DifferentiableAt ℝ AR y :=
        (hObserve (incrementsGlobalPrimaryAmplitude F hF g input (q + 2) tau true ν)
          ((hAmplitude true ν).contMDiffAt (_hW.mem_nhds hzW))).differentiableAt (by simp)
      have hAI : DifferentiableAt ℝ AI y :=
        (hObserve (incrementsGlobalPrimaryAmplitude F hF g input (q + 2) tau false ν)
          ((hAmplitude false ν).contMDiffAt (_hW.mem_nhds hzW))).differentiableAt (by simp)
      have hsum : incrementsPrimaryCorrectionSum (R ν) (Q ν) co =
          fun x ↦ C (AR x) + Complex.I • C (AI x) := by
        funext x
        simp only [incrementsPrimaryCorrectionSum, AR, AI, incrementsGlobalPrimaryAmplitude,
          map_sum, Finset.smul_sum, Finset.sum_add_distrib, R, Q, C]
      have hjet := (C.hasFDerivAt.comp y hAR.hasFDerivAt).add
        ((C.hasFDerivAt.comp y hAI.hasFDerivAt).const_smul Complex.I)
      have hh := increments_primary_correction_coefficient_eq (phi ν) tau (R ν) (Q ν)
        y (EuclideanSpace.single r 1) co (hR ν) (hQ ν)
      change HasFDerivAt (fun x ↦ C (AR x) + Complex.I • C (AI x))
        (C.comp (fderiv ℝ AR y) + Complex.I • C.comp (fderiv ℝ AI y)) y at hjet
      rw [hsum, hjet.fderiv] at hh
      dsimp only [AR, AI] at hh
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        smul_apply] at hh
      rw [hAmpJet true ν r, hAmpJet false ν r] at hh
      have hp := hObserveJet (g.phase ν) (hPhaseAt ν hz) (EuclideanSpace.single r 1)
      change fderiv ℝ (phi ν) y (EuclideanSpace.single r 1) =
        incrementsGlobalScalarDerivative (I := I) (g.phase ν) (t, e.symm y) (v r) at hp
      rw [hp] at hh
      change coeff ν r co = _ at hh
      rw [hh]
      have hC (u : EuclideanSpace ℝ (Fin N)) : C u = (u co : ℂ) := rfl
      simp only [hC, smul_eq_mul]
      simp only [incrementsGlobalPrimaryCoefficient, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_false, ite_true, add_apply,
        sub_apply, ContinuousLinearMap.smulRight_apply,
        WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    · have hAmpValue (ch : Bool) :
          incrementsGlobalPrimaryAmplitude F hF g input (q + 2) tau ch ν (t, e.symm y) = 0 :=
        (hAmplitudeZero ch ν (t, e.symm y) hzW hz).eq_of_nhds
      have hAmpDeriv (ch : Bool) : incrementsGlobalSpatialDerivative (I := I)
          (incrementsGlobalPrimaryAmplitude F hF g input (q + 2) tau ch ν)
            (t, e.symm y) = 0 := by
        have hin : ContinuousAt (fun x : M ↦ (t, x)) (e.symm y) :=
          continuousAt_const.prodMk continuousAt_id
        have hs : (fun x : M ↦ incrementsGlobalPrimaryAmplitude F hF g input
            (q + 2) tau ch ν (t, x)) =ᶠ[𝓝 (e.symm y)] 0 :=
          (hAmplitudeZero ch ν (t, e.symm y) hzW hz).comp_tendsto hin
        have hd := hs.mfderiv_eq (I := I) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin N)))
        rw [show (0 : M → EuclideanSpace ℝ (Fin N)) =
          (fun _ ↦ (0 : EuclideanSpace ℝ (Fin N))) from rfl, mfderiv_const] at hd
        unfold incrementsGlobalSpatialDerivative
        rw [hd]
        ext w
        rfl
      have hc := congrFun (congrFun (hInactive ν hz) r) co
      rw [hc]
      simp only [incrementsGlobalPrimaryCoefficient, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_false, ite_true, hAmpDeriv, hAmpValue,
        smul_zero, ContinuousLinearMap.smulRight_zero, zero_add, sub_zero,
        zero_apply, WithLp.ofLp_zero, Pi.zero_apply, Complex.ofReal_zero, mul_zero]
  have hOppositeReal (r s : Fin (m + 1)) :
      (incrementsOppositePrimaryContribution coeff r s).re =
        incrementsGlobalPrimaryMean F hF g input (q + 2) tau t (e.symm y) (v r) (v s) := by
    have hterm (ν : Λ) : ((1 / 4 : ℂ) *
        ((coeff ν r ⬝ᵥ (fun co ↦ conj (coeff ν s co))) +
          ((fun co ↦ conj (coeff ν r co)) ⬝ᵥ coeff ν s))).re =
        (1 / 2 : ℝ) *
          (inner ℝ (incrementsGlobalPrimaryCoefficient F hF g input (q + 2) tau true ν
              (t, e.symm y) (v r))
            (incrementsGlobalPrimaryCoefficient F hF g input (q + 2) tau true ν
              (t, e.symm y) (v s)) +
           inner ℝ (incrementsGlobalPrimaryCoefficient F hF g input (q + 2) tau false ν
              (t, e.symm y) (v r))
            (incrementsGlobalPrimaryCoefficient F hF g input (q + 2) tau false ν
              (t, e.symm y) (v s))) := by
      rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num]
      simp only [dotProduct, hCoeffNative, Complex.mul_re, Complex.add_re,
        Complex.mul_im, Complex.add_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.re_sum, Complex.im_sum, zero_mul, mul_zero, one_mul,
        zero_add, add_zero, sub_zero, PiLp.inner_apply, Real.inner_apply]
      ring_nf
      rw [Finset.sum_add_distrib]
      ring
    unfold incrementsOppositePrimaryContribution
    rw [Complex.re_sum]
    simp_rw [hterm]
    simp only [incrementsGlobalPrimaryMean, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.add_apply, LinearMap.BilinForm.comp_apply,
      ContinuousLinearMap.coe_coe, innerₗ_apply_apply, smul_eq_mul, Finset.mul_sum]
  have hRealMean (r s : Fin (m + 1)) : incrementsMeanRealCoordinate
      (incrementsGlobalObservedZero F hF g input (q + 2) tau 1 e t y r s -
        (input t (e.symm y) (v r) (v s) : ℂ)) =
      (fun _ : Fin 1 ↦ incrementsGlobalPrimaryMeanError F hF g input (q + 2) tau
        t (e.symm y) (v r) (v s)) := by
    ext j
    change (_ - (input t (e.symm y) (v r) (v s) : ℂ)).re = _
    rw [Complex.sub_re, Complex.ofReal_re, hZero, hOppositeReal]
    rfl
  have hUnitMean (r s : Fin (m + 1)) : incrementsMeanRealCoordinate
      (incrementsGlobalObservedZero F hF g input (q + 2) tau 1 e t y r s -
        (input t (e.symm y) (v r) (v s) : ℂ)) =
      ∑ ν, incrementsMeanRealCoordinate (incrementsMeanRemainder
        (fun _ : Unit ↦ lead ν) (fun _ : Unit ↦ err ν) r s) := by
    have hsum : incrementsMeanRemainder lead err r s =
        ∑ ν, incrementsMeanRemainder (fun _ : Unit ↦ lead ν) (fun _ : Unit ↦ err ν) r s := by
      simp [incrementsMeanRemainder, incrementsOppositePrimaryContribution,
        Finset.sum_sub_distrib]
    rw [hMean, hsum, map_sum]
  have hZeroScaled (delta : ℝ) (r s : Fin (m + 1)) :
      incrementsGlobalObservedZero F hF g input (q + 2) tau delta e t y r s =
        delta ^ 2 • incrementsOppositePrimaryContribution coeff r s := by
    unfold incrementsGlobalObservedZero
    change (∑ ν, ∑ μ, incrementsFourPhaseZeroGermPair
      (fun ν x ↦ phi ν x / tau) (delta • coeff) y ν μ r s) = _
    simp_rw [increments_four_phase_zero_germ_pair_div phi tau _htau.ne']
    rw [increments_four_phase_zero_germ_eq_opposite phi (delta • coeff)
      (fun ν ↦ {x | (t, e.symm x) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)}) y
      (fun ν hn r ↦ by
        change delta • coeff ν r = 0
        rw [show coeff ν r = 0 from congrFun (hInactive ν hn) r, smul_zero])
      hDoubleObs hInteractionObs r s, incrementsOppositePrimaryContribution_smul]
  have hFormula (theta : Λ → EuclideanSpace ℝ (Fin (m + 1)) → ℝ) :
      incrementsPrimaryWave theta tau (fun _ _ _ ↦ 1) R Q =
        fun x ↦ ∑ ν, (Real.cos (theta ν x / tau) • (∑ β, R ν β x) -
          Real.sin (theta ν x / tau) • (∑ β, Q ν β x)) := by
    funext x
    unfold incrementsPrimaryWave
    simp only [one_smul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro β _
    exact congrFun (increments_primary_real_mode_eq (theta ν) tau (R ν β) (Q ν β)) x
  let activePhi := fun ν (x : EuclideanSpace ℝ (Fin (m + 1))) ↦
    if (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) then phi ν x else 0
  have hPhiActive (ν : Λ) : DifferentiableAt ℝ (activePhi ν) y := by
    by_cases hz : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)
    · simpa only [activePhi, ite_true, hz] using
        (hObserve (g.phase ν) (hPhaseAt ν hz)).differentiableAt (by simp)
    · simpa only [activePhi, ite_false, hz] using differentiableAt_const (0 : ℝ)
  have hSameWave : (fun x ↦ incrementsGlobalPrimaryWave F hF g input (q + 2) tau
      (t, e.symm x)) =ᶠ[𝓝 y] incrementsPrimaryWave activePhi tau (fun _ _ _ ↦ 1) R Q := by
    have hterm (ν : Λ) :
        (fun x ↦ Real.cos (phi ν x / tau) • (∑ β, R ν β x) -
          Real.sin (phi ν x / tau) • (∑ β, Q ν β x)) =ᶠ[𝓝 y]
        (fun x ↦ Real.cos (activePhi ν x / tau) • (∑ β, R ν β x) -
          Real.sin (activePhi ν x / tau) • (∑ β, Q ν β x)) := by
      by_cases hz : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)
      · simp only [activePhi, hz, ite_true]
        exact Filter.EventuallyEq.rfl
      · have hR0 : (fun x ↦ ∑ β, R ν β x) =ᶠ[𝓝 y] 0 :=
          (hAmplitudeZero true ν (t, e.symm y) hzW hz).comp_tendsto hobsCont
        have hQ0 : (fun x ↦ ∑ β, Q ν β x) =ᶠ[𝓝 y] 0 :=
          (hAmplitudeZero false ν (t, e.symm y) hzW hz).comp_tendsto hobsCont
        filter_upwards [hR0, hQ0] with x hxR hxQ
        simp only [hxR, hxQ, Pi.zero_apply, smul_zero, sub_zero]
    rw [hFormula]
    filter_upwards [eventually_all.mpr hterm] with x hx
    exact Finset.sum_congr rfl (fun ν _ ↦ hx ν)
  have hCoeffActive :
      (fun ν r ↦ incrementsPrimaryDerivativeCoefficient (activePhi ν) tau (fun _ _ ↦ 1)
        (R ν) (Q ν) y (EuclideanSpace.single r 1)) = coeff := by
    funext ν r co
    by_cases hz : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)
    · simp only [activePhi, hz, ite_true]
      rfl
    · have hRv (β : Β) : R ν β y = 0 :=
        (hPieceZero true ν β (t, e.symm y) hzW hz).eq_of_nhds
      have hQv (β : Β) : Q ν β y = 0 :=
        (hPieceZero false ν β (t, e.symm y) hzW hz).eq_of_nhds
      change incrementsPrimaryDerivativeCoefficient (activePhi ν) tau (fun _ _ ↦ 1)
        (R ν) (Q ν) y (EuclideanSpace.single r 1) co =
        incrementsPrimaryDerivativeCoefficient (phi ν) tau (fun _ _ ↦ 1)
          (R ν) (Q ν) y (EuclideanSpace.single r 1) co
      simp only [incrementsPrimaryDerivativeCoefficient, hRv, hQv,
        WithLp.ofLp_zero, Pi.zero_apply, Complex.ofReal_zero, mul_zero, zero_add, add_zero]
  have hGrouped (r : Fin (m + 1)) :
      incrementsGroupedRealDerivative (fun ν ↦ activePhi ν y / tau) coeff r =
        incrementsGroupedRealDerivative (fun ν ↦ phi ν y / tau) coeff r := by
    ext co
    change (∑ ν, (incrementsMeanPhase (activePhi ν y / tau) * coeff ν r co).re) =
      ∑ ν, (incrementsMeanPhase (phi ν y / tau) * coeff ν r co).re
    apply Finset.sum_congr rfl
    intro ν _
    by_cases hz : (t, e.symm y) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)
    · simp only [activePhi, hz, ite_true]
    · have hc : coeff ν r co = 0 := congrFun (congrFun (hInactive ν hz) r) co
      simp only [hc, mul_zero]
  have hFirstJet (delta : ℝ) (r : Fin (m + 1)) :
      fderiv ℝ (fun x ↦ delta • incrementsGlobalPrimaryWave F hF g input (q + 2) tau
        (t, e.symm x)) y (EuclideanSpace.single r 1) =
      delta • incrementsGroupedRealDerivative (fun ν ↦ phi ν y / tau) coeff r := by
    have hg := increments_primary_wave_grouped_derivative activePhi tau (fun _ _ _ ↦ 1)
      R Q y (EuclideanSpace.single r 1) hPhiActive
      (fun _ _ ↦ differentiableAt_const 1) hR hQ
    change fderiv ℝ (incrementsPrimaryWave activePhi tau (fun _ _ _ ↦ 1) R Q) y
        (EuclideanSpace.single r 1) =
      incrementsGroupedRealDerivative (fun ν ↦ activePhi ν y / tau)
        (fun ν r ↦ incrementsPrimaryDerivativeCoefficient (activePhi ν) tau (fun _ _ ↦ 1)
          (R ν) (Q ν) y (EuclideanSpace.single r 1)) r at hg
    rw [hCoeffActive, hGrouped] at hg
    have hw := (hObserve (incrementsGlobalPrimaryWave F hF g input (q + 2) tau)
      (hWave.contMDiffAt (_hW.mem_nhds hzW))).differentiableAt (by simp)
    rw [fderiv_fun_const_smul hw delta, smul_apply, hSameWave.fderiv_eq (𝕜 := ℝ), hg]
  refine ⟨hCoeff, hFirstJet, hMean, (fun r s ↦ ⟨hRealMean r s, hUnitMean r s⟩), ?_⟩
  · intro delta r s
    ext j
    change (incrementsGlobalObservedZero F hF g input (q + 2) tau delta e t y r s).re = _
    rw [hZeroScaled]
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hOppositeReal]
    change delta ^ 2 * _ = delta ^ 2 * (_ + (_ - _))
    ring

end GlobalEmbedding.Paper
