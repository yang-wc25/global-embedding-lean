import GlobalEmbedding.Paper.UpgradeRankQFiniteLocalLegalWaves
import GlobalEmbedding.Paper.BufferedAtlas
import GlobalEmbedding.Paper.PaperCoordinateNormBridge
import GlobalEmbedding.Paper.InducedMetric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The original paired-probe boundary, with actual geometric objects

This is an interface, not a proof of `prop:probes`. It records the full
response estimates used downstream, with actual native derivatives, the
original atlas norm, and an actual orthogonal normal identification. There
is no field asserting incidence rank, separation, or an embedding.

The original target statement is not changed. A caller using this provider
must explicitly retain its dependency until the upstream construction is
supplied. See `PROBES_INTERFACE.md`, including the quantitative spatial
control required for the paper's chosen polar identification.
-/

noncomputable section
open Bundle Filter Manifold Set GlobalEmbedding.Paper
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.Upgrade

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual local waves delivered by the existing local-wave theorem.
The normal field may vanish. Smoothness is required on the actual open chart,
and the cutoff keeps its support inside that chart. -/
structure LocalLegalWave (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) where
  center : M
  domain : Set M
  phase : M → ℝ
  normal : ∀ x, normalSpace (I := IM) F x
  cutoff : SmoothBumpFunction IM center
  domain_open : IsOpen domain
  center_mem : center ∈ domain
  domain_chart : domain ⊆ (chartAt E center).source
  support_subset : tsupport (cutoff : M → ℝ) ⊆ domain
  phase_smooth : ContMDiffOn IM 𝓘(ℝ, ℝ) ∞ phase domain
  normal_smooth : ContMDiffOn IM 𝓘(ℝ, V) ∞ (fun x ↦ (normal x : V)) domain
  legal : ∀ x ∈ domain,
    GoodCovector F hF x (mfderiv IM 𝓘(ℝ, ℝ) phase x) ∧
      normal x ∈ supportedRankLegalValueSpace (trueSecondForm F hF x)
        (mfderiv IM 𝓘(ℝ, ℝ) phase x).toLinearMap

namespace LocalLegalWave

/-- The actual global leading value field, with its original cutoff. -/
def value {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    (w : LocalLegalWave F hF) (x : M) : V := w.cutoff x • (w.normal x : V)

/-- The actual original tensor, expressed on the native tangent model. -/
def tensor {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    (w : LocalLegalWave F hF) (x : M) : SymmetricSquare E →L[ℝ] V :=
  LinearMap.toContinuousLinearMap
    (w.cutoff x • supportedRankLegalVariation
      (mfderiv IM 𝓘(ℝ, ℝ) w.phase x).toLinearMap (w.normal x : V))

end LocalLegalWave

/-- The original atlas norm, with Euclidean-to-coordinate conversions made
explicit. No supremum domain is replaced by the open differentiation domain. -/
def probeAtlasCj (A : BufferedAtlas M E) (j : ℕ) (f : M → V) : ℝ≥0∞ :=
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  paperAtlasCj j
    (fun i x ↦ v (f ((A.chart i).symm (e.symm x))))
    (fun i ↦ e '' (A.chart i).target)
    (fun i ↦ e '' ((A.chart i) '' A.support i))

/-- The two actual coordinate responses per wave, with no nonempty-list
assumption. This finite space can be reindexed to `Fin (2*r)` for avoidance. -/
abbrev ProbeParameters (r : ℕ) := (Fin r × Bool) → ℝ

def probeTrig (b : Bool) (theta : ℝ) : ℝ := if b then Real.sin theta else Real.cos theta

/-- Actual identified true second form, not a separately supplied field. -/
def identifiedTrueSecondForm
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Q : ∀ x, normalSpace (I := IM) F x ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ x)
    (x : M) : SymmetricSquare E →L[ℝ] V :=
  (normalSpace (I := IM) F₀ x).subtypeL.comp
    ((Q x).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (LinearMap.toContinuousLinearMap (show SymmetricSquare E →ₗ[ℝ]
        normalSpace (I := IM) F x from trueSecondForm F hF x)))

/-- Ambient operator of the same actual normal-bundle identification. Its
definition retains the true new normal projection and the original inclusion. -/
def normalIdentificationOperator (F₀ F : M → V)
    (Q : ∀ x, normalSpace (I := IM) F x ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ x)
    (x : M) : V →L[ℝ] V :=
  (normalSpace (I := IM) F₀ x).subtypeL.comp
    ((Q x).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (normalSpace (I := IM) F x).orthogonalProjectionOnto)

/-- The actual inverse differential of the selected atlas chart. On its
source this transports the fixed coordinate model into the true tangent
fiber. Arbitrary values off that chart are not used in a norm estimate. -/
def probeAtlasFrame (A : BufferedAtlas M E) (i : Fin A.count) (x : M) : E →L[ℝ] E :=
  mfderiv 𝓘(ℝ, E) IM (A.chart i).symm (A.chart i x)

/-- Source-frame transport of the same symmetric tensor. This is explicitly
included before the parameter derivative is taken. -/
def probeTensorInFrame (frame : E →L[ℝ] E) (B : SymmetricSquare E →L[ℝ] V) :
    SymmetricSquare E →L[ℝ] V :=
  B.comp (LinearMap.toContinuousLinearMap (symmetricSquareLinearMap frame.toLinearMap))

/-- Full probe output for an actual fixed finite list. All derivatives in the
estimates are native derivatives of the one family or of its identified true
form. Outside the admissible scale/parameter domain the slice can be extended
by the original map; no joint smoothness or exact metric is required there.

`distinct_on_overlap` is the hierarchical choice in the original proof. It
must be supplied by phase preparation, not inferred from positivity alone. -/
structure ProbeGeometry (F₀ : M → V) (r : ℕ) where
  radius : ℝ
  radius_pos : 0 < radius
  threshold : ℝ
  threshold_pos : 0 < threshold
  map : ℝ → ProbeParameters r → M → V
  slice_smooth : ∀ t u, ContMDiff IM 𝓘(ℝ, V) ∞ (map t u)
  joint_smooth : ∀ t, 0 < t → t < threshold →
    ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry (map t)) (Metric.ball 0 radius ×ˢ Set.univ)
  metric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
    inducedMetric (I := IM) (map t u) x = inducedMetric (I := IM) F₀ x
  normalIdentification : ∀ (t : ℝ) (u : ProbeParameters r) (x : M),
    normalSpace (I := IM) (map t u) x ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ x
  normalIdentification_smooth : ∀ t, 0 < t → t < threshold →
    ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun z : ProbeParameters r × M ↦ normalIdentificationOperator (n := n) F₀ (map t z.1)
        (normalIdentification t z.1) z.2) (Metric.ball 0 radius ×ˢ Set.univ)

/-- The original quantitative probe contract, extending the same actual geometry.
This separation makes the object/estimate distinction explicit; no estimate is
replaced by a conclusion about incidence rank. -/
structure ExactProbeFamily
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (A : BufferedAtlas M E) {r : ℕ} (waves : Fin r → LocalLegalWave F₀ hF₀)
    extends ProbeGeometry (n := n) F₀ r where
  weight : Fin r → ℝ
  weight_pos : ∀ l, 0 < weight l
  distinct_on_overlap : ∀ l k, l ≠ k →
    (tsupport (waves l).cutoff ∩ tsupport (waves k).cutoff).Nonempty → weight l ≠ weight k
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  etaB : ℝ → ℝ
  etaV : ℝ → ℝ
  etaB_nonneg : ∀ t, 0 ≤ etaB t
  etaV_nonneg : ∀ t, 0 ≤ etaV t
  etaB_tendsto : Tendsto etaB (𝓝[>] 0) (𝓝 0)
  etaV_tendsto : Tendsto etaV (𝓝[>] 0) (𝓝 0)
  closeness : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    probeAtlasCj A 2 (map t u - F₀) ≤ ENNReal.ofReal (constant * t ^ ((44 : ℝ) / 5))
  spatial_C3 : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    probeAtlasCj A 3 (map t u) ≤ ENNReal.ofReal constant
  parameter_C1 : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ d,
    probeAtlasCj A 1 (fun x ↦ fderiv ℝ (fun v ↦ map t v x) u d) ≤
      ENNReal.ofReal (constant * t ^ (10 : ℕ) * ‖d‖)
  parameter_C2 : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ d,
    probeAtlasCj A 2 (fun x ↦ fderiv ℝ (fun v ↦ map t v x) u d) ≤
      ENNReal.ofReal (constant * t ^ ((44 : ℝ) / 5) * ‖d‖)
  secondForm_response : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    ∀ l b i x, x ∈ A.support i →
      ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i x)
          (identifiedTrueSecondForm (n := n) F₀ (map t v) (slice_smooth t v)
          (normalIdentification t v) x)) u (Pi.single (l, b) 1) -
        (t ^ ((44 : ℝ) / 5) * probeTrig b (weight l * (waves l).phase x /
          t ^ ((6 : ℝ) / 5))) •
          probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x)‖ ≤
        t ^ ((44 : ℝ) / 5) * (etaB t + constant * ‖u‖)
  value_response : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    ∀ l b x,
      ‖fderiv ℝ (fun v ↦ map t v x) u (Pi.single (l, b) 1) -
        (-(t ^ ((56 : ℝ) / 5)) * (weight l ^ 2)⁻¹ *
          probeTrig b (weight l * (waves l).phase x / t ^ ((6 : ℝ) / 5))) •
          (waves l).value x‖ ≤
        t ^ ((56 : ℝ) / 5) * (etaV t + constant * ‖u‖)

end GlobalEmbedding.Upgrade
