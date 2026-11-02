import Smoothing.Round3OuterIntrinsicNormalCoordinates
import Smoothing.Round3OuterC2SpatialDifference

/-! Actual chart data for the new physical normal on a primary open region.
These fields describe the fixed reference charts, genuine sample maps and
the lower reserves produced by original C2 stability.  No derivative budget
for SF, its Hessian, its new normal, or a correction is included.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance coverFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance coverFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance coverFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance coverFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

def round3NormalChartSlice (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) : Ep → M → Ey :=
  fun p x => Data.F ((Data.parameterChart i.2).symm p,x)

def round3NormalChartReference (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (e : Ep → OpenPartialHomeomorph M D) (vref : P × M → Ey) : X → Ey :=
  fun z => vref ((Data.parameterChart i.2).symm z.1,(e z.1).symm z.2)

structure Round3OriginalNormalCoverGeometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (psi : P → M → ℝ) (vref : P × M → Ey) (A : Type*)
    (Orig Samples : Fin Data.atlas.count × Fin Data.parameterCount → Set Y)
    (cF cT mu : ℝ) where
  host : (Fin Data.atlas.count × Fin Data.parameterCount) → A →
    Fin Data.atlas.count × Fin Data.parameterCount
  chart : (Fin Data.atlas.count × Fin Data.parameterCount) → A → Ep → OpenPartialHomeomorph M D
  native : (Fin Data.atlas.count × Fin Data.parameterCount) → A → Set X
  original : (Fin Data.atlas.count × Fin Data.parameterCount) → A → Set Y
  forward : (Fin Data.atlas.count × Fin Data.parameterCount) → A → Y → X
  original_open : ∀ i a, IsOpen (original i a)
  native_open : ∀ i a, IsOpen (native i a)
  original_subset : ∀ i a, original i a ⊆ Orig i
  covers : ∀ i y, y ∈ Samples i → ∃ a, y ∈ original i a
  chart_smooth : ∀ i a p, chart i a p ∈ IsManifold.maximalAtlas 𝓙 ∞ M
  forward_smooth : ∀ i a, ContDiffOn ℝ ∞ (forward i a) (original i a)
  forward_maps : ∀ i a, MapsTo (forward i a) (original i a) (native i a)
  same_point : ∀ i a y, y ∈ original i a →
    ((Data.parameterChart (host i a).2).symm (forward i a y).1,
      (chart i a (forward i a y).1).symm (forward i a y).2) =
      incrementsOriginalJointPoint Data.atlas Data.parameterChart i y
  chart_target : ∀ i a z, z ∈ native i a → z.2 ∈ (chart i a z.1).target
  source : ∀ i a z, z ∈ native i a → (chart i a z.1).symm z.2 ∈ (Data.atlas.chart (host i a).1).source
  parameter : ∀ i a z, z ∈ native i a → z.1 ∈ (Data.parameterChart (host i a).2).target
  transition_smooth : ∀ i a, ContDiffOn ℝ ∞
    (round3OriginalAdaptedTransition Data.atlas (host i a).1 (chart i a)) (native i a)
  phase_smooth : ∀ i a z, z ∈ native i a → MDifferentiableAt 𝓙 𝓘(ℝ,ℝ)
    (psi ((Data.parameterChart (host i a).2).symm z.1)) ((chart i a z.1).symm z.2)
  phase_adapted : ∀ i a z, z ∈ native i a →
    psi ((Data.parameterChart (host i a).2).symm z.1) ((chart i a z.1).symm z.2) = z.2 0
  reference_smooth : ∀ i a, ContDiffOn ℝ ∞
    (round3NormalChartReference Data (host i a) (chart i a) vref) (native i a)
  sample : ∀ i a y, y ∈ Samples i ∩ original i a →
    parameterTensorModelEquiv (m+1) d
      (round3OriginalAdaptedTransition Data.atlas (host i a).1 (chart i a) (forward i a y)) ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (host i a)
  first : ∀ i a z, z ∈ native i a → ∀ w : D, cF*‖w‖^2 ≤
    ‖fderiv ℝ (round3NormalChartSlice Data (host i a) z.1 ∘ (chart i a z.1).symm) z.2 w‖^2
  transverse : ∀ i a z, z ∈ native i a → ∀ w : Tdata, cT*‖w‖^2 ≤
    ‖incrementsModeAmbientTransverseFrame (round3NormalChartSlice Data (host i a) z.1)
      (hF ((Data.parameterChart (host i a).2).symm z.1)) (chart i a z.1).symm z.2 w‖^2
  reserve : ∀ i a z, z ∈ native i a → mu ≤
    ‖actualOriginalFreeNormalFieldRaw (round3NormalChartSlice Data (host i a))
      (fun p => hF ((Data.parameterChart (host i a).2).symm p)) (chart i a)
      (round3NormalChartReference Data (host i a) (chart i a) vref) z‖

end GlobalEmbedding.Continuation
