import Probes.Round4PrescribedGlobalZeroMean
import Smoothing.Round3ParameterMeanNorms

/-!
# The same global prescribed mean in the original source-first tensor coordinates

Every native tangent direction is the original inverse-atlas differential.
Parameter inverse charts, the source-first model, and all ordered tensor slots
remain literal. This supplies the identity needed by the unchanged original
paper seminorm; it makes no coordinate or native-mean equality an input.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N p r count : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ
local notation "𝓙" => 𝓘(ℝ,D)

/-- Actual opposite coefficient after the original parameter and source charts. -/
def round4OriginalObservedMeanCoefficient
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (R Q : Fin r → Ep × M → V)
    (idx : Fin atlas.count × Fin count) (z : X) (k : Fin ((m+1)*(m+1))) : ℂ :=
  incrementsOppositePrimaryContribution
    (round4ObservedCoefficient phase tau R Q ((param idx.2).symm z.1) (atlas.chart idx.1).symm z.2)
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

theorem round4_prescribed_original_mean_coordinates
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := 𝓙) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := 𝓙) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (phase l) W)
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (hAtlas : IsSmoothBufferedAtlas atlas) (u : Pspace)
    (idx : Fin atlas.count × Fin count) (y : Fin (m+1+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation atlas param idx)
    (hyW : incrementsOriginalJointPoint atlas param idx y ∈ W) :
    let R := fun l => round4PrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) u
    let Q := fun l => round4PrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) u
    incrementsOriginalTensorCoordinates atlas param
      (round4PrescribedNativeMean label F hF c vf phase tau length a u) idx y =
      fun k => (round4OriginalObservedMeanCoefficient atlas param phase tau R Q idx
        ((parameterTensorModelEquiv (m+1) d).symm y) k).re := by
  intro R Q
  let b := (param idx.2).symm (incrementsOriginalParameterPoint y)
  let x := incrementsOriginalSourcePoint y
  let obs := (atlas.chart idx.1).symm
  have hxy : (b,obs x) ∈ W := hyW
  have hobs : ContMDiffAt 𝓘(ℝ,D) 𝓙 ∞ obs x :=
    (contMDiffOn_symm_of_mem_maximalAtlas (hAtlas.chart_mem idx.1)).contMDiffAt
      ((atlas.chart idx.1).open_target.mem_nhds hy.1)
  have ha (l : Fin r) (ch : Bool) := (round4_prescribed_global_amplitude_smooth ch label l F hF
    (c l) (vf l) tau length (a l) W (K l) hW (hK l) (hKsource l) (hchart l)
    (hA l) (hB l) (hG l) (hJ l) (hT l) (hBR l) (hvf l) (hinput l) u).1
  funext k
  have hh := round4_observed_opposite_native_mean phase tau R Q b obs x
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    (fun l => (hphase l).contMDiffAt (hW.mem_nhds hxy))
    (fun l => (ha l false).contMDiffAt (hW.mem_nhds hxy))
    (fun l => (ha l true).contMDiffAt (hW.mem_nhds hxy)) hobs
  exact hh.symm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_original_mean_coordinates
