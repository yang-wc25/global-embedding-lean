import Repair.EntranceSpatialPrimaryProfiles
import Repair.EntranceUniformReferencePacket

/-!
# The original factory's primary charts enter the numerical reference budget

The original kernel reserve is stated in the original observing chart and
on its actual primary carrier. The actual same packet's inverse transports
that statement to the reference interface; no native frame or Hessian
output bound is assumed. Source sampling and the inner-domain property
are checked against the original observer using the packet's host identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance entranceSpatialBudgetRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance entranceSpatialBudgetSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

/-- A reserve in the literal original coordinates, before any primary
adapted chart. The actual template/transition factory supplies this. -/
structure RepairOriginalPrimaryKernelInputs
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (U : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X) (kappa : ℝ) : Prop where
  lower : ∀ nu i z, z ∈ U i →
    ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu →
    ∀ w, kappa*‖w‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart
        (fun p x => Data.F ((Data.parameterChart i.2).symm p,x))
        (fun _ => Data.atlas.chart i.1) z)
      (fderiv ℝ (fun x : D => Data.phase nu
        ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm x)) z.2) w‖

def RepairReferenceSpatialPrimarySupply.chart_inputs
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ}
    {owner : Fin Data.primaryCount → OpenPartialHomeomorph M D}
    {xi : Fin Data.primaryCount → D →L[ℝ] ℝ}
    {plateau : Fin Data.primaryCount → P × M → ℝ}
    {U : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X}
    {mu bound : ℝ}
    (s : RepairReferenceSpatialPrimarySupply Data theta owner xi plateau U mu bound)
    (hmu : 0 < mu) (hBound : 0 ≤ bound)
    (hUOpen : ∀ i, U i ⊆ actualOriginalNativeOpen Data i)
    (hOwnerSource : ∀ nu z, z ∈ Data.primaryDomain nu → z.2 ∈ (owner nu).source)
    (V : ℝ) (hV : 0 ≤ V) (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hSourceValue : ∀ i z, z ∈ U i → ‖z‖ ≤ V)
    (hOwnerValue : ∀ nu i z, z ∈ U i →
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).source →
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu →
      ‖repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu) z‖ ≤ V)
    (hForwardJet : ∀ nu i j, 1 ≤ j → ∀ z, z ∈ U i →
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).source →
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu →
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1)
        (owner nu)) z‖ ≤ T j)
    (hInverseJet : ∀ nu i j, 1 ≤ j → ∀ z,
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).target →
      (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).symm z ∈ U i →
      ((Data.parameterChart i.2).symm z.1,(owner nu).symm z.2) ∈ Data.primaryDomain nu →
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1)
        (owner nu)).symm z‖ ≤ T j)
    (hSamples : ∀ i z, z ∈ U i → parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i)
    (hInner : ∀ i z, z ∈ U i → (Data.atlas.chart i.1).symm z.2 ∈ Data.atlas.inner i.1)
    (kappa : ℝ) (kernel : RepairOriginalPrimaryKernelInputs Data U kappa) :
    RepairUniformReferenceChartInputs Data theta s.packet
      (repairEntranceSpatialNativeForward V (2*(1+2*bound)) T)
      (repairEntranceSpatialNativeInverse V (2*actualPhaseInverseConstant mu (2*bound)) T) kappa := by
  have hJets := s.native_profiles hmu hBound hUOpen hOwnerSource V hV T hT
    hSourceValue hOwnerValue hForwardJet hInverseJet
  refine ⟨hJets.1,hJets.2,?_,?_,?_⟩
  · intro nu i a z hz
    rw [s.packet.host]
    exact hSamples i z ((s.source nu i a z).mp hz).1
  · intro nu i a y hy
    have hNative := hy.2
    change (y.1,Data.atlas.chart (s.packet.piece nu i a).host y.2) ∈
      (s.packet.piece nu i a).native.source at hNative
    have hSource : (y.1,Data.atlas.chart i.1 y.2) ∈ (s.packet.piece nu i a).native.source := by
      simpa only [s.packet.host nu i a] using hNative
    have hInner' := hInner i _ ((s.source nu i a _).mp hSource).1
    have hyChart : y.2 ∈ (Data.atlas.chart i.1).source := by
      simpa only [s.packet.host nu i a] using hy.1.2
    simpa only [s.packet.host nu i a,(Data.atlas.chart i.1).left_inv hyChart] using hInner'
  · intro nu i a z hz
    have hSource := (s.source nu i a _).mp ((s.packet.piece nu i a).native.map_target hz)
    have hKernel (host : Fin Data.atlas.count) (hHost : host=i.1) :
        ∀ w, kappa*‖w‖ ≤ ‖covectorRestriction
          (round4ActualPhaseOperatorInChart
            (fun p x => Data.F ((Data.parameterChart i.2).symm p,x))
            (fun _ => Data.atlas.chart host) ((s.packet.piece nu i a).native.symm z))
          (fderiv ℝ (fun x : D => Data.phase nu
            ((Data.parameterChart i.2).symm ((s.packet.piece nu i a).native.symm z).1,
              (Data.atlas.chart host).symm x)) ((s.packet.piece nu i a).native.symm z).2) w‖ := by
      subst host
      exact kernel.lower nu i _ hSource.1 hSource.2
    exact hKernel _ (s.packet.host nu i a)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairReferenceSpatialPrimarySupply.chart_inputs
