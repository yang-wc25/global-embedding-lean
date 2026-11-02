import Probes.Round3PreparedParameterSecondaryChartSmooth
import Probes.Round3PreparedParameterCarrierObserverProfiles
import Probes.Round3PreparedParameterSecondaryPieces

/-! ALL canonical observer charts of the ONE actual signed-secondary packet
receive simultaneous primitive jet bounds on the ORIGINAL evaluation sets.
Only the true effective interaction carrier is used. Constants are fixed
before the later current map, scale and derivative order, and finite maxima
introduce no chart-count multiplier. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

 theorem round3_prepared_actual_parameter_secondary_chart_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (S : (Fin Data.atlas.count × Fin Data.parameterCount) → Set (Fin (m+1+d) → ℝ))
    (hS : ∀ i, IsCompact (S i))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i) :
    ∃ Forward Inverse Kcut : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Kcut k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) observer,
      let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
      let native := (choice.pullback (Data.parameterChart observer.2)).toNative
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans native.chart
      let rho := fun z : X => native.cutoff (native.chart.symm z)
      ∀ k z, parameterTensorModelEquiv (m+1) d z ∈ S observer →
        ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) ∈
          round3PreparedParameterSecondaryCarrier Data r choice →
        z ∈ t.source ∧ t z ∈ t.target ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Forward k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Inverse k ∧
        ell^k*‖iteratedFDeriv ℝ k rho (t z)‖ ≤ Kcut k := by
  let A := Sigma (fun r : ActualSecondarySignedRecord (Fin Data.primaryCount) =>
    Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(packet.s r i)))
  let J := A × (Fin Data.atlas.count × Fin Data.parameterCount)
  let Sn := fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S i
  have hSn (i) : IsCompact (Sn i) :=
    (parameterTensorModelEquiv (m+1) d).toHomeomorph.isCompact_preimage.mpr (hS i)
  have hSnTarget (i) : Sn i ⊆ (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).target := by
    intro z hz
    have hh := hSO i hz
    change ((parameterTensorModelEquiv (m+1) d).symm (parameterTensorModelEquiv (m+1) d z)).2 ∈
        (Data.atlas.chart i.1).target ∧
      ((parameterTensorModelEquiv (m+1) d).symm (parameterTensorModelEquiv (m+1) d z)).1 ∈
        (Data.parameterChart i.2).target at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply,mem_prod] using hh.symm
  let choice := fun r i (a : packet.s r i) =>
    round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
  have hChart (r) (i) (a : packet.s r i) :=
    round3_prepared_parameter_secondary_chart_smooth Data hd hs i r _ (packet.piece r i a)
  have hCarrier (r) (i) (a : packet.s r i) :
      IsClosed (round3PreparedParameterSecondaryCarrier Data r (choice r i a)) :=
    (isClosed_tsupport _).inter ((isClosed_tsupport _).inter (isClosed_tsupport _))
  have hOne (j : J) := round3_prepared_parameter_carrier_observer_profiles
    (Data.parameterChart j.2.2) (hd.parameter_charts_smooth j.2.2)
    (choice j.1.1 j.1.2.1 j.1.2.2).chart
    (round3_prepared_parameter_secondary_preserves Data hd hs j.1.2.1 j.1.1 _ (packet.piece j.1.1 j.1.2.1 j.1.2.2))
    (hChart j.1.1 j.1.2.1 j.1.2.2).1 (hChart j.1.1 j.1.2.1 j.1.2.2).2
    (choice j.1.1 j.1.2.1 j.1.2.2).cutoff (packet.smooth j.1.1 j.1.2.1 j.1.2.2)
    (round3PreparedParameterSecondaryCarrier Data j.1.1 (choice j.1.1 j.1.2.1 j.1.2.2))
    (hCarrier j.1.1 j.1.2.1 j.1.2.2) (packet.source j.1.1 j.1.2.1 j.1.2.2)
    (Data.atlas.chart j.2.1) (hd.atlas_smooth.chart_mem j.2.1)
    (Sn j.2) (hSn j.2) (hSnTarget j.2)
  choose Tf Ti Te hTf hTi hTe hb using hOne
  refine ⟨fun k => round3PreparedFiniteMaximum (fun j : J => Tf j k),
    fun k => round3PreparedFiniteMaximum (fun j : J => Ti j k),
    fun k => round3PreparedFiniteMaximum (fun j : J => Te j k),
    fun k => round3PreparedFiniteMaximum_nonneg _,
    fun k => round3PreparedFiniteMaximum_nonneg _,
    fun k => round3PreparedFiniteMaximum_nonneg _,?_⟩
  intro ell hell hell1 r i a observer ch native t rho k z hz hCarrierZ
  have hh := hb (⟨r,⟨i,a⟩⟩,observer) ell hell hell1 k z ⟨hz,hCarrierZ⟩
  exact ⟨hh.1,hh.2.1,
    hh.2.2.1.trans (round3PreparedFiniteMaximum_bound (fun j : J => Tf j k) (⟨r,⟨i,a⟩⟩,observer)),
    hh.2.2.2.1.trans (round3PreparedFiniteMaximum_bound (fun j : J => Ti j k) (⟨r,⟨i,a⟩⟩,observer)),
    hh.2.2.2.2.trans (round3PreparedFiniteMaximum_bound (fun j : J => Te j k) (⟨r,⟨i,a⟩⟩,observer))⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_actual_parameter_secondary_chart_profiles
