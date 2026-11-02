import Probes.Round3PreparedParameterActualRawPieces
import Probes.Round3PreparedParameterSecondaryStablePartition
import Probes.Round3ParameterSecondaryFromRawPieces
import Probes.Round3ParameterSecondaryRawReindex

/-! Actual canonical pieces are consumed as one all-order dependent raw
family. The common geometry cost is a maximum over the fixed reference
pieces, chosen before F and ell. Partition, overlap and every numerical
domination premise are proved internally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

 theorem round3_prepared_parameter_dependent_actual_factory
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hdRef hsRef theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
    (hPart : ∀ z, ∑ i, theta i z = 1) (L : ℕ)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (q : ℕ) (c : ℝ) (InputBudget Tinv Kcut Tobs : ℕ → ℝ) :
    let Sub := fun r => Sigma (fun i : Fin Ref.atlas.count × Fin Ref.parameterCount => ↥(packet.s r i))
    letI : ∀ r, Fintype (Sub r) := fun r => inferInstance
    ∃ Mrest Cut : ℕ → ℝ, (∀ j, 0 ≤ Mrest j) ∧ (∀ j, Cut j = Kcut (actualSecondarySolveOrder q j)) ∧
    ∀ Mnew : ℕ → ℝ, (∀ j, Mrest j ≤ Mnew j) →
    ∀ (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
      (stable : ∀ r i (a : packet.s r i), Round3PreparedParameterStableSecondaryPiece Ref hdRef hsRef i r _ (packet.piece r i a) F hF)
      (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
      (domain : Fin Ref.primaryCount → Set (P × M))
      (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref (Function.uncurry F) H V normal domain neighborhood
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
      (baseIndex : Fin Ref.atlas.count × Fin Ref.parameterCount),
    let W := (Ref.parameterChart baseIndex.2).target ×ˢ (univ : Set M)
    (∀ r i (a : packet.s r i),
      ∃ out : Round3PreparedParameterRawPiece Data hd hs (i.1,baseIndex.2) r W
        (fun v : Fin Ref.atlas.count => Ref.atlas.chart v)
        (fun v => (parameterTensorModelEquiv (m+1) d) ⁻¹'
          incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet (v,baseIndex.2)),
        out.choice = ((round3PreparedParameterSecondaryChoice Ref hdRef hsRef i r _ (stable r i a).piece).pullback
          (Ref.parameterChart baseIndex.2)).toNative ∧
        out.Tinv = Tinv ∧ out.Kcut = Kcut ∧ out.Tobs = Tobs ∧
        out.cT = (packet.piece r i a).cT/16 ∧ out.Bnative = 1+Tobs 1) →
    ∀ ell, 0 < ell → ell ≤ 1 → IncrementsOriginalCoordinateEllipticityInputs Data c →
    (∀ n, incrementsOriginalCoreInputProfile Data n ell ≠ ⊤) →
    (∀ n, (incrementsOriginalCoreInputProfile Data n ell).toReal ≤ InputBudget n) →
    ∀ (Β : Type*) [Fintype Β]
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
        (Λ := Fin Ref.primaryCount) (Β := Β) (actualOriginalOpenParameterSlice Data baseIndex)),
    (∀ nu, g.phase nu = fun z : Ep × M => Ref.phase nu ((Ref.parameterChart baseIndex.2).symm z.1,z.2)) →
    (∀ nu, g.cutoff nu = fun z : Ep × M => Ref.cutoff nu ((Ref.parameterChart baseIndex.2).symm z.1,z.2)) →
    ActualOriginalPrimaryPhysicalGeometry (actualOriginalOpenParameterSlice Data baseIndex)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex) g →
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞
      (fun y : Ep × M => actualOriginalOpenParameterSlice Data baseIndex y.1 y.2) W →
    ∃ family : Round3ParameterDependentSecondaryFamily Data Sub
      (actualOriginalOpenParameterSlice Data baseIndex)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex) g q ell W W
      Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D)) (round3ParameterOriginalNativeSamplesAt Data baseIndex.2),
      family.choice = fun r a =>
        ((round3PreparedParameterSecondaryChoice Ref hdRef hsRef a.1 r _ (stable r a.1 a.2).piece).pullback
          (Ref.parameterChart baseIndex.2)).toNative := by
  intro Sub
  letI : ∀ r, Fintype (Sub r) := fun r => inferInstance
  let A := Sigma Sub
  let Mrest := fun j => round3PreparedFiniteMaximum (fun a : A =>
    round3PreparedGeometryCost m d N Tinv ((packet.piece a.1 a.2.1 a.2.2).cT/16) (1+Tobs 1)
      (actualSecondarySolveOrder q j) (j+1) (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c)
  let Cut := fun j => Kcut (actualSecondarySolveOrder q j)
  refine ⟨Mrest,Cut,fun j => round3PreparedFiniteMaximum_nonneg _,fun j => rfl,?_⟩
  intro Mnew hMnew F hF stable H V normal domain neighborhood Data hd hs baseIndex W hRaw ell hell hell1 hEll hFinite hBudget
    Β _ g hPhase hCutoff primaryGeometry hOriginal
  choose raw hChoice hTi hTc hTo hcT hB using hRaw
  let piece := fun r (a : Sub r) => round3Parameter_secondary_raw_piece_reindex
    Data hd hs (a.1.1,baseIndex.2) r W
      (fun v : Fin Ref.atlas.count => Ref.atlas.chart v)
      (fun v => (parameterTensorModelEquiv (m+1) d) ⁻¹'
        incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet (v,baseIndex.2))
      (raw r a.1 a.2) (fun v : Fin Ref.atlas.count × Fin Ref.parameterCount => v.1)
  let physical := fun r (a : Sub r) => round3PreparedParameterSecondaryChoice Ref hdRef hsRef a.1 r _ (stable r a.1 a.2).piece
  let choice := fun r a => ((physical r a).pullback (Ref.parameterChart baseIndex.2)).toNative
  have hChoice' (r) (a : Sub r) : (piece r a).choice = choice r a := hChoice r a.1 a.2
  have hPartCount := round3_prepared_parameter_secondary_stable_partition_count Ref hdRef hsRef theta packet
    hSupport hPart L hCount F hF stable baseIndex.2 baseIndex.1
  have hCarrier (r) (a : Sub r) : (piece r a).carrier = tsupport (choice r a).cutoff ∩
      actualOriginalParameterSupportPair Ref baseIndex r.val.1.1 r.val.1.2 W := by
    rw [(piece r a).carrier_eq,hChoice']
    rfl
  have hPartPieces (r) (y) (hy : y ∈ actualOriginalParameterSupportPair Data baseIndex r.val.1.1 r.val.1.2 W) :
      ∑ a : Sub r, (piece r a).choice.cutoff y = 1 := by
    simp_rw [hChoice']
    exact hPartCount.1 r y hy
  have hCountPieces (r) (y) : (Finset.univ.filter (fun a : Sub r => y ∈ (piece r a).carrier)).card ≤
      L*5^Module.finrank ℝ (Ep × D) := by
    simp_rw [hCarrier]
    exact hPartCount.2 r y
  have hCost (j) (r) (a : Sub r) : round3PreparedGeometryCost m d N (piece r a).Tinv
      (piece r a).cT (piece r a).Bnative (actualSecondarySolveOrder q j) (j+1)
      (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c ≤ Mrest j := by
    change round3PreparedGeometryCost m d N (raw r a.1 a.2).Tinv
      (raw r a.1 a.2).cT (raw r a.1 a.2).Bnative _ _ _ _ ≤ _
    rw [hTi,hcT,hB]
    exact round3PreparedFiniteMaximum_bound (fun aa : A =>
      round3PreparedGeometryCost m d N Tinv ((packet.piece aa.1 aa.2.1 aa.2.2).cT/16) (1+Tobs 1)
        (actualSecondarySolveOrder q j) (j+1) (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c)
      (⟨r,a⟩ : A)
  obtain ⟨family,hFamily⟩ := round3Parameter_dependent_secondary_at_fixed_profiles Data hd hs baseIndex Sub
    (fun _ a => a.1.1) W W piece hPartPieces (L*5^Module.finrank ℝ (Ep × D)) hCountPieces
    q ell c hell hell1 hEll InputBudget hFinite hBudget Mnew Cut Tinv Tobs
    (fun j r a => (hCost j r a).trans (hMnew j))
    (fun j r a => by change (raw r a.1 a.2).Kcut _ ≤ _; rw [hTc])
    (fun k r a => by change (raw r a.1 a.2).Tinv k ≤ _; rw [hTi])
    (fun k r a => by change (raw r a.1 a.2).Tobs k ≤ _; rw [hTo])
    g hPhase hCutoff primaryGeometry hOriginal
  refine ⟨family,hFamily.trans ?_⟩
  funext r a
  exact hChoice' r a

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_dependent_actual_factory
