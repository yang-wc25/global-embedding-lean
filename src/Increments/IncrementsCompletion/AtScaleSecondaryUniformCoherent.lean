import IncrementsCompletion.AtScaleSecondaryUniformDependent
import Repair.FullIncrementNovOpenPhysicalGeometry
import Probes.Round3ParameterSecondaryCommonFamily
import Probes.Round3ParameterSecondaryNoBaseChart

/-! Same coherent physical secondary choice and original carriers, with
numeric costs independent of actual packet and indices once a common genuine
frame reserve is provided by primitive preparation. Only current-scale
positive/cutoff certificates are consumed; no all-scale family is inferred. -/

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
private local instance incrementsPositiveCoherentSignedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem incrementsCompletion_at_scale_uniform_secondary_coherent_factory
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (V0 : Set P) (hPart : ∀ z : P × M, z.1 ∈ V0 → ∑ i, theta i z = 1)
    (L : ℕ) (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (Tinv Kcut Tobs : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hKcut : ∀ k, 0 ≤ Kcut k) (hTobs : ∀ k, 0 ≤ Tobs k)
    (cT0 : ℝ) (hcT0 : 0 < cT0)
    (hMargin : ∀ r i (a : packet.s r i), cT0 ≤ (packet.piece r i a).cT)
    (q : ℕ) (c : ℝ) (InputBudget : ℕ → ℝ) :
    let Sub := fun r => Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(packet.s r i))
    letI : ∀ r, Fintype (Sub r) := fun r => inferInstance
    let Mrest := incrementsCompletionUniformSecondaryGeometryCost m d N Tinv Tobs cT0 q c InputBudget
    let Cut := fun j => Kcut (actualSecondarySolveOrder q j)
    ∀ ell, 0 < ell → ell ≤ 1 →
    IncrementsCompletionAtScaleSecondaryPacketProfiles Data hd hs theta packet ell Tinv Kcut Tobs →
    ∀ Mnew : ℕ → ℝ, (∀ j, Mrest j ≤ Mnew j) →
    ∀ (G : Set (P × M)) (hG : IsOpen G), G ⊆ incrementsOriginalParameterRegion Data →
      (∀ z ∈ G, z.1 ∈ V0) →
    IncrementsOriginalCoordinateEllipticityInputs Data c →
    (∀ n, incrementsOriginalCoreInputProfile Data n ell ≠ ⊤) →
    (∀ n, (incrementsOriginalCoreInputProfile Data n ell).toReal ≤ InputBudget n) →
    ∀ (Β : Type*) [Fintype Β] (primaryHost : Β → Fin Data.atlas.count)
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
        (Λ := Fin Data.primaryCount) (Β := Β) (fullIncrementNovOriginalSourceSlice Data)),
    (∀ nu, g.phase nu = Data.phase nu) → (∀ nu, g.cutoff nu = Data.cutoff nu) →
    (∀ i : Fin Data.atlas.count × Fin Data.parameterCount, Nonempty (ActualOriginalPrimaryPhysicalGeometry
      (fun p => fullIncrementNovOriginalSourceSlice Data ((Data.parameterChart i.2).symm p))
      (fun p => fullIncrementNov_original_source_slice_smooth Data hd hs ((Data.parameterChart i.2).symm p))
      (round3ParameterNativePrimary (fullIncrementNovOriginalSourceSlice Data) g (Data.parameterChart i.2)))) →
    Round3ParameterCoherentSecondaryOutput (SubSecondary := Sigma Sub) Data
      (fullIncrementNovOriginalSourceSlice Data) (fullIncrementNov_original_source_slice_smooth Data hd hs) g
      q ell G Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D))
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) := by
  intro Sub
  letI : ∀ r, Fintype (Sub r) := fun r => inferInstance
  intro Mrest Cut ell hell hell1 profiles Mnew hMnew G hG hGR hGV hEll hFinite hBudget Β _ primaryHost g hPhase hCutoff hPhysical
  let Ti := Tinv
  let To := Tobs
  have hMake := incrementsCompletion_at_scale_uniform_secondary_dependent_factory Data hd hs hImm theta packet
    hSupport V0 hPart L hCount Tinv Kcut Tobs hTinv hKcut hTobs cT0 hcT0 hMargin q c InputBudget ell hell hell1 profiles
  let F := fullIncrementNovOriginalSourceSlice Data
  let hF := fullIncrementNov_original_source_slice_smooth Data hd hs
  apply round3Parameter_secondary_factory_without_base_chart Data primaryHost
    (fun a : Sigma Sub => a.2.1.1) F hF g q ell G Mnew Cut Ti To
    (L*5^Module.finrank ℝ (Ep × D))
    (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet)
  intro spatialBase
  let physical := fun r (a : Sub r) =>
    (round3PreparedParameterSecondaryChoice Data hd hs a.1 r _ (packet.piece r a.1 a.2)).restrictOpen G hG
  let choice := round3ParameterSecondarySigmaChoice Sub (fun _ => Data.atlas.chart spatialBase) physical
  have hPreserves : ∀ r a, Round3ParameterChartPreserves (choice r a).chart := by
    intro r ⟨r',a⟩
    by_cases heq : r'=r
    · subst r'
      simpa only [choice,round3ParameterSecondarySigmaChoice,dite_true] using
        auxBridgeNov_secondary_restriction_preserves
          (round3PreparedParameterSecondaryChoice Data hd hs a.1 r _ (packet.piece r a.1 a.2))
          (round3_prepared_parameter_secondary_preserves Data hd hs a.1 r _ (packet.piece r a.1 a.2)) G hG
    · simpa only [choice,round3ParameterSecondarySigmaChoice,heq,dite_false] using
        round3ParameterSecondaryEmptyChoice_preserves (P := P) (Data.atlas.chart spatialBase)
  have hOne (ip : Fin Data.parameterCount) :
      ∃ family : Round3ParameterPreparedSecondaryFamily (SubSecondary := Sigma Sub) Data
        (fun p => F ((Data.parameterChart ip).symm p)) (fun p => hF ((Data.parameterChart ip).symm p))
        (round3ParameterNativePrimary F g (Data.parameterChart ip)) q ell
        (round3ParameterNativeDomain (Data.parameterChart ip) G) (round3ParameterNativeDomain (Data.parameterChart ip) G)
        Mnew Cut Ti To (L*5^Module.finrank ℝ (Ep × D)) (round3ParameterOriginalNativeSamplesAt Data ip),
        family.choice = round3ParameterNativeChoices choice (Data.parameterChart ip) := by
    let i : Fin Data.atlas.count × Fin Data.parameterCount := (spatialBase,ip)
    let B := Data.parameterChart ip
    let Fn := actualOriginalOpenParameterSlice Data i
    let hFn := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let W := round3ParameterNativeDomain B G
    let gN := round3ParameterNativePrimary F g B
    have hPhaseN (nu) : gN.phase nu = fun z : Ep × M => Data.phase nu (B.symm z.1,z.2) := by
      funext z
      exact congrFun (hPhase nu) (B.symm z.1,z.2)
    have hCutoffN (nu) : gN.cutoff nu = fun z : Ep × M => Data.cutoff nu (B.symm z.1,z.2) := by
      funext z
      exact congrFun (hCutoff nu) (B.symm z.1,z.2)
    obtain ⟨geom⟩ := hPhysical i
    have hOriginal : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞
        (fun y : Ep × M => Fn y.1 y.2) W := by
      have hh := actual_original_parameter_pullback_smooth Data hd ip Data.F
        (incrementsOriginalParameterRegion Data) hs.F_joint W (fun _ hz => hz.1)
        (fun z hz => hGR hz.2)
      apply hh.congr
      intro z hz
      exact congrFun (actualOriginalOpenParameterSlice_eq Data i z.1 (hGR hz.2).1) z.2
    obtain ⟨dep,hDep⟩ := hMake Mnew hMnew G hG hGV i hEll hFinite hBudget
      Β gN hPhaseN hCutoffN geom hOriginal
    let common := round3Parameter_coherent_secondary_common_family Data hd Sub i Fn hFn gN q ell W W
      Mnew Cut Ti To (L*5^Module.finrank ℝ (Ep × D)) (round3ParameterOriginalNativeSamplesAt Data ip)
      B physical dep hDep
    exact ⟨common,rfl⟩
  choose family hFamily using hOne
  exact ⟨choice,hPreserves,family,hFamily⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_uniform_secondary_coherent_factory
