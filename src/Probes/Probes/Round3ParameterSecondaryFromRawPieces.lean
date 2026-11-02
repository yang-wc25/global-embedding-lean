import Probes.Round3ParameterDependentSecondaryFamily
import Probes.Round3PreparedParameterRawPiece
import Probes.Round3PreparedOriginalSamples

/-! Actual prepared pieces feed the complete secondary consumer at profiles
fixed before the current map. Only numerical domination of the primitive
reference profiles is used; every later-order geometry and binding is
constructed here from the actual current original Core. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation

universe uM uP uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

private local instance round3PieceSignedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

def round3ParameterOriginalNativeSamplesAt
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (ip : Fin Data.parameterCount) :
    (Fin Data.atlas.count × Fin Data.parameterCount) → Set X :=
  fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas
    Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (i.1,ip)

theorem round3Parameter_dependent_secondary_at_fixed_profiles
    {Β : Type uPrimary} [Fintype Β]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (Sub : ActualSecondarySignedRecord (Fin Data.primaryCount) → Type uSecondary) [∀ r, Fintype (Sub r)]
    (host : (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) → Sub r → Fin Data.atlas.count)
    (W G : Set (Ep × M))
    (piece : ∀ r a, Round3PreparedParameterRawPiece Data hd hs (host r a,baseIndex.2) r W
      (fun v : Fin Data.atlas.count × Fin Data.parameterCount => Data.atlas.chart v.1)
      (round3ParameterOriginalNativeSamplesAt Data baseIndex.2))
    (hPartition : ∀ r : ActualSecondarySignedRecord (Fin Data.primaryCount), ∀ y,
      y ∈ actualOriginalParameterSupportPair Data baseIndex r.val.1.1 r.val.1.2 W →
        ∑ a : Sub r, (piece r a).choice.cutoff y = 1)
    (Rsecondary : ℕ)
    (hCount : ∀ r y, (Finset.univ.filter (fun a : Sub r => y ∈ (piece r a).carrier)).card ≤ Rsecondary)
    (q : ℕ) (ell c : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (InputBudget : ℕ → ℝ)
    (hFinite : ∀ n, incrementsOriginalCoreInputProfile Data n ell ≠ ⊤)
    (hBudget : ∀ n, (incrementsOriginalCoreInputProfile Data n ell).toReal ≤ InputBudget n)
    (Mrest Kcut Tinv Tobs : ℕ → ℝ)
    (hCost : ∀ j r a, round3PreparedGeometryCost m d N (piece r a).Tinv
      (piece r a).cT (piece r a).Bnative (actualSecondarySolveOrder q j) (j+1)
      (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c ≤ Mrest j)
    (hCutBudget : ∀ j r a, (piece r a).Kcut (actualSecondarySolveOrder q j) ≤ Kcut j)
    (hInvBudget : ∀ k r a, (piece r a).Tinv k ≤ Tinv k)
    (hObsBudget : ∀ k r a, (piece r a).Tobs k ≤ Tobs k)
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) (actualOriginalOpenParameterSlice Data baseIndex))
    (hPhase : ∀ nu, g.phase nu = fun z : Ep × M => Data.phase nu ((Data.parameterChart baseIndex.2).symm z.1,z.2))
    (hCutoff : ∀ nu, g.cutoff nu = fun z : Ep × M => Data.cutoff nu ((Data.parameterChart baseIndex.2).symm z.1,z.2))
    (primaryGeometry : ActualOriginalPrimaryPhysicalGeometry
      (actualOriginalOpenParameterSlice Data baseIndex)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex) g)
    (hOriginal : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
      (fun y : Ep × M => actualOriginalOpenParameterSlice Data baseIndex y.1 y.2) G) :
    ∃ family : Round3ParameterDependentSecondaryFamily Data Sub
        (actualOriginalOpenParameterSlice Data baseIndex)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex) g q ell W G
        Mrest Kcut Tinv Tobs Rsecondary (round3ParameterOriginalNativeSamplesAt Data baseIndex.2),
        family.choice = fun r a => (piece r a).choice := by
  let F := actualOriginalOpenParameterSlice Data baseIndex
  let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex
  let Cost := fun j r a => round3PreparedGeometryCost m d N (piece r a).Tinv
    (piece r a).cT (piece r a).Bnative (actualSecondarySolveOrder q j) (j+1)
    (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c
  have hProduce (j : ℕ) (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (a : Sub r) :
      ∃ out : ActualSecondaryRawGeometry F hF (actualSecondarySolveOrder q j) (j+1) ell (Cost j r a) W,
        out.c = (piece r a).choice.c ∧ out.chart = (piece r a).choice.chart ∧
        out.phase = actualOriginalParameterSignedPhase Data baseIndex r.val ∧
        out.sample = (piece r a).sample ∧ out.support = (piece r a).carrier :=
    (piece r a).produce (actualSecondarySolveOrder q j) (j+1) ell
      (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c hell hell1 hEll (hFinite _) (hBudget _)
  choose raw hc hchart hphase hsample hsupport using hProduce
  let geom := fun j r a => (raw j r a).enlargeBudget
    (hCost j r a)
  have hPairEq (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (ih : Fin Data.atlas.count) :
      actualOriginalParameterSupportPair Data (ih,baseIndex.2) r.val.1.1 r.val.1.2 W =
        incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
          incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2) := by
    simp only [actualOriginalParameterSupportPair,hCutoff]
  have hPhaseEq (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) :
      actualOriginalParameterSignedPhase Data baseIndex r.val = actualOriginalSecondaryPhase F g r.val := by
    rcases r with ⟨⟨⟨nu,mu⟩,branch⟩,hr⟩
    funext y
    simp only [actualOriginalParameterSignedPhase,actualOriginalSecondaryPhase,hPhase]
  have hGeomC (j : ℕ) (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (a : Sub r) :
      (geom j r a).c = (piece r a).choice.c := hc j r a
  have hGeomChart (j : ℕ) (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (a : Sub r) :
      (geom j r a).chart = (piece r a).choice.chart := hchart j r a
  have hGeomSample (j : ℕ) (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (a : Sub r) :
      (geom j r a).sample = (piece r a).sample := hsample j r a
  have hGeomSupport (j : ℕ) (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (a : Sub r) :
      (geom j r a).support = (piece r a).carrier := hsupport j r a
  let dep : Round3ParameterDependentSecondaryFamily Data Sub F hF g q ell W G
      Mrest Kcut Tinv Tobs Rsecondary (round3ParameterOriginalNativeSamplesAt Data baseIndex.2) := {
    choice := fun r a => (piece r a).choice
    geometry := geom
    hCoordinate := hGeomC
    hChart := hGeomChart
    hPhase := fun j r a => (hphase j r a).trans (hPhaseEq r)
    hHost := by
      intro r a
      rw [(piece r a).host_eq]
      exact contMDiffOn_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem (host r a))
    hHostInv := by
      intro r a
      rw [(piece r a).host_eq]
      exact contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem (host r a))
    hHostSource := by
      intro j r a
      rw [hGeomChart]
      exact (piece r a).host_source
    hSupport := by
      intro j r a
      rw [hGeomSupport,← hPairEq r (host r a)]
      exact (piece r a).support
    hPair := by
      intro j r a
      rw [hGeomSupport,← hPairEq r (host r a)]
      exact (piece r a).pair
    hPartition := by
      intro r y hy
      exact hPartition r y ((hPairEq r baseIndex.1).symm ▸ hy)
    hCut := by
      intro j r a
      dsimp only
      rw [hGeomChart]
      exact (piece r a).cut_smooth
    hInv := by
      intro j r a
      dsimp only
      rw [hGeomChart]
      exact (piece r a).inv_smooth
    hCutJets := by
      intro j r a
      dsimp only
      rw [hGeomChart,hGeomSample]
      intro k hk z hz
      exact ((piece r a).cut_jets ell hell.le hell1 (actualSecondarySolveOrder q j) k hk z hz).trans
        (hCutBudget j r a)
    hInvJets := by
      intro j r a
      dsimp only
      rw [hGeomChart,hGeomSample]
      intro k hk hkj z hz
      exact ((piece r a).inv_jets ell hell.le hell1 k z hz).trans
        (hInvBudget k r a)
    hostIndex := fun r a => (host r a,baseIndex.2)
    hHostIndex := fun r a => (piece r a).host_eq
    hNativeSamples := by
      intro j r a
      dsimp only
      rw [hGeomChart,hGeomSample]
      exact (piece r a).host_samples
    primaryGeometry := primaryGeometry
    hOriginal := hOriginal
    hChartInv := by
      intro j r a
      rw [hGeomChart]
      exact (piece r a).chart_inverse_smooth
    hObserverNativeSamples := by
      intro j v r a z hz
      rw [hGeomChart,hGeomSample]
      rw [hGeomSupport] at hz
      exact (piece r a).observer_samples v z hz
    hObserverJets := by
      intro j v r a z hz k hk hkj
      rw [hGeomChart]
      rw [hGeomSupport] at hz
      exact ((piece r a).observer_jets ell hell.le hell1 v z hz k).trans
        (hObsBudget k r a)
    hObserverCount := by
      intro j v r z hz
      simp only [hGeomSupport]
      exact hCount r _ }
  exact ⟨dep,rfl⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3Parameter_dependent_secondary_at_fixed_profiles
