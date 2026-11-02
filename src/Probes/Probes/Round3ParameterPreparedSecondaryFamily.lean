import Probes.ActualUniformSmoothedOriginalJointPair

/-! General original parameter data supply this native primitive family.
Its native choice must be identified with one physical choice by the
coherent common-family constructor; no global Ep cutoff smoothness is asked.

The complete secondary preparation of one actual increment.
There is one choice, one host assignment, and one geometry family. Both the
j and j+1 consumers use projections of this same object. Construction is
provided by the signed-host/refinement factory, not by assuming the later
wave, forcing, increment or repair estimates. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
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

structure Round3ParameterPreparedSecondaryFamily
    {Β : Type uPrimary} {SubSecondary : Type uSecondary} [Fintype Β] [Fintype SubSecondary]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q : ℕ) (ell : ℝ) (W G : Set (Ep × M))
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (NativeSamples : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X) where
  choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
    ActualOriginalSecondaryChoice Ep M m
  geometry : ∀ j, ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
    ActualSecondaryRawGeometry F hF (actualSecondarySolveOrder q j) (j+1) ell (Mrest j) W
  hCoordinate : ∀ j r a, (geometry j r a).c = (choice r a).c
  hChart : ∀ j r a, (geometry j r a).chart = (choice r a).chart
  hPhase : ∀ j r a, (geometry j r a).phase = actualOriginalSecondaryPhase F g r.val
  hHost : ∀ r a, ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ (choice r a).host (choice r a).host.source
  hHostInv : ∀ r a, ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ (choice r a).host.symm (choice r a).host.target
  hHostSource : ∀ j r a, (geometry j r a).chart.source ⊆
    ((OpenPartialHomeomorph.refl Ep).prod (choice r a).host).source
  hSupport : ∀ j r a, tsupport (fun y : W => (choice r a).cutoff y.val) ∩
    Subtype.val ⁻¹' (incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
      incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2)) ⊆
    Subtype.val ⁻¹' (geometry j r a).support
  hPair : ∀ j r a, (geometry j r a).support ⊆
    incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
      incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2)
  hPartition : ∀ r : ActualSecondarySignedRecord (Fin Data.primaryCount), ∀ y,
    y ∈ incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
      incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2) → ∑ a, (choice r a).cutoff y = 1
  hCut : ∀ j r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
    ContDiffOn ℝ ∞ ((choice r a).cutoff ∘ b.symm) (b.symm.trans (geometry j r a).chart).source
  hInv : ∀ j r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
    ContDiffOn ℝ ∞ (b.symm.trans (geometry j r a).chart).symm (b.symm.trans (geometry j r a).chart).target
  hCutJets : ∀ j r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
    ∀ k ≤ actualSecondarySolveOrder q j, ∀ z ∈ (geometry j r a).sample,
      ell^k*‖iteratedFDeriv ℝ k ((choice r a).cutoff ∘ b.symm)
        ((b.symm.trans (geometry j r a).chart).symm z)‖ ≤ Kcut j
  hInvJets : ∀ j r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
    ∀ k, 1 ≤ k → k ≤ actualSecondarySolveOrder q j+1 → ∀ z ∈ (geometry j r a).sample,
      ell^(k-1)*‖iteratedFDeriv ℝ k (b.symm.trans (geometry j r a).chart).symm z‖ ≤ Tinv k
  hostIndex : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
    (Fin Data.atlas.count × Fin Data.parameterCount)
  hHostIndex : ∀ r a, (choice r a).host = Data.atlas.chart (hostIndex r a).1
  hNativeSamples : ∀ j r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
    (b.symm.trans (geometry j r a).chart).symm '' (geometry j r a).sample ⊆ NativeSamples (hostIndex r a)
  primaryGeometry : ActualOriginalPrimaryPhysicalGeometry F hF g
  hOriginal : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (fun y : Ep × M => F y.1 y.2) G
  hChartInv : ∀ j r a, ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
    (geometry j r a).chart.symm (geometry j r a).chart.target
  hObserverNativeSamples : ∀ j i r a z,
    z ∈ NativeSamples i ∩ (fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2)) ⁻¹'
      (geometry j r a).support →
    (geometry j r a).chart (z.1,(Data.atlas.chart i.1).symm z.2) ∈ (geometry j r a).sample
  hObserverJets : ∀ j i r a z,
    z ∈ NativeSamples i ∩ (fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2)) ⁻¹'
      (geometry j r a).support →
    ∀ k, 1 ≤ k → k ≤ j+2 → ell^(k-1)*‖iteratedFDeriv ℝ k
      ((geometry j r a).chart ∘ (fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2))) z‖ ≤ Tobs k
  hObserverCount : ∀ j i (r : ActualSecondarySignedRecord (Fin Data.primaryCount)), ∀ z ∈ NativeSamples i,
    (Finset.univ.filter (fun a => (z.1,(Data.atlas.chart i.1).symm z.2) ∈
      (geometry j r a).support)).card ≤ Rsecondary

end GlobalEmbedding.Continuation
