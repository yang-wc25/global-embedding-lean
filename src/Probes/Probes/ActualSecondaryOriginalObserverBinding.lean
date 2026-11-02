import Probes.ActualSecondaryOriginalForcingSupport
import Probes.ActualSecondaryObservedForcingBinding
import Probes.ActualIncrementQuadraticLocalizationInvariant

/-! The SAME host-defined secondary h-fields satisfy the actual forcing
binding in every subsequent observation chart. Ordinary partitions are only
used on the genuine primary pair, and cutoff support is only asserted inside
the actual target of the observation chart. No observed forcing identity or
quadratic support condition is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Label SubPrimary SubSecondary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

 def actual_original_secondary_observer_binding
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (n j q : ℕ) (hq : 1 ≤ q) (ell Mg CH tau delta : ℝ) (htau : 0 < tau)
    (r : (Label × Label) × Fin 4)
    (data : SubSecondary → ActualSecondaryPieceData F hF n j ell Mg CH delta W)
    (host : SubSecondary → OpenPartialHomeomorph M D)
    (hHost : ∀ a, ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ (host a) (host a).source)
    (hHostInv : ∀ a, ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ (host a).symm (host a).target)
    (hHostSource : ∀ a y, y ∈ (data a).chart.source → y.2 ∈ (host a).source)
    (rho : SubSecondary → Ep × M → ℝ)
    (hRho : ∀ a, tsupport (fun y : W => rho a y.val) ∩
      Subtype.val ⁻¹' (incrementsGlobalRelativeSupport W (g.cutoff r.1.1) ∩
        incrementsGlobalRelativeSupport W (g.cutoff r.1.2)) ⊆ Subtype.val ⁻¹' (data a).chart.source)
    (hPartition : ∀ y, y ∈ incrementsGlobalRelativeSupport W (g.cutoff r.1.1) ∩
        incrementsGlobalRelativeSupport W (g.cutoff r.1.2) → ∑ a, rho a y = 1)
    (hPhase : ∀ a, (data a).phase = actualOriginalSecondaryPhase F g r)
    (hReal : ∀ a, (data a).hR =
      actualSecondaryInverseForcing (((OpenPartialHomeomorph.refl Ep).prod (host a)).symm.trans (data a).chart)
        (rho a ∘ ((OpenPartialHomeomorph.refl Ep).prod (host a)).symm)
        (fun z => actualRealTensorAssembly (actualOriginalSecondaryQuadratic F hF g input (q+2) tau delta (host a) r z)))
    (hImag : ∀ a, (data a).hI =
      actualSecondaryInverseForcing (((OpenPartialHomeomorph.refl Ep).prod (host a)).symm.trans (data a).chart)
        (rho a ∘ ((OpenPartialHomeomorph.refl Ep).prod (host a)).symm)
        (fun z => actualImaginaryTensorAssembly (actualOriginalSecondaryQuadratic F hF g input (q+2) tau delta (host a) r z)))
    (e : OpenPartialHomeomorph M D)
    (he : ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ e e.source)
    (heInv : ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ e.symm e.target)
    (hTransition : ∀ a, ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data a).chart)
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data a).chart).source)
    (hInverse : ∀ a, ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data a).chart).symm
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data a).chart).target) :
    let b := (OpenPartialHomeomorph.refl Ep).prod e
    let H := actualOriginalSecondaryQuadratic F hF g input (q+2) tau delta e r
    ActualSecondaryForcingBinding F hF data b
      (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
      (fun z => actualOriginalSecondaryPhase F g r (b.symm z)) := by
  intro b H
  let cutoff := fun a => rho a ∘ b.symm
  have hCov (a : SubSecondary) :=
    actual_original_quadratic_localization_observer_independent F hF g input W primary h (q+2) tau delta
      (host a) e (hHost a) (hHostInv a) he heInv (data a).chart (hHostSource a)
      (data a).source_domain (hInverse a) (rho a) r.1.1 r.1.2 r.2
  refine {
    cutoff := cutoff
    transition := hTransition
    inverseTransition := hInverse
    first := ?_
    cutoffSupport := ?_
    adaptation := ?_
    realForcing := ?_
    imagForcing := ?_
    partition := ?_ }
  · intro a z hz
    have hh := (actual_secondary_piece_chart_coordinates F hF (data a) (b.symm z) hz.2).1
    exact hh
  · intro a z hz hzW hn hactive
    refine ⟨hz,?_⟩
    change b.symm z ∈ (data a).chart.source
    exact hRho a ⟨subset_tsupport (fun y : W => rho a y.val)
      (show (⟨b.symm z,hzW⟩ : W) ∈ Function.support (fun y : W => rho a y.val) from hn),
      actual_original_quadratic_forcing_active_pair F hF g input W primary h q hq tau delta htau
        e he heInv z hz.2 hzW r hactive⟩
  · intro a z hz
    change ((data a).chart (b.symm z)).2 0 = _
    rw [← (data a).adaptation (b.symm z) hz.2,hPhase a]
  · intro a
    rw [hReal a]
    exact (hCov a).1
  · intro a
    rw [hImag a]
    exact (hCov a).2
  · intro z hz hzW hactive
    exact hPartition (b.symm z)
      (actual_original_quadratic_forcing_active_pair F hF g input W primary h q hq tau delta htau
        e he heInv z hz.2 hzW r hactive)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_secondary_observer_binding
