import NormalPolar.JointMixedQuadraticLocalization
import NormalPolar.JointSecondaryProfiles
import NormalPolar.ActualRepairModelFirstDefectQuadraticSupport
import Probes.ActualSecondaryObservedForcingBinding

/-! The host-defined same common-array forcing satisfies the actual forcing
binding in every original maximal observation chart. The ordinary partition
is required only on its genuine two-label carrier; all observed identities
are proved from the same host h-fields, not supplied as new fields. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M Ep Label SubSecondary : Type*} {m N : ℕ}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

def jointMixed_observer_binding
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (phase : Label → Ep × M → ℝ) (R Q : Label → Ep × M → V)
    (W : Set (Ep × M)) (hW : IsOpen W) (K : Label → Set (Ep × M))
    (hRsupport : ∀ l, tsupport (fun z : W => R l z) ⊆ Subtype.val ⁻¹' K l)
    (hQsupport : ∀ l, tsupport (fun z : W => Q l z) ⊆ Subtype.val ⁻¹' K l)
    (n j : ℕ) (ell Mg CH tau delta : ℝ) (rec : (Label × Label) × Fin 4)
    (data : SubSecondary → ActualSecondaryPieceData F hF n j ell Mg CH delta W)
    (host : SubSecondary → OpenPartialHomeomorph M D)
    (hHost : ∀ a, host a ∈ maximalAtlas IM ∞ M)
    (hHostSource : ∀ a y, y ∈ (data a).chart.source → y.2 ∈ (host a).source)
    (rho : SubSecondary → Ep × M → ℝ)
    (hRho : ∀ a, tsupport (fun y : W => rho a y.val) ∩
      Subtype.val ⁻¹' (K rec.1.1 ∩ K rec.1.2) ⊆ Subtype.val ⁻¹' (data a).chart.source)
    (hPartition : ∀ y ∈ K rec.1.1 ∩ K rec.1.2, ∑ a, rho a y = 1)
    (hPhase : ∀ a, (data a).phase = jointSecondarySignedPhase phase rec)
    (hReal : ∀ a, (data a).hR =
      actualSecondaryInverseForcing (((OpenPartialHomeomorph.refl Ep).prod (host a)).symm.trans (data a).chart)
        (rho a ∘ ((OpenPartialHomeomorph.refl Ep).prod (host a)).symm)
        (fun z => actualRealTensorAssembly (actualParameterPrimaryQuadratic phase R Q tau (host a) rec z)))
    (hImag : ∀ a, (data a).hI =
      actualSecondaryInverseForcing (((OpenPartialHomeomorph.refl Ep).prod (host a)).symm.trans (data a).chart)
        (rho a ∘ ((OpenPartialHomeomorph.refl Ep).prod (host a)).symm)
        (fun z => actualImaginaryTensorAssembly (actualParameterPrimaryQuadratic phase R Q tau (host a) rec z)))
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (hTransition : ∀ a, ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data a).chart)
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data a).chart).source)
    (hInverse : ∀ a, ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data a).chart).symm
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data a).chart).target) :
    let b := (OpenPartialHomeomorph.refl Ep).prod e
    let H := actualParameterPrimaryQuadratic phase R Q tau e rec
    ActualSecondaryForcingBinding F hF data b
      (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
      (fun z => jointSecondarySignedPhase phase rec (b.symm z)) := by
  intro b H
  let cutoff := fun a => rho a ∘ b.symm
  have hCov (a : SubSecondary) := jointMixed_quadratic_localization_observer_independent
    phase R Q tau (host a) e (hHost a) he (data a).chart (hHostSource a)
    (hInverse a) (rho a) rec.1.1 rec.1.2 rec.2
  have hactive (z : X) (hz : z ∈ b.target) (hzW : b.symm z ∈ W)
      (hn : actualRealTensorAssembly (H z) ≠ 0 ∨ actualImaginaryTensorAssembly (H z) ≠ 0) :
      b.symm z ∈ K rec.1.1 ∩ K rec.1.2 := by
    exact actualRepairModelFirstDefect_quadratic_active_pair_of_amplitudes phase tau R Q W hW K
      hRsupport hQsupport (fun z : X => (z.1,e.symm z.2)) z
      (b.symm.continuousOn.continuousAt (b.open_target.mem_nhds hz)) hzW rec.1.1 rec.1.2 rec.2 hn
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
    exact (actual_secondary_piece_chart_coordinates F hF (data a) (b.symm z) hz.2).1
  · intro a z hz hzW hn ha
    refine ⟨hz,?_⟩
    exact hRho a ⟨subset_tsupport (fun y : W => rho a y.val)
      (show (⟨b.symm z,hzW⟩ : W) ∈ Function.support (fun y : W => rho a y.val) from hn),
      hactive z hz hzW ha⟩
  · intro a z hz
    change ((data a).chart (b.symm z)).2 0 = _
    rw [← (data a).adaptation (b.symm z) hz.2,hPhase a]
  · intro a
    rw [hReal a]
    exact (hCov a).1
  · intro a
    rw [hImag a]
    exact (hCov a).2
  · intro z hz hzW ha
    exact hPartition (b.symm z) (hactive z hz hzW ha)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_observer_binding

