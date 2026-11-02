import Probes.ActualIncrementComplexCoefficientJets
import Probes.ActualIncrementPhysicalChartRows

/-!
# Actual coefficient regularity on the chosen maximal chart

This qualitative producer starts from the original smooth map and genuine
immersion/transverse Gram conditions. It derives every coefficient regularity
needed to differentiate the actual secondary reconstruction. No coefficient
regularity or finite derivative budget is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ P
local notation "Cdata" => Fin (m+1) → ℂ
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

private local instance regularityDDNormed : NormedAddCommGroup (D →L[ℝ] D) := inferInstance
private local instance regularityDDSpace : NormedSpace ℝ (D →L[ℝ] D) := inferInstance
private local instance regularityDVNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance regularityDVSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance regularityANormed : NormedAddCommGroup ((D →L[ℝ] D) →L[ℝ] D) := inferInstance
private local instance regularityASpace : NormedSpace ℝ ((D →L[ℝ] D) →L[ℝ] D) := inferInstance
private local instance regularityDCNormed : NormedAddCommGroup (D →L[ℝ] Cdata) := inferInstance
private local instance regularityDCSpace : NormedSpace ℝ (D →L[ℝ] Cdata) := inferInstance
private local instance regularityCANormed : NormedAddCommGroup ((D →L[ℝ] Cdata) →L[ℝ] Cdata) := inferInstance
private local instance regularityCASpace : NormedSpace ℝ ((D →L[ℝ] Cdata) →L[ℝ] Cdata) := inferInstance

/-- Genuine original geometry in the chosen maximal chart supplies all
source and reconstruction coefficient regularity for the actual mode. -/
theorem actual_increment_chosen_chart_coefficients_contDiffOn
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target)
    (hinj : ∀ z ∈ O, Function.Injective (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm z)))
    (hfree : ∀ z ∈ O,
      let beta := incrementsTransversePairing F hF (chart.symm z)
        (fun a : Fin m => incrementsModeCoordinateDirections chart.symm z a.succ)
      (beta.comp beta.adjoint).IsInvertible) :
    ContDiffOn (F := Fin (m+1) → V) ℝ ∞
      (fun z i => (incrementsModeSecondForm F hF chart.symm z 0 i : V)) O ∧
    ContDiffOn ℝ ∞ (fun z => (normalSpace (I := 𝓙) F (chart.symm z)).subtypeL.comp
      (incrementsModeCoordinateJ F hF chart.symm z)) O ∧
    ContDiffOn ℝ ∞ (incrementsModeTransverseValue F chart.symm) O ∧
    ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF chart.symm) O ∧
    ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF chart.symm) O := by
  let c : D → M := chart.symm
  have hFc : ContDiffOn ℝ ∞ (F ∘ c) O :=
    ((hF.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hchart)).contDiffOn).mono hOt
  have hD := hFc.fderiv_of_isOpen hO (m := ∞) (by simp)
  have hDD := hD.fderiv_of_isOpen hO (m := ∞) (by simp)
  have hi : ∀ z ∈ O, Function.Injective (fderiv ℝ (F ∘ c) z) := by
    intro z hz
    exact actual_increment_chart_derivative_injective F hF chart hchart z (hOt hz) (hinj z hz)
  have hP : ContDiffOn ℝ ∞ (fun z => (normalSpace (I := 𝓙) F (c z)).starProjection) O := by
    apply (smooth_frame_normal_projection _ hD hi).congr
    intro z hz
    rw [actual_increment_normalSpace_eq_chart_range F hF chart hchart z (hOt hz)]
  have hB (i j : Fin (m+1)) : ContDiffOn ℝ ∞
      (fun z => (incrementsModeSecondForm F hF c z i j : V)) O := by
    have hH := (hDD.clm_apply (contDiffOn_const (c := EuclideanSpace.single i 1))).clm_apply
      (contDiffOn_const (c := EuclideanSpace.single j 1))
    apply (hP.clm_apply hH).congr
    intro z hz
    exact actual_increment_secondForm_chart F hF chart hchart z (hOt hz) i j
  have hGamma (i j : Fin (m+1)) : ContDiffOn ℝ ∞
      (fun z => incrementsModeGamma F c z i j) O := by
    have hG := (smooth_frame_gram_coefficients _ hD.contMDiffOn hi).contDiffOn
    have hH := (hDD.clm_apply (contDiffOn_const (c := EuclideanSpace.single i 1))).clm_apply
      (contDiffOn_const (c := EuclideanSpace.single j 1))
    exact hG.clm_apply hH
  have hBR : ContDiffOn (F := Fin (m+1) → V) ℝ ∞
      (fun z i => (incrementsModeSecondForm F hF c z 0 i : V)) O :=
    contDiffOn_pi.mpr fun i => hB 0 i
  have hFrame : ContDiffOn ℝ ∞ (incrementsModeAmbientTransverseFrame F hF c) O := by
    apply contDiffOn_clm_apply.mpr
    intro t
    have hsum : ContDiffOn ℝ ∞ (fun z => ∑ q : P,
        t q • (incrementsModeSecondForm F hF c z q.val.1.succ q.val.2.succ : V)) O :=
      ContDiffOn.sum fun q _ => (hB q.val.1.succ q.val.2.succ).const_smul (t q)
    simpa [incrementsModeAmbientTransverseFrame] using hsum
  have hFI : ∀ z ∈ O, Function.Injective (incrementsModeAmbientTransverseFrame F hF c z) := by
    intro z hz
    exact incrementsModeAmbientTransverseFrame_injective F hF c z (hfree z hz)
  have hJ : ContDiffOn ℝ ∞ (fun z => (normalSpace (I := 𝓙) F (c z)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c z)) O := by
    apply ((freeGramRightInverse_contMDiffOn (I := 𝓙) _ hFrame.contMDiffOn hFI).contDiffOn).congr
    intro z hz
    exact incrementsModeCoordinateJ_ambient F hF c z
  have hT : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O := by
    apply contDiffOn_clm_apply.mpr
    intro u
    have hr : ContDiffOn (F := P → ℝ) ℝ ∞ (fun z q =>
        -inner ℝ (incrementsModeGamma F c z q.val.1.succ q.val.2.succ) u) O :=
      contDiffOn_pi.mpr fun q => ((hGamma q.val.1.succ q.val.2.succ).inner ℝ contDiffOn_const).neg
    exact (EuclideanSpace.equiv P ℝ).symm.contDiff.comp_contDiffOn hr
  let Rows := fun z i => (incrementsModeSecondForm F hF c z 0 i : V)
  let J := fun z => (normalSpace (I := 𝓙) F (c z)).subtypeL.comp (incrementsModeCoordinateJ F hF c z)
  let Z := fun z => (actualIncrementFullRowPairing m N (Rows z)).comp (J z)
  have hZ : ContDiffOn ℝ ∞ Z O :=
    ((actualIncrementFullRowPairing m N).contDiff.comp_contDiffOn hBR).clm_comp hJ
  have hAR : ContDiffOn ℝ ∞ (incrementsModeFirstOrderA F hF c) O := by
    apply (contDiffOn_const.sub (hZ.clm_comp (contDiffOn_const (c := incrementsModeTransverseJet)))).congr
    intro z hz
    exact actual_increment_first_order_A_eq F hF c z
  have hGR : ContDiffOn (F := Fin (m+1) → D) ℝ ∞ (fun z i => incrementsModeGamma F c z 0 i) O :=
    contDiffOn_pi.mpr fun i => hGamma 0 i
  have hBRreal : ContDiffOn ℝ ∞ (incrementsModeFirstOrderB F hF c) O := by
    have hG := (actualIncrementFullRowPairing m (m+1)).contDiff.comp_contDiffOn hGR
    apply (hG.neg.sub (hZ.clm_comp hT)).congr
    intro z hz
    exact actual_increment_first_order_B_eq F hF c z
  refine ⟨hBR,hJ,hT,?_,?_⟩
  · apply ((actualIncrementComplexAMap m).contDiff.comp_contDiffOn hAR).congr
    intro z hz
    exact actual_increment_complex_A_eq F hF chart z
  · apply ((actualIncrementComplexBMap m).contDiff.comp_contDiffOn hBRreal).congr
    intro z hz
    exact actual_increment_complex_B_eq F hF chart z

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_chosen_chart_coefficients_contDiffOn
