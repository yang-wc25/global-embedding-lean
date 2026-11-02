import Probes.ActualIncrementGoodPhaseGeometry
import Probes.ActualProbeNormalSource
import GlobalEmbedding.Paper.IncrementsOriginalQualitativeAdmissibility

/-! The ORIGINAL phase-kernel free-normal condition supplies the actual
chosen-chart beta kernel. This is an algebraic bridge through the literal
adapted phase derivative, so it retains the given normal and both original
paired-probe signs. No normal, kernel identity or geometric carrier is chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

/-- The same normal annihilates every coordinate transverse column when it
annihilates the actual second form on the transported first-coordinate kernel. -/
theorem actual_increment_transverse_kernel_of_chart_free
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (chart : OpenPartialHomeomorph M D) (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ chart.target)
    (xi : TangentSpace 𝓙 (chart.symm x) →L[ℝ] ℝ)
    (hxi : xi = (EuclideanSpace.proj 0).comp (mfderiv 𝓙 𝓙 chart (chart.symm x)))
    (normal : normalSpace (I := 𝓙) F (chart.symm x))
    (hfree : ∀ u v : xi.ker, inner ℝ
      ((trueSecondForm F hF (chart.symm x)
        (symmetricSquareProduct (TangentSpace 𝓙 (chart.symm x)) u.val v.val)) : V)
      (normal : V) = 0) :
    incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart.symm x a.succ) normal = 0 := by
  let A : D →L[ℝ] TangentSpace 𝓙 (chart.symm x) := mfderiv 𝓙 𝓙 chart.symm x
  let H : TangentSpace 𝓙 (chart.symm x) →L[ℝ] D := mfderiv 𝓙 𝓙 chart (chart.symm x)
  have hHA : H.comp A = ContinuousLinearMap.id ℝ D :=
    (actual_increment_maximal_chart_mdifferentiable chart hchart).comp_symm_deriv hx
  have hdir (a : Fin m) :
      xi (incrementsModeCoordinateDirections chart.symm x a.succ) = 0 := by
    rw [hxi]
    change (H.comp A) (EuclideanSpace.single a.succ 1) 0 = 0
    rw [hHA]
    simp
  ext q
  rw [incrementsTransversePairing_apply]
  exact hfree ⟨incrementsModeCoordinateDirections chart.symm x q.val.1.succ,hdir q.val.1⟩
    ⟨incrementsModeCoordinateDirections chart.symm x q.val.2.succ,hdir q.val.2⟩

/-- Original freedom on ker(d psi) becomes beta freedom in the SAME genuinely
adapted maximal chart. No extra Riemannian tangent structure is required. -/
theorem actual_increment_transverse_kernel_of_phase_free
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (psi : M → ℝ) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target) (x : D) (hx : x ∈ O)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) psi (chart.symm x))
    (hadapt : ∀ z ∈ O, psi (chart.symm z) = z 0)
    (normal : normalSpace (I := 𝓙) F (chart.symm x))
    (hfree :
      let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (chart.symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (chart.symm x))
      ∀ u v : xi.ker, inner ℝ
        ((trueSecondForm F hF (chart.symm x)
          (symmetricSquareProduct (TangentSpace 𝓙 (chart.symm x)) u.val v.val)) : V)
        (normal : V) = 0) :
    incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart.symm x a.succ) normal = 0 :=
  actual_increment_transverse_kernel_of_chart_free F hF chart hchart x (hOt hx) _
    (actual_increment_phaseCovector_eq_chosen_chart psi chart hchart O hO hOt x hx hpsi hadapt)
    normal hfree

section Original
variable {d : ℕ} {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- The frozen original free-normal condition discharges the beta-kernel input
for its actual source slice and actual adapted chart. The normal is the literal
original given Euclidean vector, included using its original normal condition. -/
theorem actual_original_free_normal_transverse_kernel
    (data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
    (hn : IncrementsOriginalFreeNormalConditions data hd hs) (nu : Fin data.primaryCount)
    (p : P) (hp : p ∈ data.parameterOpen)
    (chart : OpenPartialHomeomorph M D) (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target)
    (hmap : ∀ z ∈ O, (p,chart.symm z) ∈ data.primaryDomain nu)
    (hadapt : ∀ z ∈ O, data.phase nu (p,chart.symm z) = z 0)
    (x : D) (hx : x ∈ O) :
    let F := fun y => data.F (p,y)
    let hF := incrementsOriginal_slice_contMDiff data hd hs p hp
    let hactive : (p,chart.symm x) ∈ data.primaryDomain nu ∩ incrementsOriginalParameterRegion data :=
      ⟨hmap x hx,⟨hp,Set.mem_univ _⟩⟩
    let normal : normalSpace (I := 𝓙) F (chart.symm x) :=
      ⟨data.freeNormal nu (p,chart.symm x),hn.normal nu (p,chart.symm x) hactive⟩
    incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart.symm x a.succ) normal = 0 := by
  intro F hF hactive normal
  have hopen : IsOpen (data.primaryDomain nu ∩ incrementsOriginalParameterRegion data) :=
    (hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ)
  have hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (fun y => data.phase nu (p,y)) (chart.symm x) := by
    have hj := (hs.phase_joint nu).contMDiffAt (hopen.mem_nhds hactive)
    exact (hj.comp (chart.symm x) (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  apply actual_increment_transverse_kernel_of_phase_free F hF (fun y => data.phase nu (p,y))
    chart hchart O hO hOt x hx hpsi hadapt normal
  exact hn.free nu (p,chart.symm x) hactive

end Original

section Amplitude
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

/-- The exact negative prescribed probe amplitude preserves the same beta
kernel. Real and negative-real sine/cosine multipliers require no sign choice. -/
theorem actual_probe_normal_amplitude_transverse_kernel
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (chart : Ep → D → M) (chi : Ep × D → ℝ)
    (normal : (b : Ep) → (x : D) → normalSpace (I := 𝓙) (F b) (chart b x))
    (delta tau lambda : ℝ) (b : Ep) (x : D)
    (hn : incrementsTransversePairing (F b) (hF b) (chart b x)
      (fun a : Fin m => incrementsModeCoordinateDirections (chart b) x a.succ) (normal b x) = 0)
    (s : ℝ) :
    incrementsTransversePairing (F b) (hF b) (chart b x)
      (fun a : Fin m => incrementsModeCoordinateDirections (chart b) x a.succ)
      (s • actualProbeNormalAmplitude F chart chi normal delta tau lambda b x) = 0 := by
  simp only [actualProbeNormalAmplitude,map_smul,hn,smul_zero]

end Amplitude
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_transverse_kernel_of_chart_free
#print axioms GlobalEmbedding.Continuation.actual_increment_transverse_kernel_of_phase_free
#print axioms GlobalEmbedding.Continuation.actual_original_free_normal_transverse_kernel
#print axioms GlobalEmbedding.Continuation.actual_probe_normal_amplitude_transverse_kernel
