import Probes.ActualIncrementHessianJets
import Probes.ActualOriginalTransverseInverse

/-!
# Original true-B rows and transverse columns from primitive geometric jets

The finite observation maps below are fixed coordinate maps. Their native
norms stay explicit. The outputs are the original first row of true-B and
the original once-sorted ambient transverse frame, on the same joint domain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

private local instance rowFirstNormed (m N : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowFirstSpace (m N : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowHessianNormed (m N : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowHessianSpace (m N : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowPiNormed (m N : ℕ) : NormedAddCommGroup
    (Fin (m+1) → EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowPiSpace (m N : ℕ) : NormedSpace ℝ
    (Fin (m+1) → EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowFrameNormed (m N : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowFrameSpace (m N : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := inferInstance

def actualIncrementHessianEntry (m N : ℕ) (i j : Fin (m+1)) :
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) →L[ℝ]
        EuclideanSpace ℝ (Fin N) :=
  (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace.single j 1)).comp
    (ContinuousLinearMap.apply ℝ
      (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N))
      (EuclideanSpace.single i 1))

def actualIncrementFirstRows (m N : ℕ) :
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) →L[ℝ]
        (Fin (m+1) → EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.pi fun i => actualIncrementHessianEntry m N 0 i

def actualIncrementTransverseColumns (m N : ℕ) :
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) →L[ℝ]
        (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} →L[ℝ]
          EuclideanSpace ℝ (Fin N)) :=
  ∑ q : {p : Fin m × Fin m // p.1 ≤ p.2},
    ((ContinuousLinearMap.smulRightL ℝ
      (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2})
      (EuclideanSpace ℝ (Fin N))) (EuclideanSpace.proj q)).comp
        (actualIncrementHessianEntry m N q.val.1.succ q.val.2.succ)

theorem actualIncrementTransverseColumns_apply (m N : ℕ)
    (H : EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    actualIncrementTransverseColumns m N H =
      ∑ q : {p : Fin m × Fin m // p.1 ≤ p.2}, (EuclideanSpace.proj q).smulRight
        (H (EuclideanSpace.single q.val.1.succ 1) (EuclideanSpace.single q.val.2.succ 1)) := by
  simp [actualIncrementTransverseColumns, actualIncrementHessianEntry]

def actualIncrementFirstRowsConstant (m N j : ℕ) (c MA MH : ℝ) : ℝ :=
  ‖actualIncrementFirstRows m N‖ * actualIncrementSecondFormConstant m N j c MA MH

def actualIncrementTransverseFrameConstant (m N j : ℕ) (c MA MH : ℝ) : ℝ :=
  ‖actualIncrementTransverseColumns m N‖ * actualIncrementSecondFormConstant m N j c MA MH

theorem actualIncrementFirstRowsConstant_nonneg (m N j : ℕ) {c MA MH : ℝ}
    (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH) :
    0 ≤ actualIncrementFirstRowsConstant m N j c MA MH :=
  mul_nonneg (actualIncrementFirstRows m N).opNorm_nonneg
    (actualIncrementSecondFormConstant_nonneg m N j hc hMA hMH)

theorem actualIncrementTransverseFrameConstant_nonneg (m N j : ℕ) {c MA MH : ℝ}
    (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH) :
    0 ≤ actualIncrementTransverseFrameConstant m N j c MA MH :=
  mul_nonneg (actualIncrementTransverseColumns m N).opNorm_nonneg
    (actualIncrementSecondFormConstant_nonneg m N j hc hMA hMH)

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

section PrimitiveInputs

/-- The actual original first true-B row, including all coordinates at once,
has joint slow jets produced from primitive first/Hessian profiles. -/
theorem actual_increment_first_rows_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (hH : ContDiffOn ℝ ∞ (fun z : X =>
      fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2) O)
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH) :
    ContDiffOn (F := Fin (m+1) → V) ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)) O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv (F := Fin (m+1) → V) ℝ k
      (fun y : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (I := 𝓙) (F y.1) (hF y.1) (e y.1).symm y.2 0 i : V)) z‖ ≤
          actualIncrementFirstRowsConstant m N j c MA MH := by
  let Q : X → D →L[ℝ] D →L[ℝ] V := fun z =>
    actualIncrementPostcomposeHessian D V
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
      (fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2)
  obtain ⟨hQ,hQb⟩ := actual_increment_projected_hessian_slow_jets F hF e he O hO hcoord
    hA hH j ell c MA MH hell hc hMA hMH hreserve hAj hHj
  let L := actualIncrementFirstRows m N
  have hEq : ∀ z ∈ O, (fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)) = L (Q z) := by
    intro z hz
    funext i
    exact actual_increment_secondForm_chart (F z.1) (hF z.1) (e z.1) (he z.1) z.2 (hcoord z hz) 0 i
  refine ⟨(L.contDiff.comp_contDiffOn hQ).congr hEq, ?_⟩
  intro k hk z hz
  have hg : (fun y : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F y.1) (hF y.1) (e y.1).symm y.2 0 i : V)) =ᶠ[𝓝 z] L ∘ Q :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hz) (fun y hy => hEq y hy)
  rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
  exact slow_linear_jet_bound L O hO Q hQ k ell
    (actualIncrementSecondFormConstant m N j c MA MH) hell.le z hz (hQb k hk z hz)

/-- The SAME once-sorted original transverse frame receives its slow-jet
budget from the same actual projected Hessian, not from an assumed frame bound. -/
theorem actual_increment_transverse_frame_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (hH : ContDiffOn ℝ ∞ (fun z : X =>
      fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2) O)
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH) :
    ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeAmbientTransverseFrame (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => incrementsModeAmbientTransverseFrame (I := 𝓙)
        (F y.1) (hF y.1) (e y.1).symm y.2) z‖ ≤
          actualIncrementTransverseFrameConstant m N j c MA MH := by
  let Q : X → D →L[ℝ] D →L[ℝ] V := fun z =>
    actualIncrementPostcomposeHessian D V
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
      (fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2)
  obtain ⟨hQ,hQb⟩ := actual_increment_projected_hessian_slow_jets F hF e he O hO hcoord
    hA hH j ell c MA MH hell hc hMA hMH hreserve hAj hHj
  let L := actualIncrementTransverseColumns m N
  have hEq : ∀ z ∈ O, incrementsModeAmbientTransverseFrame (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2 = L (Q z) := by
    intro z hz
    change _ = actualIncrementTransverseColumns m N (Q z)
    rw [actualIncrementTransverseColumns_apply]
    unfold incrementsModeAmbientTransverseFrame
    apply Finset.sum_congr rfl
    intro q hq
    exact congrArg (fun v : V => (EuclideanSpace.proj q).smulRight v)
      (actual_increment_secondForm_chart (F z.1) (hF z.1) (e z.1) (he z.1) z.2
        (hcoord z hz) q.val.1.succ q.val.2.succ)
  refine ⟨(L.contDiff.comp_contDiffOn hQ).congr hEq, ?_⟩
  intro k hk z hz
  have hg : (fun y : X => incrementsModeAmbientTransverseFrame (I := 𝓙)
      (F y.1) (hF y.1) (e y.1).symm y.2) =ᶠ[𝓝 z] L ∘ Q :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hz) (fun y hy => hEq y hy)
  rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
  exact slow_linear_jet_bound L O hO Q hQ k ell
    (actualIncrementSecondFormConstant m N j c MA MH) hell.le z hz (hQb k hk z hz)

end PrimitiveInputs
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_first_rows_slow_jets
#print axioms GlobalEmbedding.Continuation.actual_increment_transverse_frame_slow_jets
