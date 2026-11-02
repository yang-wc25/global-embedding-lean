import Repair.IncrementActualSignedTransport
import Repair.ReferenceSignedPhaseJets
import Repair.ReferenceSlicePhases

/-! Exact differentials of the literal four signed physical phases.
The dominant term is differentiated through its real chart inverse;
the foreign term uses the genuine chart transition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "I" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

def incrementLiteralSignedPhase
    (left right : OpenPartialHomeomorph M D) (xi eta : D →L[ℝ] ℝ)
    (leftWeight rightWeight : ℝ) (branch : Fin 4) (x : M) : ℝ :=
  let l := leftWeight*xi (left x)
  let r := rightWeight*eta (right x)
  ![l+r,l-r,-l+r,-l-r] branch

theorem increment_literal_signed_differential
    (left right : OpenPartialHomeomorph M D)
    (hLeft : left ∈ IsManifold.maximalAtlas I ∞ M)
    (hRight : right ∈ IsManifold.maximalAtlas I ∞ M)
    (xi eta : D →L[ℝ] ℝ) (leftWeight rightWeight : ℝ)
    (x : M) (hxLeft : x ∈ left.source) (hxRight : x ∈ right.source)
    (branch : Fin 4) :
    DifferentiableAt ℝ (incrementLiteralSignedPhase left right xi eta leftWeight rightWeight branch ∘ left.symm) (left x) ∧
      fderiv ℝ (incrementLiteralSignedPhase left right xi eta leftWeight rightWeight branch ∘ left.symm) (left x) =
        let L := leftWeight • xi
        let R := rightWeight • eta.comp (fderiv ℝ (right ∘ left.symm) (left x))
        ![L+R,L-R,-L+R,-L-R] branch := by
  let l : D → ℝ := fun y => leftWeight*xi (left (left.symm y))
  let r : D → ℝ := fun y => rightWeight*eta (right (left.symm y))
  have he : l =ᶠ[𝓝 (left x)] fun y => leftWeight*xi y := by
    filter_upwards [left.open_target.mem_nhds (left.map_source hxLeft)] with y hy
    simp only [l,left.right_inv hy]
  have hl : DifferentiableAt ℝ l (left x) := he.differentiableAt_iff.mpr (xi.differentiableAt.const_mul leftWeight)
  have hld : fderiv ℝ l (left x) = leftWeight • xi := by
    rw [he.fderiv_eq]
    change fderiv ℝ (leftWeight • (fun y => xi y)) (left x) = _
    rw [fderiv_const_smul xi.differentiableAt,ContinuousLinearMap.fderiv]
  have hz : (0,left x) ∈ (repairReferenceHostTransition (Ep := ℝ) left right).source := by
    refine ⟨mem_univ _,left.map_source hxLeft,?_⟩
    change left.symm (left x) ∈ right.source
    rwa [left.left_inv hxLeft]
  have ht : DifferentiableAt ℝ (right ∘ left.symm) (left x) := by
    have hh := ((repair_reference_host_transition_smooth (Ep := ℝ) left right hLeft hRight).1.snd
      |>.contDiffAt ((repairReferenceHostTransition (Ep := ℝ) left right).open_source.mem_nhds hz)).comp (left x)
      (contDiffAt_const.prodMk contDiffAt_id)
    exact hh.differentiableAt (by simp)
  have hr : DifferentiableAt ℝ r (left x) := (eta.differentiableAt.comp _ ht).const_mul rightWeight
  have hrd : fderiv ℝ r (left x) = rightWeight • eta.comp (fderiv ℝ (right ∘ left.symm) (left x)) := by
    change fderiv ℝ (rightWeight • (eta ∘ (right ∘ left.symm))) (left x) = _
    rw [fderiv_const_smul (eta.differentiableAt.comp _ ht),fderiv_comp _ eta.differentiableAt ht,
      ContinuousLinearMap.fderiv]
  fin_cases branch
  · refine ⟨hl.add hr,?_⟩
    change fderiv ℝ (fun y => l y+r y) (left x) =
      leftWeight • xi+rightWeight • eta.comp (fderiv ℝ (right ∘ left.symm) (left x))
    exact (fderiv_fun_add hl hr).trans (congrArg₂ (·+·) hld hrd)
  · refine ⟨hl.sub hr,?_⟩
    change fderiv ℝ (fun y => l y-r y) (left x) =
      leftWeight • xi-rightWeight • eta.comp (fderiv ℝ (right ∘ left.symm) (left x))
    exact (fderiv_fun_sub hl hr).trans (congrArg₂ (·-·) hld hrd)
  · refine ⟨hl.neg.add hr,?_⟩
    change fderiv ℝ (-l+r) (left x) =
      -(leftWeight • xi)+rightWeight • eta.comp (fderiv ℝ (right ∘ left.symm) (left x))
    rw [fderiv_add hl.neg hr,fderiv_neg,hld,hrd]
  · refine ⟨hl.neg.sub hr,?_⟩
    change fderiv ℝ (-l-r) (left x) =
      -(leftWeight • xi)-rightWeight • eta.comp (fderiv ℝ (right ∘ left.symm) (left x))
    rw [fderiv_sub hl.neg hr,fderiv_neg,hld,hrd]

theorem increment_literal_signed_swap
    (left right : OpenPartialHomeomorph M D) (xi eta : D →L[ℝ] ℝ)
    (leftWeight rightWeight : ℝ) (branch : Fin 4) :
    incrementLiteralSignedPhase left right xi eta leftWeight rightWeight branch =
      incrementLiteralSignedPhase right left eta xi rightWeight leftWeight (![0,2,1,3] branch) := by
  funext x
  fin_cases branch
  · change leftWeight*xi (left x)+rightWeight*eta (right x) =
      rightWeight*eta (right x)+leftWeight*xi (left x)
    ring
  · change leftWeight*xi (left x)-rightWeight*eta (right x) =
      -(rightWeight*eta (right x))+leftWeight*xi (left x)
    ring
  · change -(leftWeight*xi (left x))+rightWeight*eta (right x) =
      rightWeight*eta (right x)-leftWeight*xi (left x)
    ring
  · change -(leftWeight*xi (left x))-rightWeight*eta (right x) =
      -(rightWeight*eta (right x))-leftWeight*xi (left x)
    ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_literal_signed_differential
#print axioms GlobalEmbedding.Continuation.increment_literal_signed_swap
