import Mathlib.Topology.Algebra.Support
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Exact relative supports of passive primitive data

The scalar field and its original relative support are pulled back through
the actual parameter projection.  For a one-point seed this preserves the
support pointwise, so the original labels and overlap counts are unchanged.
No support or disjointness assumption about a completed increment is used.
-/

noncomputable section
open Set Function
open scoped Topology Classical
namespace GlobalEmbedding.Continuation

variable {S P M : Type*} [TopologicalSpace S] [TopologicalSpace P]
  [TopologicalSpace M]

theorem passiveParameter_relativeSupport_subset (s₀ : S) (W : Set (S × M))
    (f : S × M → ℝ) :
    (Subtype.val '' tsupport
      (fun z : ((fun z : P × M => (s₀,z.2)) ⁻¹' W) => f (s₀,z.val.2))) ⊆
    (fun z : P × M => (s₀,z.2)) ⁻¹'
      (Subtype.val '' tsupport (fun z : W => f z.val)) := by
  let lift : ((fun z : P × M => (s₀,z.2)) ⁻¹' W) → W :=
    fun z => ⟨(s₀,z.val.2),z.property⟩
  have hlift : Continuous lift :=
    (continuous_const.prodMk continuous_subtype_val.snd).subtype_mk _
  rintro z ⟨w,hw,rfl⟩
  exact ⟨lift w,tsupport_comp_subset_preimage (fun y : W => f y.val) hlift hw,rfl⟩

/-- Exact relative support at each physical parameter, including empty
spatial supports and zero-dimensional parameter spaces. -/
theorem passiveParameter_relativeSupport_iff [Subsingleton S]
    (s₀ : S) (W : Set (S × M)) (f : S × M → ℝ) (b : P) (x : M) :
    (b,x) ∈ (Subtype.val '' tsupport
      (fun z : ((fun z : P × M => (s₀,z.2)) ⁻¹' W) => f (s₀,z.val.2))) ↔
    (s₀,x) ∈ (Subtype.val '' tsupport (fun z : W => f z.val)) := by
  constructor
  · exact fun h => passiveParameter_relativeSupport_subset s₀ W f h
  · rintro ⟨w,hw,heq⟩
    let lift : W → ((fun z : P × M => (s₀,z.2)) ⁻¹' W) :=
      fun z => ⟨(b,z.val.2),by
        change (s₀,z.val.2) ∈ W
        have h : (s₀,z.val.2) = z.val := Prod.ext (Subsingleton.elim _ _) rfl
        exact h.symm ▸ z.property⟩
    have hlift : Continuous lift :=
      (continuous_const.prodMk continuous_subtype_val.snd).subtype_mk _
    have hcomp : (fun z : W => f z.val) =
        (fun z : ((fun z : P × M => (s₀,z.2)) ⁻¹' W) => f (s₀,z.val.2)) ∘ lift := by
      funext z
      change f z.val = f (s₀,z.val.2)
      exact congrArg f (Prod.ext (Subsingleton.elim _ _) rfl)
    rw [hcomp] at hw
    refine ⟨lift w,tsupport_comp_subset_preimage _ hlift hw,?_⟩
    change (b,w.val.2) = (b,x)
    exact Prod.ext rfl (congrArg (fun z : S × M => z.2) heq)

theorem passiveParameter_relativeSupport_overlap [Subsingleton S]
    {Label : Type*} [Fintype Label] (s₀ : S) (W : Set (S × M))
    (f : Label → S × M → ℝ) (b : P) (x : M) :
    (Finset.univ.filter (fun l =>
      (b,x) ∈ (Subtype.val '' tsupport
        (fun z : ((fun z : P × M => (s₀,z.2)) ⁻¹' W) => f l (s₀,z.val.2))))).card =
    (Finset.univ.filter (fun l => (s₀,x) ∈
      (Subtype.val '' tsupport (fun z : W => f l z.val)))).card := by
  classical
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    passiveParameter_relativeSupport_iff]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveParameter_relativeSupport_iff
#print axioms GlobalEmbedding.Continuation.passiveParameter_relativeSupport_overlap
