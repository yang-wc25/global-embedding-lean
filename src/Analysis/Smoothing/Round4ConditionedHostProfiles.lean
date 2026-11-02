import Probes.ActualHostRefinementCutoff

/-! Restricting a chart's domain preserves its literal functions. On the
unchanged cutoff support, the old target membership is recovered from the
actual support relation. Thus its existing jet bounds apply to the genuine
conditioned target without an unproved domain enlargement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped Topology ContDiff
namespace GlobalEmbedding.Continuation
variable {Z X : Type*} [TopologicalSpace Z] [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem round4_conditioned_host_original_target
    (q : OpenPartialHomeomorph Z X) (b₀ b₁ : OpenPartialHomeomorph X X)
    (eta₀ eta₁ : Z → ℝ) (heta : eta₁ = eta₀)
    (hforward : (b₁ : X → X) = b₀)
    (hSource : b₁.source ⊆ q.target)
    (hSupport : tsupport eta₀ ⊆ (q.trans b₀).source)
    (y : X) (hy : y ∈ b₁.target)
    (hEta : (q.trans b₁).symm y ∈ tsupport eta₁) :
    b₁.symm y ∈ b₀.source ∧ y ∈ b₀.target := by
  have hx := hSource (b₁.map_target hy)
  have hEtaOld : q.symm (b₁.symm y) ∈ tsupport eta₀ := by
    change q.symm (b₁.symm y) ∈ tsupport eta₁ at hEta
    rwa [heta] at hEta
  have hs : q.symm (b₁.symm y) ∈ (q.trans b₀).source := hSupport hEtaOld
  have hOld : b₁.symm y ∈ b₀.source := by
    have hh := hs.2
    change q (q.symm (b₁.symm y)) ∈ b₀.source at hh
    rwa [q.right_inv hx] at hh
  have he : b₀ (b₁.symm y) = y := by
    rw [← hforward]
    exact b₁.right_inv hy
  exact ⟨hOld,by simpa only [he] using b₀.map_source hOld⟩

theorem round4_conditioned_host_adapted_cutoff_eq
    (q : OpenPartialHomeomorph Z X) (b₀ b₁ : OpenPartialHomeomorph X X)
    (eta₀ eta₁ : Z → ℝ) (heta : eta₁ = eta₀)
    (hinverse : (b₁.symm : X → X) = b₀.symm) :
    eta₁ ∘ (q.trans b₁).symm = eta₀ ∘ (q.trans b₀).symm := by
  funext y
  change eta₁ (q.symm (b₁.symm y)) = eta₀ (q.symm (b₀.symm y))
  rw [heta,hinverse]

#print axioms round4_conditioned_host_original_target
#print axioms round4_conditioned_host_adapted_cutoff_eq
end GlobalEmbedding.Continuation
