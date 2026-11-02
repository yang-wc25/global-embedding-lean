import NormalPolar.PassiveParameterSupport
import Mathlib.Topology.Compactness.Compact

/-! Exact global supports for a passive one-point seed, including compact
supports and the unchanged subordinate overlap count on compact P. -/

noncomputable section
open Set Function
open scoped Topology Classical
namespace GlobalEmbedding.Continuation

variable {S P M : Type*} [TopologicalSpace S] [Subsingleton S]
  [TopologicalSpace P] [TopologicalSpace M]

theorem passiveParameter_tsupport_iff
    (s₀ : S) (f : S × M → ℝ) (b : P) (x : M) :
    (b,x) ∈ tsupport (fun z : P × M => f (s₀,z.2)) ↔ (s₀,x) ∈ tsupport f := by
  constructor
  · intro hx
    exact tsupport_comp_subset_preimage f
      (continuous_const.prodMk continuous_snd : Continuous (fun z : P × M => (s₀,z.2))) hx
  · intro hx
    have hf : f = (fun z : P × M => f (s₀,z.2)) ∘ (fun z : S × M => (b,z.2)) := by
      funext z
      exact congrArg f (Prod.ext (Subsingleton.elim _ _) rfl)
    rw [hf] at hx
    exact tsupport_comp_subset_preimage (fun z : P × M => f (s₀,z.2))
      (continuous_const.prodMk continuous_snd : Continuous (fun z : S × M => (b,z.2))) hx

theorem passiveParameter_tsupport_eq_preimage (s₀ : S) (f : S × M → ℝ) :
    tsupport (fun z : P × M => f (s₀,z.2)) =
      (fun z : P × M => (s₀,z.2)) ⁻¹' tsupport f := by
  ext z
  exact passiveParameter_tsupport_iff s₀ f z.1 z.2

theorem passiveParameter_tsupport_compact [CompactSpace P]
    (s₀ : S) (f : S × M → ℝ) (hf : IsCompact (tsupport f)) :
    IsCompact (tsupport (fun z : P × M => f (s₀,z.2))) := by
  apply (isCompact_univ.prod (hf.image continuous_snd)).of_isClosed_subset (isClosed_tsupport _)
  intro z hz
  exact ⟨mem_univ _,⟨(s₀,z.2),(passiveParameter_tsupport_iff s₀ f z.1 z.2).mp hz,rfl⟩⟩

theorem passiveParameter_tsupport_overlap
    {Label : Type*} [Fintype Label] (s₀ : S) (f : Label → S × M → ℝ) (z : P × M) :
    (Finset.univ.filter (fun l => z ∈ tsupport (fun y : P × M => f l (s₀,y.2)))).card =
      (Finset.univ.filter (fun l => (s₀,z.2) ∈ tsupport (f l))).card := by
  congr 1
  ext l
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact passiveParameter_tsupport_iff s₀ (f l) z.1 z.2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveParameter_tsupport_iff
#print axioms GlobalEmbedding.Continuation.passiveParameter_tsupport_compact
#print axioms GlobalEmbedding.Continuation.passiveParameter_tsupport_overlap
