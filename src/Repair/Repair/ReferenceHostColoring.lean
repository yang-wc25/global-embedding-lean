import Smoothing.TensorPreparedProduct
import GlobalEmbedding.Paper.InitializationColoredCutoffsColoring
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The actual bounded host coloring used by the repair phase preparation

Source: `main.tex`, proof of `thm:repair`, the paragraph beginning
"Normalize a covering bump family".  The enlarged-support graph is the
original one.  Each primary label has an actual host and a bounded slot in
that host.  A genuine graph coloring produces one bounded integer label,
distinct on every pair of overlapping primary supports.  Its bound does
not involve the total number of hosts.  The empty host/primary cases and
zero slots are retained.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped Topology
namespace GlobalEmbedding.Continuation

theorem repair_reference_host_labels
    {X Host Primary : Type*} [TopologicalSpace X] [Fintype Host]
    (W : Host → Set X) (D K : ℕ)
    (hdegree : ∀ a, tensorEnlargedSupportDegree W a ≤ D)
    (host : Primary → Host) (slot : Primary → Fin K)
    (hinjective : Function.Injective (fun a => (host a, slot a)))
    (support : Primary → Set X) (hsub : ∀ a, support a ⊆ W (host a)) :
    ∃ label : Primary → ℕ,
      (∀ a, label a < (D+2)*K) ∧
      (∀ a b, a ≠ b → (support a ∩ support b).Nonempty → label a ≠ label b) := by
  classical
  let G := tensorEnlargedSupportGraph W
  obtain ⟨color⟩ := initialization_colored_cutoffs_coloring G D hdegree
  let enc : Fin (D+2) × Fin K ≃ Fin ((D+2)*K) := finProdFinEquiv
  let label : Primary → ℕ := fun a => (enc (color (host a),slot a)).val
  refine ⟨label, ?_, ?_⟩
  · intro a
    exact (enc (color (host a),slot a)).isLt
  · intro a b hab hinter heq
    have hpairs : (color (host a),slot a) = (color (host b),slot b) :=
      enc.injective (Fin.ext heq)
    have hcolors : color (host a) = color (host b) := congrArg Prod.fst hpairs
    have hslots : slot a = slot b := congrArg Prod.snd hpairs
    have hhosts : host a = host b := by
      by_contra hne
      obtain ⟨x, hxa, hxb⟩ := hinter
      have hadj : G.Adj (host a) (host b) := ⟨hne, x, hsub a hxa, hsub b hxb⟩
      exact color.valid hadj hcolors
    exact hab (hinjective (Prod.ext hhosts hslots))

/-- The cutoffs need only be subordinate to the same original normalized
host cutoffs.  No degree bound on a newly invented refinement graph is
assumed: it is the original enlarged-support degree that produces labels. -/
theorem repair_reference_normalized_host_labels
    {X Host Primary : Type*} [TopologicalSpace X] [Fintype Host]
    (W : Host → Set X) (raw : Host → X → ℝ)
    (hraw : ∀ a, tsupport (raw a) ⊆ W a)
    (D K : ℕ) (hdegree : ∀ a, tensorEnlargedSupportDegree W a ≤ D)
    (host : Primary → Host) (slot : Primary → Fin K)
    (hinjective : Function.Injective (fun a => (host a, slot a)))
    (chi : Primary → X → ℝ)
    (hsub : ∀ a, tsupport (chi a) ⊆ tsupport (squareNormalizedCutoff raw (host a))) :
    ∃ label : Primary → ℕ,
      (∀ a, label a < (D+2)*K) ∧
      (∀ x a b, x ∈ tsupport (chi a) → x ∈ tsupport (chi b) →
        a ≠ b → label a ≠ label b) := by
  obtain ⟨label,hbound,hdistinct⟩ := repair_reference_host_labels W D K hdegree host slot
    hinjective (fun a => tsupport (chi a))
    (fun a => (hsub a).trans ((squareNormalizedCutoff_tsupport_subset raw (host a)).trans
      (hraw (host a))))
  exact ⟨label,hbound,fun x a b hxa hxb hab => hdistinct a b hab ⟨x,hxa,hxb⟩⟩

/-- Original buffered atlas specialization, retaining its actual support
graph and the same cutoffs and slots. -/
theorem repair_reference_buffered_atlas_labels
    {M E Primary : Type*} [TopologicalSpace M] [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : BufferedAtlas M E) (K : ℕ)
    (host : Primary → Fin A.count) (slot : Primary → Fin K)
    (hinjective : Function.Injective (fun a => (host a, slot a)))
    (support : Primary → Set M) (hsub : ∀ a, support a ⊆ A.support (host a)) :
    ∃ label : Primary → ℕ,
      (∀ a, label a < (A.supportDegree+2)*K) ∧
      (∀ a b, a ≠ b → (support a ∩ support b).Nonempty → label a ≠ label b) := by
  apply repair_reference_host_labels A.support A.supportDegree K _ host slot hinjective support hsub
  intro a
  classical
  change A.supportGraph.degree a ≤ A.supportDegree
  exact Finset.le_sup (f := fun b : Fin A.count => A.supportGraph.degree b) (Finset.mem_univ a)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_host_labels
#print axioms GlobalEmbedding.Continuation.repair_reference_normalized_host_labels
#print axioms GlobalEmbedding.Continuation.repair_reference_buffered_atlas_labels
