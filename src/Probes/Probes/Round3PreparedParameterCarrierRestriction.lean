import Probes.Round3PreparedCompactProfiles

/-! Parameter neighborhoods from genuine compact carriers. A stage-dependent
open set may be chosen after pointwise control on the original compact
parameter set, without changing any carrier, chart function or profile.
No compactness of the whole source manifold is required. -/

noncomputable section
open Set Function
namespace GlobalEmbedding.Continuation

theorem round3_prepared_compact_carrier_parameter_neighborhood
    {P M I : Type*} [TopologicalSpace P] [T2Space P] [TopologicalSpace M] [Fintype I]
    (K V0 : Set P) (hV0 : IsOpen V0) (hKV0 : K ⊆ V0)
    (carrier good : I → Set (P × M))
    (hCarrier : ∀ i, IsCompact (carrier i)) (hGood : ∀ i, IsOpen (good i))
    (hKgood : ∀ i p, p ∈ K → ∀ x, (p,x) ∈ carrier i → (p,x) ∈ good i) :
    ∃ V : Set P, IsOpen V ∧ K ⊆ V ∧ V ⊆ V0 ∧
      ∀ i, (V ×ˢ (univ : Set M)) ∩ carrier i ⊆ good i := by
  let bad : Set P := ⋃ i, Prod.fst '' (carrier i ∩ (good i)ᶜ)
  have hBad : IsCompact bad := isCompact_iUnion
    (fun i => ((hCarrier i).inter_right (hGood i).isClosed_compl).image continuous_fst)
  let V := V0 ∩ badᶜ
  refine ⟨V,hV0.inter hBad.isClosed.isOpen_compl,?_,inter_subset_left,?_⟩
  · intro p hp
    refine ⟨hKV0 hp,?_⟩
    intro hbad
    obtain ⟨i,⟨z,⟨hz,hzg⟩,hzp⟩⟩ := mem_iUnion.mp hbad
    have hpz : z.1 ∈ K := by rwa [hzp]
    exact hzg (hKgood i z.1 hpz z.2 hz)
  · intro i z hz
    by_contra hbad
    apply hz.1.1.2
    exact mem_iUnion.mpr ⟨i,⟨z,⟨hz.2,hbad⟩,rfl⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_compact_carrier_parameter_neighborhood
