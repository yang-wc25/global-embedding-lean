import NormalPolar.JointSecondarySource

/-! The explicit joint source has the original relative support and is smooth
on the original physical domain.  Both conclusions come from the constructed
physical pieces.  The ordinary signed-record and subordinate sums retain
their original labels, including the diagonal resonant exclusions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M Ep Label Sub : Type*} {m N : ℕ}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord Label

variable
    (F : Ep → M → (EuclideanSpace ℝ (Fin N))) (hF : ∀ b, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ (F b))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (geometry : (ActualSecondarySignedRecord Label) → Sub → ActualSecondaryRawGeometry F hF n j ell Mg W)
    (host : (ActualSecondarySignedRecord Label) → Sub → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1))))
    (cutoff : (ActualSecondarySignedRecord Label) → Sub → Ep × M → ℝ)
    (phase : Label → Ep × M → ℝ) (R Q : Label → Ep × M → (EuclideanSpace ℝ (Fin N))) (tau : ℝ)
    (data : (ActualSecondarySignedRecord Label) → Sub → ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (spec : JointSecondaryFamilySpec F hF n j ell Mg CH delta W
      geometry host cutoff phase R Q tau data)

include spec

theorem jointSecondary_physical_source_regular_support
    (hW : IsOpen W) (K : Set (Ep × M))
    (hK : ∀ rec b, (geometry rec b).support ⊆ K) (tau' : ℝ) (length : ℕ) :
    let source := fun rec b => jointSecondarySourceOfRawGeometry F hF n j ell Mg W
      (geometry rec b) (host rec b) (cutoff rec b) phase R Q tau rec.val
    let wave := actualParameterSecondarySourceSum F hF source tau' length
    ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,V) ∞ wave W ∧
      tsupport (fun z : W => wave z.val) ⊆ Subtype.val ⁻¹' K := by
  intro source wave
  have he : wave = actualConstructedSecondarySum F hF (fun rec b => (data rec b).base) tau' length :=
    (jointSecondary_sum_eq_physical_source F hF n j ell Mg CH delta W
      geometry host cutoff phase R Q tau data spec tau' length).symm
  rw [he]
  unfold actualConstructedSecondarySum actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
  simp only [Finset.sum_filter]
  constructor
  · apply contMDiffOn_finsetSum
    intro l _
    apply contMDiffOn_finsetSum
    intro l' _
    apply contMDiffOn_finsetSum
    intro q _
    by_cases h : l ≠ l' ∨ q = 0 ∨ q = 3
    · simp only [if_pos h,actualConstructedSecondaryFamily,dif_pos h]
      exact contMDiffOn_finsetSum (fun b _ => ((data ⟨((l,l'),q),h⟩ b).base.wave_regular tau' length hW).1)
    · simpa only [if_neg h] using contMDiffOn_const
  · apply actualRepairModelFirstDefect_finite_sum_support
    intro l
    apply actualRepairModelFirstDefect_finite_sum_support
    intro l'
    apply actualRepairModelFirstDefect_finite_sum_support
    intro q
    by_cases h : l ≠ l' ∨ q = 0 ∨ q = 3
    · simp only [if_pos h,actualConstructedSecondaryFamily,dif_pos h]
      apply actualRepairModelFirstDefect_finite_sum_support
      intro b
      have hs : (data ⟨((l,l'),q),h⟩ b).base.support = (geometry ⟨((l,l'),q),h⟩ b).support :=
        (spec ⟨((l,l'),q),h⟩ b).2.2.2.1
      exact (((data ⟨((l,l'),q),h⟩ b).base.wave_regular tau' length hW).2).trans
        (fun z hz => hK _ b (by simpa only [Set.mem_preimage,hs] using hz))
    · simp only [if_neg h]
      change tsupport (0 : W → V) ⊆ _
      rw [tsupport_zero]
      exact empty_subset _

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_physical_source_regular_support
