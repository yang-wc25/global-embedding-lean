import Repair.AuxBridgeNovOriginalSupports

/-! Support output in terms of the original labelled cutoffs and the same U.
It retains the actual decomposition into primary labels and signed quadratic
pairs, while hiding only internal refinement indices. All supports are the
original relative supports on the genuine final open neighborhood. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {X V Label : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
  [Fintype Label] [DecidableEq Label]

def FullIncrementNovOriginalSupportConclusion
    (cutoff : Label → X → ℝ) (W : Set X) (U : X → V) : Prop :=
  ∃ (primary : Label → X → V) (secondary : ((Label × Label) × Fin 4) → X → V),
    U = (fun z => (∑ nu, primary nu z) +
      ∑ r ∈ actualSecondaryNonzeroRecords Label, secondary r z) ∧
    (∀ nu, tsupport (fun z : W => primary nu z.val) ⊆ Subtype.val ⁻¹' tsupport (cutoff nu)) ∧
    (∀ r, tsupport (fun z : W => secondary r z.val) ⊆
      Subtype.val ⁻¹' (tsupport (cutoff r.1.1) ∩ tsupport (cutoff r.1.2))) ∧
    tsupport (fun z : W => U z.val) ⊆ Subtype.val ⁻¹' (⋃ nu, tsupport (cutoff nu))

variable {m N : ℕ} {P M SubPrimary SubSecondary : Type*}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

omit [TopologicalSpace X] [NormedAddCommGroup V] in
theorem fullIncrementNov_original_support_decomposition
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
    (W : Set (P × M))
    (h : AuxBridgeNovOriginalSupports F hF g input length tau delta choice W) :
    FullIncrementNovOriginalSupportConclusion g.cutoff W
      (round3ParameterIncrementMap F hF g input length tau delta choice) := by
  let primary := fun nu z => delta •
    (Real.cos (g.phase nu z / tau) • round3ParameterPrimaryAmplitude F hF g input length tau true nu z -
      Real.sin (g.phase nu z / tau) • round3ParameterPrimaryAmplitude F hF g input length tau false nu z)
  let secondary := fun (r : (Label × Label) × Fin 4) z =>
    if hr : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 then
      ∑ a, round3ParameterSecondaryPiece F hF g input length tau delta r (choice ⟨r,hr⟩ a) z else 0
  refine ⟨primary,secondary,?_,h.primary_label,?_,h.total⟩
  · funext z
    unfold round3ParameterIncrementMap round3ParameterPrimaryWave round3ParameterSecondarySum
    rw [actual_secondary_refined_sum_eq_records]
    dsimp only
    rw [Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := (Finset.mem_filter.mp hr).2
    simp only [secondary,dif_pos hr']
  · intro r
    apply auxBridgeNov_relative_support_of_zero (secondary r) W
      (tsupport (g.cutoff r.1.1) ∩ tsupport (g.cutoff r.1.2))
      ((isClosed_tsupport _).inter (isClosed_tsupport _))
    intro z hz hn
    dsimp only [secondary]
    split_ifs with hr
    · apply Finset.sum_eq_zero
      intro a ha
      have hnot : (⟨z,hz⟩ : W) ∉ tsupport (fun w : W =>
          round3ParameterSecondaryPiece F hF g input length tau delta r (choice ⟨r,hr⟩ a) w.val) :=
        fun ht => hn (h.secondary_piece ⟨r,hr⟩ a ht)
      change (fun w : W => round3ParameterSecondaryPiece F hF g input length tau delta r
        (choice ⟨r,hr⟩ a) w.val) ⟨z,hz⟩ = 0
      exact image_eq_zero_of_notMem_tsupport (f := fun w : W =>
        round3ParameterSecondaryPiece F hF g input length tau delta r (choice ⟨r,hr⟩ a) w.val) hnot
    · rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.FullIncrementNovOriginalSupportConclusion
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_support_decomposition
