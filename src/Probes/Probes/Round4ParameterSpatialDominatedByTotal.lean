import Smoothing.Round4SpatialPairNorm

/-!
# The genuine spatial packet is bounded by the stronger total working norm

Only this one-way inequality is asserted. Every actual spatial coordinate
word has length at most two; appending the extra joint coordinate word gives
one actual total coordinate word of order at most j+2. The comparison has
constant one, no chart count, and no loss in the extra weighted order.
It lets an existing stronger repair state consume the literal spatial
smoothing theorem without adding another budget premise.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation

theorem round4Parameter_partial_append {n : ℕ}
    (l r : List (Fin n)) (f : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ)) :
    paperCoordinatePartial l (paperCoordinatePartial r f O) O =
      paperCoordinatePartial (l ++ r) f O := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    simp only [paperCoordinatePartial, List.cons_append, ih]

theorem round4ParameterSpatialCj_le_total
    {ι : Type*} [Fintype ι] {n d q : ℕ}
    (j : ℕ) (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    parameterSpatialCj (n := n) (d := d) j f O S ≤ paperAtlasCj (j+2) f O S := by
  unfold parameterSpatialCj paperAtlasCj
  refine iSup_le fun iw => ?_
  unfold paperCoordinateCj
  refine iSup_le fun l => iSup_le fun x => iSup_le fun c => ?_
  let w := List.ofFn (fun a => Fin.castAdd d (iw.2.2 a))
  have heq : Set.EqOn
      (fun y => parameterSpatialPacket (n := n) (d := d) f iw y c)
      (paperCoordinatePartial w (fun y => f iw.1 y c) (O iw.1)) (O iw.1) := by
    intro z hz
    exact parameterSpatialJet_eq_paper_partial (hO iw.1) (hf iw.1) iw.2 hz c
  rw [paperCoordinatePartial_congr l.val heq (hSO iw.1 x.property),
    round4Parameter_partial_append]
  have hlen : (l.val ++ w).length ≤ j+2 := by
    have hword := iw.2.1.isLt
    have horder := l.property.2
    simp only [List.length_append, w, List.length_ofFn]
    omega
  have hh := paper_coordinate_partial_le (j+2) (f iw.1) (O iw.1) (S iw.1)
    (hO iw.1) (hSO iw.1) (hf iw.1) (l.val ++ w) hlen x c
  exact hh.trans (le_iSup_of_le iw.1 le_rfl)

theorem round4ParameterSpatialWeighted_le_total
    {ι : Type*} [Fintype ι] {n d q : ℕ}
    (j : ℕ) (t : ℝ) (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    parameterSpatialWeighted (n := n) (d := d) j t f O S ≤
      paperAtlasWeighted 2 j t f O S := by
  unfold parameterSpatialWeighted paperAtlasWeighted
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul' le_rfl
  simpa only [Nat.add_zero, parameterSpatialCj] using
    round4ParameterSpatialCj_le_total a f O S hO hSO hf

variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem round4ParameterSpatialPairWeighted_le_total
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin c) P (EuclideanSpace ℝ (Fin d)))
    (F : P × M → EuclideanSpace ℝ (Fin N))
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart F i)
      (incrementsOriginalDifferentiation A B.chart i)) (j : ℕ) (t : ℝ) :
    round4ParameterSpatialPairWeighted A B F H j t S ≤
      parameterLocalOriginalTotalPairWeighted A B F H j t S :=
  add_le_add (round4ParameterSpatialWeighted_le_total j t
    (incrementsOriginalMapCoordinates A B.chart F)
    (incrementsOriginalDifferentiation A B.chart) S
    (parameterRound2_originalDifferentiation_open A B.chart) hSO hF) le_rfl

#print axioms round4ParameterSpatialCj_le_total
#print axioms round4ParameterSpatialWeighted_le_total
#print axioms round4ParameterSpatialPairWeighted_le_total
end GlobalEmbedding.Continuation
