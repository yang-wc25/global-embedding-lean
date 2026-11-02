import Smoothing.ParameterRound2RepairNormAlgebra
import Smoothing.ParameterRound2NativeTensorGermNorms

/-! Exact original three-term norm algebra on genuine sample neighborhoods.
Only the original differentiation domains are restricted locally for the
proof; every final norm is the unchanged frozen paperAtlasWeighted. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

theorem actual_paperWeighted_normalized_three_terms_germs
    {ι : Type*} [Fintype ι] {n q : ℕ}
    (m : ℕ) {tau : ℝ} (htau : 0 < tau)
    (f g h : ι → (Fin n → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ S i ⊆ U ∧ ContDiffOn ℝ ∞ (f i) U)
    (hg : ∀ i, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ S i ⊆ U ∧ ContDiffOn ℝ ∞ (g i) U)
    (hh : ∀ i, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ S i ⊆ U ∧ ContDiffOn ℝ ∞ (h i) U)
    (hfFinite : paperAtlasWeighted 0 m tau f O S ≠ ⊤)
    (hgFinite : paperAtlasWeighted 0 m tau g O S ≠ ⊤)
    (hhFinite : paperAtlasWeighted 0 m tau h O S ≠ ⊤)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let R := fun i x => b • (a • f i x-g i x-h i x)
    (∀ i, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ S i ⊆ U ∧ ContDiffOn ℝ ∞ (R i) U) ∧
    paperAtlasWeighted 0 m tau R O S ≠ ⊤ ∧
    (paperAtlasWeighted 0 m tau R O S).toReal ≤
      b*(a*(paperAtlasWeighted 0 m tau f O S).toReal+
        (paperAtlasWeighted 0 m tau g O S).toReal+(paperAtlasWeighted 0 m tau h O S).toReal) := by
  intro R
  choose Of hOf hSf hfs using hf
  choose Og hOg hSg hgs using hg
  choose Oh hOh hSh hhs using hh
  let V := fun i => O i ∩ (Of i ∩ (Og i ∩ Oh i))
  have hV : ∀ i, IsOpen (V i) := fun i => (hO i).inter ((hOf i).inter ((hOg i).inter (hOh i)))
  have hSV : ∀ i, S i ⊆ V i := fun i x hx => ⟨hSO i hx,hSf i hx,hSg i hx,hSh i hx⟩
  have hVO : ∀ i, V i ⊆ O i := fun _ => inter_subset_left
  have hfV (i) : ContDiffOn ℝ ∞ (f i) (V i) := (hfs i).mono (fun _ hx => hx.2.1)
  have hgV (i) : ContDiffOn ℝ ∞ (g i) (V i) := (hgs i).mono (fun _ hx => hx.2.2.1)
  have hhV (i) : ContDiffOn ℝ ∞ (h i) (V i) := (hhs i).mono (fun _ hx => hx.2.2.2)
  have he (u : ι → (Fin n → ℝ) → Fin q → ℝ) :=
    actual_paperAtlasWeighted_open_restrict 0 m tau u O V S hO hV hVO hSV
  have hnorm := parameterRound2_paperAtlasWeighted_normalized_three_terms m htau f g h V S hV hSV
    hfV hgV hhV ((he f) ▸ hfFinite) ((he g) ▸ hgFinite) ((he h) ▸ hhFinite) a b ha hb
  refine ⟨?_,?_,?_⟩
  · intro i
    exact ⟨V i,hV i,hSV i,(((hfV i).const_smul a).sub (hgV i) |>.sub (hhV i)).const_smul b⟩
  · rw [he R]
    exact hnorm.1
  · rw [he R,he f,he g,he h]
    exact hnorm.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_paperWeighted_normalized_three_terms_germs
