import Smoothing.ParameterOriginalCoreBounds
import GlobalEmbedding.Offline.ModelCoordinateNorms

/-!
# Literal weighted coordinate norms control actual shifted joint jets

The map entry in the frozen original Core carries a base-two shift. This
module retains that shift: order k+b costs ell^k, for every b at most the
stated base order. The proof uses the same differentiation and evaluation
domains, proves finiteness before taking a real projection, and retains the
actual continuous linear coordinate-change norms. No atlas cardinality is
introduced into the constant.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation

theorem paperAtlasWeighted_shifted_joint_jet_le
    {ι : Type*} [Fintype ι] {n q : ℕ}
    (base j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hfinite : paperAtlasWeighted base j ell f O S ≠ ⊤)
    (i : ι) {k b : ℕ} (hk : k ≤ j) (hb : b ≤ base)
    {x : Fin n → ℝ} (hx : x ∈ S i) :
    ell^k * ‖iteratedFDeriv ℝ (k+b) (f i) x‖ ≤
      coordinateDimensionFactor n (j+base) *
        (paperAtlasWeighted base j ell f O S).toReal := by
  have hbdd := (paperAtlasWeighted_ne_top_iff base j ell hell f O S hO hSO hf).1 hfinite
  have hspec (a : ℕ) (ha : a ≤ j) :=
    finiteCjNorm_specification (a+base) (f i) (S i)
      (fun r hr => hbdd i r (by omega))
  calc
    _ ≤ ell^k * finiteCjNorm (k+base) (f i) (S i) :=
      mul_le_mul_of_nonneg_left ((hspec k hk).2.1 (k+b) (by omega) x hx)
        (pow_nonneg hell.le k)
    _ ≤ ∑ a ∈ Finset.range (j+1), ell^a * finiteCjNorm (a+base) (f i) (S i) :=
      Finset.single_le_sum
        (fun a ha => mul_nonneg (pow_nonneg hell.le a)
          (hspec a (by simpa using ha)).1)
        (by simpa using hk)
    _ ≤ _ := paperAtlasWeighted_finiteCjNorm_bound base j ell hell f O S hO hSO hf hfinite i

/-- A fixed change from the paper's coordinate source and target to native
models preserves the shifted weights. All norm costs are explicit and
depend only on the fixed model equivalences and the derivative order. -/
theorem paperAtlasWeighted_native_shifted_joint_jet_le
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {ι : Type*} [Fintype ι] {n q : ℕ}
    (a : E ≃L[ℝ] (Fin n → ℝ)) (c : (Fin q → ℝ) ≃L[ℝ] Y)
    (base j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hfinite : paperAtlasWeighted base j ell f O S ≠ ⊤)
    (i : ι) {k b : ℕ} (hk : k ≤ j) (hb : b ≤ base)
    {x : E} (hx : a x ∈ S i) :
    ell^k * ‖iteratedFDeriv ℝ (k+b) (c ∘ f i ∘ a) x‖ ≤
      (‖c.toContinuousLinearMap‖ * linearModelFactor a (j+base) *
        coordinateDimensionFactor n (j+base)) *
        (paperAtlasWeighted base j ell f O S).toReal := by
  have hj := paperAtlasWeighted_shifted_joint_jet_le base j ell hell f O S hO hSO hf
    hfinite i hk hb hx
  have hchange := paper_coordinate_change_jet_bound a c (f i) x (k+b)
  have hpow : ‖a.toContinuousLinearMap‖^(k+b) ≤ linearModelFactor a (j+base) :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (linearModelFactor_mono a (by omega))
  calc
    _ ≤ ell^k * (‖c.toContinuousLinearMap‖ *
        ‖iteratedFDeriv ℝ (k+b) (f i) (a x)‖ * ‖a.toContinuousLinearMap‖^(k+b)) :=
      mul_le_mul_of_nonneg_left hchange (pow_nonneg hell.le k)
    _ ≤ ell^k * (‖c.toContinuousLinearMap‖ *
        ‖iteratedFDeriv ℝ (k+b) (f i) (a x)‖ * linearModelFactor a (j+base)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        (pow_nonneg hell.le k)
    _ = (‖c.toContinuousLinearMap‖ * linearModelFactor a (j+base)) *
        (ell^k * ‖iteratedFDeriv ℝ (k+b) (f i) (a x)‖) := by ring
    _ ≤ (‖c.toContinuousLinearMap‖ * linearModelFactor a (j+base)) *
        (coordinateDimensionFactor n (j+base) *
          (paperAtlasWeighted base j ell f O S).toReal) :=
      mul_le_mul_of_nonneg_left hj
        (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg a _))
    _ = _ := by ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.paperAtlasWeighted_shifted_joint_jet_le
#print axioms GlobalEmbedding.Continuation.paperAtlasWeighted_native_shifted_joint_jet_le
