import Smoothing.IntegrationSpatialWeighted

/-!
# Sign and error-orientation invariance for the actual spatial packet norm

These identities retain the original coordinate derivative norm, including
infinite values. They justify the paper's G-SG orientation after estimating
SG-G, without a change of map, domain, or norm.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

/-- Native spatial words commute with negation without any regularity premise. -/
theorem parameterSpatialJet_neg {n d q : ℕ}
    (u : (Fin (n+d) → ℝ) → Fin q → ℝ) (w : ParameterSpatialWord n) (z : Fin (n+d) → ℝ) :
    parameterSpatialJet (n := n) (d := d) (fun y => -u y) w z =
      -parameterSpatialJet (n := n) (d := d) u w z := by
  exact congrArg (fun L => L (fun j => Pi.single (Fin.castAdd d (w.2 j)) 1))
    (iteratedFDeriv_neg_apply (𝕜 := ℝ) (f := u) (i := w.1.val) (x := z))

variable {ι : Type*} [Fintype ι] {n d q : ℕ}

theorem parameterSpatialCj_neg (j : ℕ)
    (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    parameterSpatialCj (n := n) (d := d) j (fun i y => -f i y) O S =
      parameterSpatialCj (n := n) (d := d) j f O S := by
  have he : parameterSpatialPacket (n := n) (d := d) (fun i y => -f i y) =
      fun iw => -parameterSpatialPacket (n := n) (d := d) f iw := by
    funext iw z
    exact parameterSpatialJet_neg (f iw.1) iw.2 z
  unfold parameterSpatialCj
  rw [he]
  exact paperAtlasCj_neg j (parameterSpatialPacket (n := n) (d := d) f)
    (fun iw => O iw.1) (fun iw => S iw.1) (fun iw => hO iw.1) (fun iw => hSO iw.1)
    (fun iw => parameterSpatialJet_contDiffOn (hO iw.1) (hf iw.1) iw.2)

theorem parameterSpatialWeighted_neg (m : ℕ) (t : ℝ)
    (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    parameterSpatialWeighted (n := n) (d := d) m t (fun i y => -f i y) O S =
      parameterSpatialWeighted (n := n) (d := d) m t f O S := by
  unfold parameterSpatialWeighted paperAtlasWeighted
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact parameterSpatialCj_neg (j+0) f O S hO hSO hf

/-- The original G-SG and SG-G anisotropic norms are exactly equal. -/
theorem parameterSpatialWeighted_sub_comm (m : ℕ) (t : ℝ)
    (f g : ι → (Fin (n+d) → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i)) :
    parameterSpatialWeighted (n := n) (d := d) m t (fun i y => f i y - g i y) O S =
      parameterSpatialWeighted (n := n) (d := d) m t (fun i y => g i y - f i y) O S := by
  simpa only [neg_sub] using (parameterSpatialWeighted_neg m t (fun i y => f i y-g i y) O S
    hO hSO (fun i => (hf i).sub (hg i))).symm

#print axioms parameterSpatialWeighted_neg
#print axioms parameterSpatialWeighted_sub_comm
end
end GlobalEmbedding.Continuation
