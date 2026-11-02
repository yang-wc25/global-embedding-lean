import Smoothing.IntegrationSpatialPaperNorms
import GlobalEmbedding.Offline.WeightedTailAlgebra

/-!
# Original parameter/spatial weighted norm after genuine native gluing

These wrappers use the literal original spatial packet, with spatial orders
0,1,2 followed by joint derivatives. They turn actual native low/high error
jets into the original two-term (6.4). Every output norm is proved finite
before passing to its real value. No total chart count enters the conversion.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff ENNReal BigOperators

namespace GlobalEmbedding.Continuation

attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

theorem parameterSpatialWeighted_ne_top_of_Cj {ι : Type*} [Fintype ι] {n d q : ℕ}
    (m : ℕ) (t : ℝ) (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ))
    (hfinite : ∀ j ≤ m, parameterSpatialCj (n := n) (d := d) j f O S ≠ ⊤) :
    parameterSpatialWeighted (n := n) (d := d) m t f O S ≠ ⊤ := by
  unfold parameterSpatialWeighted paperAtlasWeighted
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  apply ENNReal.mul_ne_top
  · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  · simpa only [Nat.add_zero, parameterSpatialCj] using hfinite j (by simpa using hj)

theorem parameterSpatialWeighted_Cj_ne_top {ι : Type*} [Fintype ι] {n d q : ℕ}
    (m : ℕ) {t : ℝ} (ht : 0 < t)
    (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ))
    (hfinite : parameterSpatialWeighted (n := n) (d := d) m t f O S ≠ ⊤)
    {j : ℕ} (hj : j ≤ m) : parameterSpatialCj (n := n) (d := d) j f O S ≠ ⊤ := by
  have hsum : (∑ a ∈ Finset.range (m + 1), ENNReal.ofReal t ^ a *
      parameterSpatialCj (n := n) (d := d) a f O S) ≠ ⊤ := by
    simpa only [parameterSpatialWeighted, paperAtlasWeighted, parameterSpatialCj,
      Nat.add_zero] using hfinite
  have hterm := ENNReal.sum_ne_top.mp hsum j (by simpa using hj)
  have hw : ENNReal.ofReal t ^ j ≠ 0 :=
    ENNReal.pow_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr ht) j
  intro htop
  rw [htop, ENNReal.mul_top hw] at hterm
  exact hterm rfl

theorem parameterSpatialWeighted_toReal {ι : Type*} [Fintype ι] {n d q : ℕ}
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ))
    (hfinite : parameterSpatialWeighted (n := n) (d := d) m t f O S ≠ ⊤) :
    (parameterSpatialWeighted (n := n) (d := d) m t f O S).toReal =
      ∑ a ∈ Finset.range (m + 1), t ^ a *
        (parameterSpatialCj (n := n) (d := d) a f O S).toReal := by
  simpa only [parameterSpatialWeighted, parameterSpatialCj, Nat.add_zero] using
    paperAtlasWeighted_toReal 0 m t ht (parameterSpatialPacket (n := n) (d := d) f)
      (fun i => O i.1) (fun i => S i.1) hfinite

/-- All original native-to-coordinate costs are explicit and precede any
atlas, field or scale. L and H are the actual low and high native constants. -/
def parameterSpatialWeightedTailFactor (n d q m : ℕ) (L H : ℝ) : ℝ :=
  parameterSpatialCoordinateFactor n d q m * (((m + 1 : ℕ) : ℝ) * L + H)

theorem parameterSpatialWeightedTailFactor_nonneg (n d q m : ℕ) {L H : ℝ}
    (hL : 0 ≤ L) (hH : 0 ≤ H) : 0 ≤ parameterSpatialWeightedTailFactor n d q m L H := by
  unfold parameterSpatialWeightedTailFactor
  exact mul_nonneg (parameterSpatialCoordinateFactor_nonneg n d q m)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hL) hH)

/-- Original two-term (6.4), derived from actual native low/high jets of
the same map error. This includes arbitrary nonzero parameter dimension d.
It does not posit an output norm bound or a weighted tail as a hypothesis. -/
theorem parameterSpatialWeighted_tail_of_native_profiles
    {ι : Type*} [Fintype ι] {n d q : ℕ}
    (m r : ℕ) (f e : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O U S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hUO : ∀ i, U i ⊆ O i)
    (he : ∀ i, ContDiffOn ℝ ∞ (e i) (O i))
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t)
    (hNr : parameterSpatialWeighted (n := n) (d := d) r t f O S ≠ ⊤)
    (hNm : parameterSpatialWeighted (n := n) (d := d) m t f O S ≠ ⊤)
    (budget L H : ℝ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hbudget : (parameterSpatialWeighted (n := n) (d := d) r t f O S).toReal ≤ budget)
    (hlow : ∀ j ≤ m, j ≤ r → ∀ i, ∀ k ≤ j,
      ∀ z : (Fin d → ℝ) × (Fin n → ℝ), sourceFirstCoordinates n d z ∈ U i →
        ‖iteratedFDeriv ℝ k (spatialNativeJet (e i ∘ sourceFirstCoordinates n d)) z‖ ≤
          L * ell ^ (r - j) * (parameterSpatialCj (n := n) (d := d) r f O S).toReal)
    (hhigh : ∀ j ≤ m, ∀ i, ∀ k ≤ j,
      ∀ z : (Fin d → ℝ) × (Fin n → ℝ), sourceFirstCoordinates n d z ∈ U i →
        ‖iteratedFDeriv ℝ k (spatialNativeJet (e i ∘ sourceFirstCoordinates n d)) z‖ ≤
          H * (parameterSpatialCj (n := n) (d := d) j f O S).toReal) :
    parameterSpatialWeighted (n := n) (d := d) m tau e O U ≠ ⊤ ∧
      (parameterSpatialWeighted (n := n) (d := d) m tau e O U).toReal ≤
        parameterSpatialWeightedTailFactor n d q m L H *
          (budget * (ell / t) ^ r +
            (parameterSpatialWeighted (n := n) (d := d) m t f O S).toReal * (tau / t) ^ r) := by
  let I := fun j => (parameterSpatialCj (n := n) (d := d) j f O S).toReal
  let E := fun j => (parameterSpatialCj (n := n) (d := d) j e O U).toReal
  let F := parameterSpatialCoordinateFactor n d q m
  have hF : 0 ≤ F := parameterSpatialCoordinateFactor_nonneg n d q m
  have hell : 0 < ell := htau.trans_le htaul
  have ht : 0 < t := hell.trans_le helt
  have hhighC (j : ℕ) (hj : j ≤ m) :=
    parameterSpatialCj_finite_and_bound_of_native j e O U hO hUO he (H * I j)
      (mul_nonneg hH ENNReal.toReal_nonneg) (hhigh j hj)
  have hout := parameterSpatialWeighted_ne_top_of_Cj m tau e O U
    (fun j hj => (hhighC j hj).1)
  have hl : ∀ j ≤ m, j ≤ r → E j ≤ (F * L) * ell ^ (r - j) * I r := by
    intro j hj hjr
    have h := (parameterSpatialCj_finite_and_bound_of_native j e O U hO hUO he
      (L * ell ^ (r-j) * I r) (by exact mul_nonneg (mul_nonneg hL (pow_nonneg hell.le _)) ENNReal.toReal_nonneg)
      (hlow j hj hjr)).2
    apply h.trans
    calc
      _ ≤ F * (L * ell ^ (r-j) * I r) :=
        mul_le_mul_of_nonneg_right (parameterSpatialCoordinateFactor_mono n d q hj)
          (mul_nonneg (mul_nonneg hL (pow_nonneg hell.le _)) ENNReal.toReal_nonneg)
      _ = _ := by ring
  have hh : ∀ j ≤ m, E j ≤ (F * H) * I j := by
    intro j hj
    apply (hhighC j hj).2.trans
    calc
      _ ≤ F * (H * I j) :=
        mul_le_mul_of_nonneg_right (parameterSpatialCoordinateFactor_mono n d q hj)
          (mul_nonneg hH ENNReal.toReal_nonneg)
      _ = _ := by ring
  have hNrSum : (∑ a ∈ Finset.range (r+1), t^a * I a) ≤ budget := by
    rw [parameterSpatialWeighted_toReal r t ht.le f O S hNr] at hbudget
    exact hbudget
  have hw := weighted_low_high_tail m r I E (fun _ => ENNReal.toReal_nonneg)
    (F * L) (F * H) (mul_nonneg hF hL) (mul_nonneg hF hH)
    htau.le htaul helt ht budget hNrSum hl hh
  refine ⟨hout, ?_⟩
  rw [parameterSpatialWeighted_toReal m tau htau.le e O U hout,
    parameterSpatialWeighted_toReal m t ht.le f O S hNm]
  convert hw using 1
  unfold parameterSpatialWeightedTailFactor
  dsimp only [F]
  ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.parameterSpatialWeighted_tail_of_native_profiles
