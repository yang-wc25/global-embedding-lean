import GlobalEmbedding.Paper.CollarCoefficientComplexStrip
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual source complex extension in the Euclidean coefficient model

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Canonical finite coordinates are transported by actual complex CLMs.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Real source coefficients yield an actual complex analytic, periodic Euclidean-valued
extension on an actual invariant open product domain containing the entire base real orbit.
It agrees exactly with the original real data throughout a positive real base neighborhood.

Source: Proposition `prop:collar`, proof lines 530–534. Construct the full real-source complex
strip first. The actual complex linear append map takes the Euclidean base/orbit product to
its canonical finite coordinates; pull back the genuine complex open domain along this CLM.
The actual inverse Euclidean coordinate equivalence transports the coefficient values to the
original Euclidean norm model. Both actual maps are complex linear and continuous, so the
extension remains complex analytic. The append identity under integer spatial shifts proves
the actual domain and function periodicities. The common source strip contains every real
base orbit, and its exact real agreement becomes the stated actual Euclidean value formula.
No alternate Hölder norm or assumed complex extension is introduced. -/
theorem collar_euclidean_coefficient_complex_extension {b a N : ℕ}
    (f : (Fin (b + a) → ℝ) → (Fin N → ℝ)) (V : Set (Fin b → ℝ))
    (hV : IsOpen V) (p₀ : Fin b → ℝ) (hp₀ : p₀ ∈ V)
    (hf : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      AnalyticAt ℝ f x)
    (hperiod : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        f (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = f x) :
    ∃ (U : Set (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)))
      (g : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) →
        EuclideanSpace ℂ (Fin N)) (ε : ℝ), 0 < ε ∧ IsOpen U ∧ AnalyticOnNhd ℂ g U ∧
      (∀ y : EuclideanSpace ℝ (Fin a),
        (toLp 2 (fun i ↦ (p₀ i : ℂ)), toLp 2 (fun j ↦ (y j : ℂ))) ∈ U) ∧
      (∀ w (t : Fin a → ℤ), w + (0, toLp 2 (fun j : Fin a ↦ (t j : ℂ))) ∈ U ↔ w ∈ U) ∧
      (∀ w ∈ U, ∀ t : Fin a → ℤ, g (w + (0, toLp 2 (fun j ↦ (t j : ℂ)))) = g w) ∧
      (∀ (p : Fin b → ℝ) (y : Fin a → ℝ),
        (∀ i, |p i - p₀ i| < ε) → p ∈ V ∧
        g (toLp 2 (fun i ↦ (p i : ℂ)), toLp 2 (fun j ↦ (y j : ℂ))) =
          toLp 2 (fun l ↦ (f (Fin.append p y) l : ℂ))) := by
  obtain ⟨U, G, ε, _, hε, hU, hG, hinv, hGp, hreal, _, hstrip⟩ :=
    collar_coefficient_complex_strip f V hV p₀ hp₀ hf hperiod
  let Sₗ : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) →ₗ[ℂ]
      (Fin (b + a) → ℂ) :=
    { toFun := fun w ↦ Fin.append (fun i ↦ w.1 i) (fun j ↦ w.2 j)
      map_add' := by intro w v; ext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
      map_smul' := by intro c w; ext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp }
  let S := Sₗ.toContinuousLinearMap
  let E := (EuclideanSpace.equiv (Fin N) ℂ).symm.toContinuousLinearMap
  have hS (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) :
      S w = Fin.append (fun i ↦ w.1 i) (fun j ↦ w.2 j) := rfl
  have hE (v : Fin N → ℂ) : E v = toLp 2 v := rfl
  have hSreal (p : Fin b → ℝ) (y : Fin a → ℝ) :
      S (toLp 2 (fun i ↦ (p i : ℂ)), toLp 2 (fun j ↦ (y j : ℂ))) =
        fun r ↦ ((Fin.append p y r : ℝ) : ℂ) := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [hS]
  have hshift (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) (t : Fin a → ℤ) :
      S (w + (0, toLp 2 (fun j ↦ (t j : ℂ)))) =
        S w + Fin.append (fun _ : Fin b ↦ (0 : ℂ)) (fun j ↦ (t j : ℂ)) := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [hS]
  let W := S ⁻¹' U
  let g := fun w ↦ E (G (S w))
  have hg : AnalyticOnNhd ℂ g W := by
    intro w hw
    exact (E.analyticAt _).comp ((hG (S w) hw).comp (S.analyticAt w))
  refine ⟨W, g, ε, hε, hU.preimage S.continuous, hg, ?_, ?_, ?_, ?_⟩
  · intro y
    change S _ ∈ U
    rw [hSreal]
    exact (hstrip _ (by intro i; simp only [Fin.append_left, sub_self, norm_zero]; exact hε)
      (by intro j; simp only [Fin.append_right, Complex.ofReal_im, abs_zero]; exact hε)).1
  · intro w t
    change S (w + _) ∈ U ↔ S w ∈ U
    rw [hshift]
    exact hinv (S w) t
  · intro w hw t
    change E (G (S (w + _))) = E (G (S w))
    rw [hshift, hGp (S w) hw t]
  · intro p y hp
    have he := hreal (Fin.append p y) (by simpa only [Fin.append_left] using hp)
    refine ⟨by simpa only [Fin.append_left] using he.1, ?_⟩
    change E (G (S _)) = _
    rw [hSreal, he.2, hE]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_euclidean_coefficient_complex_extension
