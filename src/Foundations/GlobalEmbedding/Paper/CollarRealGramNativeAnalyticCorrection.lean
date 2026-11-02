import GlobalEmbedding.Paper.CollarRealGramSourceCoefficients
import GlobalEmbedding.Paper.CollarSourceNativeAnalyticCorrection

/-!
# The actual real Gram source formula gives a native analytic correction

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 522–534. The coefficient is exactly the original ordinary-transpose Gram inverse.
-/

open Set Filter WithLp Matrix
open scoped Topology NNReal Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Original real periodic matrix data, Gram nondegeneracy only over the base fiber, actual
forcing and the original real contraction give a genuine native analytic torus correction.

Source: Proposition `prop:collar`, proof lines 522–534. Actual determinant continuity and
periodic compactness construct an open base neighborhood of uniform Gram nondegeneracy. The
actual ordinary-transpose formula constructs a genuine analytic periodic right inverse there,
with exactly the real finite-coordinate matrix source coefficient used by actual multiplication.
Apply the source native analytic correction theorem to this precise coefficient and the
restricted original forcing. This constructs one actual common open correction domain with
exact source lifts, original real norm-ball fixed equation and uniqueness, and native joint
analytic order omega on the original torus. C_F analyticity, nearby Gram nondegeneracy, complex
extensions, function-space membership and correction existence are not extra assumptions.
Actual geometric construction of T_F/h and the real bounded Q/translation symmetry/contraction
estimates remain explicit inputs or separate obligations; no global bundle gluing is claimed. -/
theorem collar_real_gram_native_analytic_correction {b a M N : ℕ}
    (T : (Fin (b + a) → ℝ) → Matrix (Fin M) (Fin N) ℝ)
    (fH : (Fin (b + a) → ℝ) → (Fin M → ℝ))
    (V : Set (Fin b → ℝ)) (hV : IsOpen V) (p₀ : Fin b → ℝ) (hp₀ : p₀ ∈ V)
    (hT : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ i j, AnalyticAt ℝ (fun z ↦ T z i j) x)
    (hfH : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      AnalyticAt ℝ fH x)
    (hperiodT : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        T (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = T x)
    (hperiodH : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        fH (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = fH x)
    (hbase : ∀ y : Fin a → ℝ,
      (T (Fin.append p₀ y) * (T (Fin.append p₀ y))ᵀ).det ≠ 0)
    (Q : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ))
    (hQτ : ∀ (h : EuclideanSpace ℝ (Fin a))
      (u v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)),
      Q (littlePeriodicCAlphaTranslateIsometry h u) (littlePeriodicCAlphaTranslateIsometry h v) =
        littlePeriodicCAlphaTranslateIsometry h (Q u v)) :
    let C := fun x ↦ (T x)ᵀ * (T x * (T x)ᵀ)⁻¹
    let fA := fun x (q : Fin (N * M)) ↦
      C x (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
    ∃ V₀ : Set (Fin b → ℝ), IsOpen V₀ ∧ p₀ ∈ V₀ ∧ V₀ ⊆ V ∧
      (∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V₀ →
        (T x * (T x)ᵀ).det ≠ 0 ∧ T x * C x = 1) ∧
    let p₀R := collarEuclideanRealEquiv (b + a)
      (toLp 2 (Fin.append p₀ (fun _ : Fin a ↦ (0 : ℝ))))
    ∃ (AR : collarEuclideanRealSubmodule (b + a) →
        LittlePeriodicCAlphaFunction a (N * M) 2 (1 / 2 : ℝ))
      (HR : collarEuclideanRealSubmodule (b + a) →
        LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ))
      (mult : LittlePeriodicCAlphaFunction a (N * M) 2 (1 / 2 : ℝ) →L[ℝ]
        LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ) →L[ℝ]
        LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)),
      AnalyticAt ℝ AR p₀R ∧ AnalyticAt ℝ HR p₀R ∧
      (∀ᶠ p : collarEuclideanRealSubmodule (b + a) in 𝓝 p₀R,
        (∀ y : EuclideanSpace ℝ (Fin a), (AR p).val.toFun y =
          toLp 2 (fun l ↦ fA
            (Fin.append (fun i : Fin b ↦ (p.val (Fin.castAdd a i)).re)
              (fun j : Fin a ↦ y j + (p.val (Fin.natAdd b j)).re)) l)) ∧
        (∀ y : EuclideanSpace ℝ (Fin a), (HR p).val.toFun y =
          toLp 2 (fun l ↦ fH
            (Fin.append (fun i : Fin b ↦ (p.val (Fin.castAdd a i)).re)
              (fun j : Fin a ↦ y j + (p.val (Fin.natAdd b j)).re)) l))) ∧
      (∀ coeff u y, (mult coeff u).val.toFun y =
        hilbertSchmidtCoordinateEvaluation M N (coeff.val.toFun y) (u.val.toFun y)) ∧
      ∀ (ρ : ℝ), 0 ≤ ρ → ∀ (q : ℝ≥0), (q : ℝ) < 1 →
        (∀ᶠ p : collarEuclideanRealSubmodule (b + a) in 𝓝 p₀R,
          let S : Set (LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)) := {x | ‖x‖ ≤ ρ}
          let Φ := fun x ↦ mult (AR p) ((1 / 2 : ℝ) • HR p + Q x x)
          MapsTo Φ S S ∧ LipschitzOnWith q Φ S) →
        ∃ (u : EuclideanSpace ℝ (Fin b) → LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
          (W : Set (EuclideanSpace ℝ (Fin b))), IsOpen W ∧ toLp 2 p₀ ∈ W ∧
          (∀ p ∈ W, ofLp p ∈ V₀ ∧
            (∀ y : EuclideanSpace ℝ (Fin a),
              (AR (collarRealJointParameter b a (p, 0))).val.toFun y =
                toLp 2 (fA (Fin.append (ofLp p) (ofLp y)))) ∧
            (∀ y : EuclideanSpace ℝ (Fin a),
              (HR (collarRealJointParameter b a (p, 0))).val.toFun y =
                toLp 2 (fH (Fin.append (ofLp p) (ofLp y)))) ∧
            ‖u p‖ ≤ ρ ∧
            mult (AR (collarRealJointParameter b a (p, 0)))
              ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)) + Q (u p) (u p)) = u p ∧
            ∀ v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ), ‖v‖ ≤ ρ →
              (mult (AR (collarRealJointParameter b a (p, 0)))
                ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)) + Q v v) = v ↔ u p = v)) ∧
          let _charted := periodicFlatTorusChartedSpace a
          ContMDiffOn ((𝓘(ℝ, EuclideanSpace ℝ (Fin b))).prod
            (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))) (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) ω
            (fun z : EuclideanSpace ℝ (Fin b) × PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) ↦
              littlePeriodicCAlphaTorusValue (u z.1) z.2) (W ×ˢ univ) := by
  dsimp only
  let C := fun x ↦ (T x)ᵀ * (T x * (T x)ᵀ)⁻¹
  let fA := fun x (q : Fin (N * M)) ↦
    C x (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
  obtain ⟨V₀, hV₀, hpV₀, hsub, hcoeff⟩ :=
    collar_real_gram_source_coefficients T V hV p₀ hp₀ hT hperiodT hbase
  refine ⟨V₀, hV₀, hpV₀, hsub, ?_, ?_⟩
  · intro x hx
    exact ⟨(hcoeff x hx).1, (hcoeff x hx).2.1⟩
  · exact collar_source_native_analytic_correction fA fH V₀ hV₀ p₀ hpV₀
      (fun x hx ↦ (hcoeff x hx).2.2.1)
      (fun x hx ↦ hfH x (hsub hx))
      (fun x hx t ↦ (hcoeff x hx).2.2.2 t)
      (fun x hx t ↦ hperiodH x (hsub hx) t) Q hQτ

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_real_gram_native_analytic_correction
