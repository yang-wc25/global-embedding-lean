import GlobalEmbedding.Paper.CollarSourceRealHolderFamily
import GlobalEmbedding.Paper.CollarOriginalRealAnalyticFixedPoints

/-!
# Actual real-source analytic correction for the collar fixed-point equation

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
equation (5.2), proof lines 524–534.
-/

open Set Filter WithLp
open scoped Topology NNReal

namespace GlobalEmbedding.Paper

/-- Original jointly real analytic periodic matrix/forcing coefficients and the actual
bounded REAL Q construct the original real coefficient families and an analytic correction
whenever their original real norm ball is invariant and uniformly contracting.

Source: Proposition `prop:collar`, equation (5.2), proof lines 524–534. Construct both actual
complex coefficient norm series directly from the original real source data on its actual
open real base domain. Their canonical shared real parameter submodule gives actual original
real little coefficient families, with exact translated source lifts, actual real/complex
agreement and exact norm equality. Construct actual real matrix multiplication, complexify
the actual bounded real Q and use the full original-norm real-form isometry. Original real
ball invariance and Lipschitz q transfer with unchanged q. The actual analytic fixed-point
construction then returns a genuine complex analytic branch whose real restriction is the
unique original real solution in that same original norm ball, also at radius zero/boundary.
No complex extension, Holder membership, analytic operator family, complex Q, real-family
matching data or complex contraction estimate is an input. The paper-specific bounded REAL Q
construction and original real small-ball estimates remain explicit separate obligations. -/
theorem collar_source_analytic_fixed_points {b a M N : ℕ}
    (fA : (Fin (b + a) → ℝ) → (Fin (N * M) → ℝ))
    (fH : (Fin (b + a) → ℝ) → (Fin M → ℝ))
    (V : Set (Fin b → ℝ)) (hV : IsOpen V) (p₀ : Fin b → ℝ) (hp₀ : p₀ ∈ V)
    (hfA : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      AnalyticAt ℝ fA x)
    (hfH : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      AnalyticAt ℝ fH x)
    (hperiodA : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        fA (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = fA x)
    (hperiodH : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        fH (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = fH x)
    (Q : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ)) :
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
        ∃ ψ : EuclideanSpace ℂ (Fin (b + a)) → CollarComplexHolderSpace a N 2 (1 / 2 : ℝ),
          AnalyticAt ℂ ψ (p₀R : EuclideanSpace ℂ (Fin (b + a))) ∧
          ∀ᶠ p : collarEuclideanRealSubmodule (b + a) in 𝓝 p₀R,
            ∃ u : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ), ‖u‖ ≤ ρ ∧
              mult (AR p) ((1 / 2 : ℝ) • HR p + Q u u) = u ∧
              (∀ y, collarComplexHolderFunction (ψ p.val) y =
                toLp 2 (fun l ↦ ((u.val.toFun y l : ℝ) : ℂ))) ∧
              (∀ v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ), ‖v‖ ≤ ρ →
                (mult (AR p) ((1 / 2 : ℝ) • HR p + Q v v) = v ↔ u = v)) := by
  dsimp only
  let p₀R := collarEuclideanRealEquiv (b + a)
    (toLp 2 (Fin.append p₀ (fun _ : Fin a ↦ (0 : ℝ))))
  obtain ⟨A, AR, hA, hAR, hAnear⟩ :=
    collar_source_real_holder_family fA V hV p₀ hp₀ hfA hperiodA
  obtain ⟨H, HR, hH, hHR, hHnear⟩ :=
    collar_source_real_holder_family fH V hV p₀ hp₀ hfH hperiodH
  have hmatch : ∀ᶠ p : collarEuclideanRealSubmodule (b + a) in 𝓝 p₀R,
      (∀ y, collarComplexHolderFunction (A p.val) y =
        toLp 2 (fun i ↦ (((AR p).val.toFun y i : ℝ) : ℂ))) ∧
      (∀ y, collarComplexHolderFunction (H p.val) y =
        toLp 2 (fun i ↦ (((HR p).val.toFun y i : ℝ) : ℂ))) := by
    filter_upwards [hAnear, hHnear] with p hpA hpH
    exact ⟨hpA.2.1, hpH.2.1⟩
  obtain ⟨mult, hmult, hbranch⟩ := collar_original_real_analytic_fixed_points
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (collarEuclideanRealSubmodule (b + a)) p₀R A H AR HR Q hA hH hmatch
  refine ⟨AR, HR, mult, hAR, hHR, ?_, hmult, hbranch⟩
  filter_upwards [hAnear, hHnear] with p hpA hpH
  exact ⟨hpA.1, hpH.1⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_source_analytic_fixed_points
