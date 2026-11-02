import GlobalEmbedding.Paper.CollarEuclideanCoefficientComplexExtension
import GlobalEmbedding.Paper.CollarTranslatedCoefficientPowerSeries
import GlobalEmbedding.Paper.CollarCoefficientMultiplierAnalytic

/-!
# Actual real-source holomorphic little Hölder coefficient family

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. DAG node: `collar-holomorphic-holder-coefficients`.
-/

open Set WithLp
open scoped NNReal ENNReal

namespace GlobalEmbedding.Paper

/-- Actual jointly real analytic periodic source coefficients construct the actual complex
little c^{2,1/2} family for (p,α)↦[y↦g_C(p,y+α)], with a genuine norm power series and complex
Fréchet holomorphy on a positive parameter neighborhood.

Source: Proposition `prop:collar`, proof lines 530–534. Construct the actual source complex
extension from the original real-valued coefficients, preserving exact real agreement in the
original open base domain. Actual complex linear coordinate projections encode the joint
base/translation parameters in one Euclidean parameter space. The actual flat torus is compact,
so construct its finite diameter bound. The translated coefficient theorem constructs the
actual little-space norm power series with its original norm. That genuine complex norm series
gives both AnalyticOnNhd and complex Fréchet differentiability throughout the parameter ball.
No Hölder membership, complex extension, norm coefficient bounds or holomorphic family is
an input. The source complex value model is the actual Euclidean norm model.
The last conclusion constructs the actual bounded complex matrix coefficient-to-operator map,
with exact pointwise matrix action and operator-norm analyticity for every analytic coefficient
family. Applying the source coefficient conclusion to matrix coordinates therefore proves the
original matrix coefficient clause as well. -/
theorem collar_holomorphic_holder_coefficients {b a N : ℕ}
    (f : (Fin (b + a) → ℝ) → (Fin N → ℝ)) (V : Set (Fin b → ℝ))
    (hV : IsOpen V) (p₀ : Fin b → ℝ) (hp₀ : p₀ ∈ V)
    (hf : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      AnalyticAt ℝ f x)
    (hperiod : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        f (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = f x) :
    ∃ (U : Set (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)))
      (g : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) → EuclideanSpace ℂ (Fin N))
      (ε : ℝ) (ρ : ℝ≥0)
      (F : EuclideanSpace ℂ (Fin (b + a)) → CollarComplexHolderSpace a N 2 (1 / 2 : ℝ))
      (q : FormalMultilinearSeries ℂ (EuclideanSpace ℂ (Fin (b + a)))
        (CollarComplexHolderSpace a N 2 (1 / 2 : ℝ))),
      0 < ε ∧ 0 < ρ ∧ IsOpen U ∧ AnalyticOnNhd ℂ g U ∧
      (∀ (p : Fin b → ℝ) (y : Fin a → ℝ), (∀ i, |p i - p₀ i| < ε) → p ∈ V ∧
        g (toLp 2 (fun i ↦ (p i : ℂ)), toLp 2 (fun j ↦ (y j : ℂ))) =
          toLp 2 (fun l ↦ (f (Fin.append p y) l : ℂ))) ∧
      HasFPowerSeriesOnBall F q
        (toLp 2 (Fin.append (fun i ↦ (p₀ i : ℂ)) (fun _ : Fin a ↦ 0))) (ρ : ℝ≥0∞) ∧
      (∀ z ∈ Metric.eball
        (toLp 2 (Fin.append (fun i ↦ (p₀ i : ℂ)) (fun _ : Fin a ↦ 0))) (ρ : ℝ≥0∞),
        AnalyticAt ℂ F z ∧ DifferentiableAt ℂ F z) ∧
      (∀ z ∈ Metric.eball (0 : EuclideanSpace ℂ (Fin (b + a))) (ρ : ℝ≥0∞),
        ∀ y : EuclideanSpace ℝ (Fin a),
        let w := toLp 2 (Fin.append (fun i ↦ (p₀ i : ℂ)) (fun _ : Fin a ↦ 0)) + z
        collarComplexHolderFunction (F w) y =
          g (toLp 2 (fun i : Fin b ↦ w (Fin.castAdd a i)),
            toLp 2 (fun j : Fin a ↦ (y j : ℂ) + w (Fin.natAdd b j)))) ∧
      (∀ M R : ℕ, ∃ C : CollarComplexHolderSpace a (R * M) 2 (1 / 2 : ℝ) →L[ℂ]
          CollarComplexHolderSpace a M 2 (1 / 2 : ℝ) →L[ℂ]
          CollarComplexHolderSpace a R 2 (1 / 2 : ℝ),
        (∀ coeff u (y : EuclideanSpace ℝ (Fin a)) (i : Fin R),
          collarComplexHolderFunction (C coeff u) y i =
            ∑ j : Fin M, collarComplexHolderFunction coeff y (finProdFinEquiv (i, j)) *
              collarComplexHolderFunction u y j) ∧
        (∀ (A : EuclideanSpace ℂ (Fin (b + a)) → CollarComplexHolderSpace a (R * M) 2 (1 / 2 : ℝ))
          (z : EuclideanSpace ℂ (Fin (b + a))), AnalyticAt ℂ A z →
            AnalyticAt ℂ (fun w ↦ C (A w)) z)) := by
  obtain ⟨U, g, ε, hε, hU, hg, hbase, hinv, hgp, hreal⟩ :=
    collar_euclidean_coefficient_complex_extension f V hV p₀ hp₀ hf hperiod
  let πₗ : EuclideanSpace ℂ (Fin (b + a)) →ₗ[ℂ] EuclideanSpace ℂ (Fin b) :=
    { toFun := fun z ↦ toLp 2 (fun i ↦ z (Fin.castAdd a i))
      map_add' := by intro z w; ext i; rfl
      map_smul' := by intro c z; ext i; rfl }
  let Aₗ : EuclideanSpace ℂ (Fin (b + a)) →ₗ[ℂ] EuclideanSpace ℂ (Fin a) :=
    { toFun := fun z ↦ toLp 2 (fun j ↦ z (Fin.natAdd b j))
      map_add' := by intro z w; ext i; rfl
      map_smul' := by intro c z; ext i; rfl }
  let π := πₗ.toContinuousLinearMap
  let A := Aₗ.toContinuousLinearMap
  let z₀ : EuclideanSpace ℂ (Fin (b + a)) :=
    toLp 2 (Fin.append (fun i ↦ (p₀ i : ℂ)) (fun _ : Fin a ↦ 0))
  have hπ₀ : π z₀ = toLp 2 (fun i ↦ (p₀ i : ℂ)) := by ext i; simp [π, πₗ, z₀]
  have hA₀ : A z₀ = 0 := by ext i; simp [A, Aₗ, z₀]
  have hslice (y : EuclideanSpace ℝ (Fin a)) :
      (π z₀, toLp 2 (fun i ↦ (y i : ℂ)) + A z₀) ∈ U := by
    rw [hπ₀, hA₀, add_zero]
    exact hbase y
  have hcompact : IsCompact (univ : Set (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))) := by
    have hrange : Set.range (toLp 2 : (Fin a → AddCircle (1 : ℝ)) →
        PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) = univ :=
      Set.range_eq_univ.mpr (WithLp.equiv 2 (Fin a → AddCircle (1 : ℝ))).symm.surjective
    rw [← hrange]
    exact isCompact_range (PiLp.continuous_toLp _ _)
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  obtain ⟨ρ, hρ, F, q, hFq, _, _, _, hF⟩ :=
    collar_translated_coefficient_power_series (k := 2) (α := (1 / 2 : ℝ))
      g U hU hg hinv hgp π A z₀ hslice (by norm_num) D
      (fun x y ↦ hD (mem_univ _) (mem_univ _))
  refine ⟨U, g, ε, ρ, F, q, hε, hρ, hU, hg, hreal, hFq, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨hFq.analyticAt_of_mem hz, (hFq.analyticAt_of_mem hz).differentiableAt⟩
  · intro z hz y
    exact hF z hz y
  · intro M R
    let A₀ : EuclideanSpace ℂ (Fin (b + a)) → CollarComplexHolderSpace a (R * M) 2 (1 / 2 : ℝ) :=
      fun _ ↦ 0
    obtain ⟨C, hC, _⟩ := collar_coefficient_multiplier_analytic
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      A₀ 0 analyticAt_const
    refine ⟨C, hC, ?_⟩
    intro A z hA
    exact (C.analyticAt (A z)).comp hA

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_holomorphic_holder_coefficients
