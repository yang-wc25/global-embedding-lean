import GlobalEmbedding.Paper.MatrixScalarMomentCalculus

/-!
# Interpreting the actual smooth basic scalar root

Source: `main.tex`, `prop:matrix`, lines358–365.
DAG: `matrix-scalar-root-interpretation`.
Basicness turns the literal fixed-coefficient orbit equation into the actual
moments of the genuinely selected scalar function.
-/

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The genuinely selected scalar function has both exact original moments and
full native-flat correction when its actual smooth basic coefficients solve the
literal period equation.

Proof: joint native smoothness of the actual ansatz gives actual smoothness of
eta. Basicness makes c(R_t z)=c(z), so the actual integral of the true eta moment
integrands equals the solved fixed-coefficient equation. Coordinate projections
commute with these actual integrable period maps, giving both the scalar mean
and the actual A-valued quadratic moment. The already proved native smooth
cutoff-multiple theorem gives full flatness of eta minus its actual trial.
Source: `prop:matrix`, lines358–365. -/
theorem matrix_scalar_moments_of_basic_root {C m : ℕ} [Fact (0 < C)]
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ u : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u)
    (c : PlanarHopfSphere C → MatrixScalarCoefficients m)
    (hc : ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixScalarCoefficients m) ∞ c)
    (hbasic : ∀ s z, c (planarHopfFlow s z) = c z)
    (hroot : ∀ z, matrixScalarMomentMap A κ u z (c z) = 0) :
    let η := fun z ↦ matrixScalarAnsatz A κ u (c z) z
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η ∧
    (∀ z, orbitAverage planarHopfFlow η z = 0) ∧
    (∀ z, orbitAverage planarHopfFlow (fun w ↦ η w ^ 2 • A w) z = 0) ∧
    ManifoldFlatOn (I := planarHopfModel C) (fun z ↦ η z - u z) {z | κ z = 0} := by
  let η := fun z ↦ matrixScalarAnsatz A κ u (c z) z
  have hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η :=
    (matrixScalarAnsatz_contMDiff A hA κ u hκ hu).comp (contMDiff_id.prodMk hc)
  have hvalues : Continuous (fun w ↦ matrixScalarMomentValues A (η w) w) :=
    (matrixScalarMomentValues_continuous A hA.continuous).comp
      (hη.continuous.prodMk continuous_id)
  have hH (z : PlanarHopfSphere C) :
      orbitAverage planarHopfFlow (fun w ↦ matrixScalarMomentValues A (η w) w) z = 0 := by
    calc
      _ = matrixScalarMomentMap A κ u z (c z) := by
        unfold orbitAverage matrixScalarMomentMap
        apply intervalIntegral.integral_congr
        intro t _
        simp only [η, hbasic]
      _ = 0 := hroot z
  have hInt (z : PlanarHopfSphere C) : IntervalIntegrable
      (fun t ↦ matrixScalarMomentValues A (η (planarHopfFlow t z)) (planarHopfFlow t z))
      volume 0 1 := by
    have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
      ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
    exact (hvalues.comp hR).intervalIntegrable 0 1
  refine ⟨hη, ?_, ?_, matrixScalarAnsatz_sub_base_flat A hA κ u hκ hu c hc⟩
  · intro z
    have hproj := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Option (Fin m)) none)
      |>.intervalIntegral_comp_comm (hInt z)
    calc
      orbitAverage planarHopfFlow η z =
          (EuclideanSpace.proj (𝕜 := ℝ) (ι := Option (Fin m)) none)
            (orbitAverage planarHopfFlow (fun w ↦ matrixScalarMomentValues A (η w) w) z) := by
        unfold orbitAverage
        rw [← hproj]
        rfl
      _ = 0 := by rw [hH z]; rfl
  · intro z
    have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
      ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
    have hi : IntervalIntegrable
        (fun t ↦ η (planarHopfFlow t z) ^ 2 • A (planarHopfFlow t z)) volume 0 1 :=
      (((hη.pow 2).smul hA).continuous.comp hR).intervalIntegrable 0 1
    ext i
    have hp := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin m) i).intervalIntegral_comp_comm hi
    have hq := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Option (Fin m)) (some i))
      |>.intervalIntegral_comp_comm (hInt z)
    change (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin m) i)
      (orbitAverage planarHopfFlow (fun w ↦ η w ^ 2 • A w) z) = 0
    calc
      _ = (EuclideanSpace.proj (𝕜 := ℝ) (ι := Option (Fin m)) (some i))
          (orbitAverage planarHopfFlow (fun w ↦ matrixScalarMomentValues A (η w) w) z) := by
        unfold orbitAverage
        rw [← hp, ← hq]
        rfl
      _ = 0 := by rw [hH z]; rfl

#print axioms matrix_scalar_moments_of_basic_root

end GlobalEmbedding.Paper
