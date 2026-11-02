import GlobalEmbedding.Paper.FreeInductionNativeData
import GlobalEmbedding.Paper.FreeHopfBalancedCorrection
import GlobalEmbedding.Paper.FreeUniformPivotEstimates
import GlobalEmbedding.Targets.OrthogonalPrimitives

/-!
# Genuine simultaneous choices for the original free induction

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines431–475.
DAG: `free-induction-data-exists`; exclusive worker W6.
All matrix, cofactor, pivot and polynomial outputs below share the same choices.
-/

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace Matrix.Norms.Elementwise

namespace GlobalEmbedding.Paper

variable {m K : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]

local instance freeDataExistsOldPositive (i : Fin m) :
    Fact (0 < freeHopfOldDimensions C i) := inferInstanceAs (Fact (0 < C i.castSucc))

local instance freeDataExistsMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Original dimensions and the unchanged old selector hypothesis construct all
actual induction data simultaneously. Choose f/P/η from the full accepted original
matrix proposition in dimension m+1≥2. On these same data the accepted genuine
pivot theorem constructs A/n and one positive δ₀, buffer d₀ and coercivity/pivot
constants. With these fixed choices, the actual native-data polynomial theorem
constructs W and the joint smooth family with its exact original residual.
No auxiliary map, period, pivot, chosen δ or desired W is an input. The actual
pointwise limiting-rank and normalized inverse remain the separately owned next
steps; this theorem keeps their inputs fixed. Source: lines431–475. -/
theorem freeHopf_induction_data_exists (hm : 1 ≤ m) (hC : ∀ i, 2 ≤ C i)
    (H ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hIH : FreeSelectorProperties (freeHopfModel (freeHopfOldDimensions C))
      (freeHopfProductFlow (freeHopfOldDimensions C)) H ν) :
    ∃ (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
      (P : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
      (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
      (_hf : MatrixPlanarSelectorProperties f)
      (_hP : ContMDiff (planarHopfModel (C (Fin.last m)))
        𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
      (_hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η),
    let Q := orbitDeriv planarHopfFlow P
    let κ := planarOrbitCurvature planarHopfFlow f
    (∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin (m + 1)) ℝ) ∧
    (∀ z, orbitAverage planarHopfFlow Q z = 0) ∧
    (∀ z, orbitAverage planarHopfFlow (fun w ↦ (P w).transpose * Q w) z = 0) ∧
    (∀ z, orbitAverage planarHopfFlow η z = 0) ∧
    (∀ z, orbitAverage planarHopfFlow
      (fun w ↦ η w ^ 2 • ((Q w).transpose * orbitDeriv planarHopfFlow Q w)) z = 0) ∧
    (∀ z, κ z = 0 → orbitDeriv planarHopfFlow Q z = 0) ∧
    (∀ z, κ z = 0 → orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow η) z = 1) ∧
    ∃ (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
      (_hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
      (_hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n),
    (∀ x, LinearIndependent ℝ (fun i ↦ freeHopfDeriv (freeHopfOldDimensions C) i A x)) ∧
    (∀ x, ‖n x‖ = 1) ∧
    (∀ x i, ⟪n x, freeHopfDeriv (freeHopfOldDimensions C) i A x⟫ = 0) ∧
    ∃ δ₀ d₀ lam B : ℝ, 0 < δ₀ ∧ 0 < d₀ ∧ 0 < lam ∧ 0 < B ∧
      (∀ p : FreeHopfProduct (freeHopfOldDimensions C) × PlanarHopfSphere (C (Fin.last m)),
        (∀ v, lam * ‖v‖ ^ 2 ≤
          ‖freePivotMixedFrame (freeHopfOldDimensions C) Q η A n δ₀ p v‖ ^ 2) ∧
        ‖freePivotNormal (freeHopfOldDimensions C) Q η A n δ₀ p -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1)‖ ≤ B * δ₀ ∧
        (κ p.2 = 0 → |⟪freePivotNormal (freeHopfOldDimensions C) Q η A n δ₀ p,
          freePivotActiveSecond (freeHopfOldDimensions C) P Q η A n δ₀ p⟫ - δ₀| ≤
            B * δ₀ ^ 2) ∧
        (|κ p.2| < d₀ → δ₀ / 4 ≤
          ⟪freePivotNormal (freeHopfOldDimensions C) Q η A n δ₀ p,
            freePivotActiveSecond (freeHopfOldDimensions C) P Q η A n δ₀ p⟫)) ∧
      let F0 := freeHopfInductionBase C H f
      let Z := freeHopfInductionZ C ν P Q η δ₀ A n
      ∃ (W : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
        (hW : ContMDiff (freeHopfModel C)
          𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W),
        ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞
          (fun p : ℝ × FreeHopfProduct C ↦ freePolynomialFamily F0 Z W p.1 p.2) ∧
        (∀ ε x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i
          (freePolynomialFamily F0 Z W ε) x) =
          1 + ε ^ 3 • freeMetricCrossTerm Z W (freeHopfGeneratorSection C) x +
            ε ^ 4 • balancedGeometry W hW (freeHopfGeneratorSection C) x) ∧
        (∀ i j, ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞
          (fun x ↦ freeMetricCrossTerm Z W (freeHopfGeneratorSection C) x i j)) ∧
        (∀ i j, ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞
          (fun x ↦ balancedGeometry W hW (freeHopfGeneratorSection C) x i j)) := by
  obtain ⟨f, P, η, hf, hP, hη, hSO, havQ, hperiod, hmean, hquad, hstationary, _, haccel⟩ :=
    orthogonal_primitives_scalar_moments (C (Fin.last m)) (m + 1) (hC _) (by omega)
  obtain ⟨A, n, hA, hn, hLI, hunit, hperp, δ₀, d₀, lam, B, hδ, hd, hlam, hB, hpivot⟩ :=
    free_matrix_uniform_pivot_exists (freeHopfOldDimensions C) f hf P hP η hη
      hSO hstationary haccel
  have hQ := contMDiff_orbitDeriv planarHopfFlow
    (planarHopfFlow_contMDiff (C (Fin.last m))) P hP
  obtain ⟨W, hW, hjoint, hres, hS3, hS4⟩ := freeHopf_induction_polynomial C H ν hIH f hf
    P (orbitDeriv planarHopfFlow P) hP hQ (fun _ ↦ rfl) hSO hperiod
    η hη hmean hquad δ₀ A n hA hn hunit hperp
  refine ⟨f, P, η, hf, hP, hη, hSO, havQ, hperiod, hmean, hquad, hstationary, haccel,
    A, n, hA, hn, hLI, hunit, hperp, δ₀, d₀, lam, B, hδ, hd, hlam, hB, hpivot,
    W, hW, hjoint, ?_, hS3, hS4⟩
  intro ε x
  have hF0 := freeHopfInductionBase_contMDiff C H hIH.1 f hf.smooth
  have hZ := freeHopfInductionZ_contMDiff C ν hIH.2.1 P (orbitDeriv planarHopfFlow P)
    hP hQ η hη δ₀ A n hA hn
  exact (freeHopf_geometry_eq_gram C _
    (freePolynomialFamily_contMDiff _ _ W hF0 hZ hW ε) x).symm.trans (hres ε x)

#print axioms freeHopf_induction_data_exists

end GlobalEmbedding.Paper
