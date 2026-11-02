import GlobalEmbedding.Paper.FreeHopfProductGenerators
import GlobalEmbedding.Paper.FreeInductionEuclideanBlocks
import GlobalEmbedding.Paper.FreePolynomialResidual
import GlobalEmbedding.Paper.FreeInductionSecondCorrection
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# The actual whole-product polynomial with its fixed original residual

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 431–442 and 470–475.
DAG node: `free-induction-polynomial`.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- One fixed genuine polynomial family is jointly native smooth, including its
parameter-zero slice. Compose the actual smooth summands with the product projection,
multiply by the actual parameter and its square, then add. No parameterwise choice
of maps or coefficient functions occurs. Source: Pε at line 474. -/
theorem freePolynomialFamily_joint_contMDiff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}
    (F Z W : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (hW : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ W) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun p : ℝ × M ↦ freePolynomialFamily F Z W p.1 p.2) := by
  exact ((hF.comp contMDiff_snd).add (contMDiff_fst.smul (hZ.comp contMDiff_snd))).add
    ((contMDiff_fst.pow 2).smul (hW.comp contMDiff_snd))

/-- The literal initial block map F₀=(H,f,0) has exact full partial Gram I.
Use the actual generator/orbit derivative equality and the shared Euclidean block
derivative. Old-factor basicness of f and active-factor basicness of H make the mixed
rows zero. The old Gram is exactly the input old Gram, and the active row is the
genuine squared norm of the unit velocity. Source: F₀ in lines 431–433. -/
theorem free_induction_base_gram {m K : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (H : FreeHopfProduct C → EuclideanSpace ℝ (Fin K))
    (f : FreeHopfProduct C → Planar)
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
    (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hHbasic : ∀ t x, H (freeHopfProductFlow C (Fin.last m) t x) = H x)
    (hfbasic : ∀ (i : Fin m) t x, f (freeHopfProductFlow C i.castSucc t x) = f x)
    (hunit : ∀ x, ‖freeHopfDeriv C (Fin.last m) f x‖ = 1)
    (hGram : ∀ x, Matrix.gram ℝ (fun i : Fin m ↦ freeHopfDeriv C i.castSucc H x) = 1) :
    ∀ x, balancedGeometry (fun y ↦ freeInductionBlock K m (H y) (f y) 0)
      (freeInductionBlock_contMDiff K m H f (fun _ ↦ 0) hH hf contMDiff_const)
      (freeHopfGeneratorSection C) x = 1 := by
  let F := fun y ↦ freeInductionBlock K m (H y) (f y) 0
  have hF := freeInductionBlock_contMDiff K m H f (fun _ ↦ 0) hH hf contMDiff_const
  have hd (i : Fin (m + 1)) (x : FreeHopfProduct C) :
      balancedDirectionalDerivative F (freeHopfGeneratorSection C i) x =
        freeInductionBlock K m (freeHopfDeriv C i H x) (freeHopfDeriv C i f x) 0 := by
    change mvfderiv (freeHopfModel C) F x (freeHopfGenerator C i x) = _
    rw [freeHopfGenerator_mvfderiv C i F hF x]
    have hh := freeInductionBlock_orbitDeriv (freeHopfProductSmoothFlow C i) K m H f
      (fun _ ↦ 0) hH hf contMDiff_const x
    simpa only [F, freeHopfDeriv, freeHopfProductSmoothFlow, orbitDeriv, deriv_const] using hh
  have hlast (x : FreeHopfProduct C) : freeHopfDeriv C (Fin.last m) H x = 0 := by
    unfold freeHopfDeriv orbitDeriv
    simp only [hHbasic, deriv_const]
  have hold (i : Fin m) (x : FreeHopfProduct C) : freeHopfDeriv C i.castSucc f x = 0 := by
    unfold freeHopfDeriv orbitDeriv
    simp only [hfbasic, deriv_const]
  intro x
  ext i j
  change inner ℝ (balancedDirectionalDerivative F (freeHopfGeneratorSection C i) x)
      (balancedDirectionalDerivative F (freeHopfGeneratorSection C j) x) =
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i j
  rw [hd i x, hd j x, freeInductionBlock_inner]
  simp only [inner_zero_left, add_zero]
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp [hlast, hunit]
    · simp [hlast, hold, Ne.symm (Fin.castSucc_ne_last j)]
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp [hlast, hold]
    · have hh := congrArg (fun A : Matrix (Fin m) (Fin m) ℝ ↦ A i j) (hGram x)
      change inner ℝ (freeHopfDeriv C i.castSucc H x) (freeHopfDeriv C j.castSucc H x) =
        (1 : Matrix (Fin m) (Fin m) ℝ) i j at hh
      simpa only [hold, inner_zero_left, add_zero, Matrix.one_apply, Fin.castSucc_inj] using hh

/-- The actual induction data produce one native smooth quadratic polynomial
family with exactly the original fixed cubic/quartic residual. The old Gram and unit
active velocity prove the true base identity. The actual second-cancellation theorem
constructs W, and the proved genuine polynomial expansion cancels degrees one and two.
The coefficients are literally symmetrized DZ/DW pairings and the actual Gram of W;
the same W and coefficients serve every real parameter, including zero, at all orders.
No desired W, residual coefficients, polynomial family or solver is an input. The
first-cancellation hypothesis is discharged by the actual W2 moving-frame Z theorem.
Source: thm:free, the polynomial residual in lines 474–475. -/
theorem free_induction_polynomial {m K : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (H : FreeHopfProduct C → EuclideanSpace ℝ (Fin K))
    (f : FreeHopfProduct C → Planar)
    (Z : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
    (κ : FreeHopfProduct C → ℝ)
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
    (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hZ : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ Z)
    (hκ : ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hHbasic : ∀ t x, H (freeHopfProductFlow C (Fin.last m) t x) = H x)
    (hfbasic : ∀ (i : Fin m) t x, f (freeHopfProductFlow C i.castSucc t x) = f x)
    (hind : ∀ x, LinearIndependent ℝ
      (freeFlowColumns (fun i : Fin m ↦ freeHopfProductFlow C i.castSucc) H x))
    (hunit : ∀ x, ‖freeHopfDeriv C (Fin.last m) f x‖ = 1)
    (hacc : ∀ x,
      freeHopfDeriv C (Fin.last m) (freeHopfDeriv C (Fin.last m) f) x =
        κ x • planarQuarterTurn (freeHopfDeriv C (Fin.last m) f x))
    (hn : ∀ x, ∃ s : ℝ, κ (freeHopfProductFlow C (Fin.last m) s x) ≠ 0)
    (hperiod : ∀ (i : Fin m) x, orbitAverage (freeHopfProductFlow C (Fin.last m))
      (fun y ↦ inner ℝ (freeHopfDeriv C i.castSucc Z y)
        (freeHopfDeriv C (Fin.last m) Z y)) x = 0)
    (hGram : ∀ x, Matrix.gram ℝ (fun i : Fin m ↦ freeHopfDeriv C i.castSucc H x) = 1)
    (hlinear : ∀ x, freeMetricCrossTerm (fun y ↦ freeInductionBlock K m (H y) (f y) 0) Z
      (freeHopfGeneratorSection C) x = 0) :
    let F0 := fun y ↦ freeInductionBlock K m (H y) (f y) 0
    let hF0 := freeInductionBlock_contMDiff K m H f (fun _ ↦ 0) hH hf contMDiff_const
    ∃ (W : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
      (hW : ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W),
      ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞
        (fun p : ℝ × FreeHopfProduct C ↦ freePolynomialFamily F0 Z W p.1 p.2) ∧
      (∀ ε x, balancedGeometry (freePolynomialFamily F0 Z W ε)
        (freePolynomialFamily_contMDiff F0 Z W hF0 hZ hW ε)
        (freeHopfGeneratorSection C) x =
          1 + ε ^ 3 • freeMetricCrossTerm Z W (freeHopfGeneratorSection C) x +
            ε ^ 4 • balancedGeometry W hW (freeHopfGeneratorSection C) x) ∧
      (∀ i j, ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞
        (fun x ↦ freeMetricCrossTerm Z W (freeHopfGeneratorSection C) x i j)) ∧
      (∀ i j, ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞
        (fun x ↦ balancedGeometry W hW (freeHopfGeneratorSection C) x i j)) := by
  let F0 := fun y ↦ freeInductionBlock K m (H y) (f y) 0
  have hF0 := freeInductionBlock_contMDiff K m H f (fun _ ↦ 0) hH hf contMDiff_const
  obtain ⟨W, hW, hquad⟩ := free_induction_second_correction C H f Z κ hH hf hZ hκ
    hHbasic hfbasic hind hunit hacc hn hperiod
  refine ⟨W, hW, freePolynomialFamily_joint_contMDiff F0 Z W hF0 hZ hW, ?_, ?_, ?_⟩
  · exact freePolynomialFamily_residual F0 Z W hF0 hZ hW (freeHopfGeneratorSection C)
      (free_induction_base_gram C H f hH hf hHbasic hfbasic hunit hGram) hlinear hquad
  · exact freeMetricCrossTerm_entry_contMDiff Z W hZ hW (freeHopfGeneratorSection C)
  · exact balancedGeometry_entry_contMDiff W hW (freeHopfGeneratorSection C)

#print axioms freePolynomialFamily_joint_contMDiff
#print axioms free_induction_base_gram
#print axioms free_induction_polynomial

end GlobalEmbedding.Paper
