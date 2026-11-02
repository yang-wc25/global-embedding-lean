import GlobalEmbedding.Paper.FreeInductionDisplacement
import GlobalEmbedding.Paper.FreeHopfProductSuccessor
import GlobalEmbedding.Paper.FreeHopfUnitComplements
import GlobalEmbedding.Paper.FreeHopfDerivativeCommute
import GlobalEmbedding.Paper.FreePolynomialResidual

/-!
# The literal displacement and mixed periods on the original successor Hopf product

Source: `main.tex`, `thm:free`, lines431–453.
DAG: `free-mixed-period-identity`; exclusive owner W2.
Only the accepted genuine source split and the same accepted target block are used.
-/

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace Matrix.Norms.Elementwise

namespace GlobalEmbedding.Paper

variable {m k : ℕ} (C : Fin (m + 1) → ℕ)

local instance freeMixedNativeMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Pullback of the literal old derivative through the genuine source split.
This is equality of the actual real orbit curves, requiring no extra regularity.
Source: the old factors in the induction, main.tex431–453. -/
theorem freeHopfDeriv_split_old
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : FreeHopfProduct (freeHopfOldDimensions C) ×
      PlanarHopfSphere (C (Fin.last m)) → F) (i : Fin m) (x : FreeHopfProduct C) :
    freeHopfDeriv C i.castSucc (fun y ↦ g (freeHopfProductSplit C y)) x =
      orbitDeriv (fun t p ↦
        (freeHopfProductFlow (freeHopfOldDimensions C) i t p.1, p.2))
        g (freeHopfProductSplit C x) := by
  unfold freeHopfDeriv orbitDeriv
  congr 1
  funext t
  dsimp only
  rw [freeHopfProductSplit_flow_old]

/-- Pullback of the literal new derivative through the same genuine source split.
Source: the last factor in the induction, main.tex431–453. -/
theorem freeHopfDeriv_split_last
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : FreeHopfProduct (freeHopfOldDimensions C) ×
      PlanarHopfSphere (C (Fin.last m)) → F) (x : FreeHopfProduct C) :
    freeHopfDeriv C (Fin.last m) (fun y ↦ g (freeHopfProductSplit C y)) x =
      orbitDeriv (fun t p ↦ (p.1, planarHopfFlow t p.2))
        g (freeHopfProductSplit C x) := by
  unfold freeHopfDeriv orbitDeriv
  congr 1
  funext t
  dsimp only
  rw [freeHopfProductSplit_flow_last]

/-- The actual derivative pullback for every original factor, with the same
old factors and the actual new last factor. Source: main.tex431–453. -/
theorem freeHopfDeriv_split
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : FreeHopfProduct (freeHopfOldDimensions C) ×
      PlanarHopfSphere (C (Fin.last m)) → F) (i : Fin (m + 1)) (x : FreeHopfProduct C) :
    freeHopfDeriv C i (fun y ↦ g (freeHopfProductSplit C y)) x =
      orbitDeriv (Fin.lastCases (fun t p ↦ (p.1, planarHopfFlow t p.2))
        (fun j t p ↦ (freeHopfProductFlow (freeHopfOldDimensions C) j t p.1, p.2)) i)
        g (freeHopfProductSplit C x) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.lastCases_last] using freeHopfDeriv_split_last C g x
  · simpa only [Fin.lastCases_castSucc] using freeHopfDeriv_split_old C g j x

/-- Literal period integrals pull back through the same actual last-factor split.
Source: the physical mixed quadratic average in main.tex444–453. -/
theorem freeHopfAverage_split_last
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : FreeHopfProduct (freeHopfOldDimensions C) ×
      PlanarHopfSphere (C (Fin.last m)) → F) (x : FreeHopfProduct C) :
    orbitAverage (freeHopfProductFlow C (Fin.last m))
      (fun y ↦ g (freeHopfProductSplit C y)) x =
      orbitAverage (fun t p ↦ (p.1, planarHopfFlow t p.2))
        g (freeHopfProductSplit C x) := by
  unfold orbitAverage
  simp only [freeHopfProductSplit_flow_last]

/-- The same literal base map on the original Fin-snoc product, with no new carrier.
Source: F0=(H,f,0_m), main.tex431. -/
def freeHopfInductionBase
    (H₀ : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar) :
    FreeHopfProduct C → EuclideanSpace ℝ (Fin (k + (2 + m))) :=
  fun x ↦ freeInductionBase H₀ f (freeHopfProductSplit C x)

/-- The same literal moving-frame displacement on the original Fin-snoc product.
Source: Z=T(PA+delta eta Qn), main.tex437–440. -/
def freeHopfInductionZ
    (ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ) (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1))) :
    FreeHopfProduct C → EuclideanSpace ℝ (Fin (k + (2 + m))) :=
  fun x ↦ freeInductionZ ν P Q η δ A n (freeHopfProductSplit C x)

variable [∀ i, Fact (0 < C i)]

local instance freeMixedNativeOldPositive (i : Fin m) :
    Fact (0 < freeHopfOldDimensions C i) := inferInstanceAs (Fact (0 < C i.castSucc))

/-- The actual base map on the original product is native smooth at every order.
Source: smooth F0 in main.tex431; compose its actual product construction with the
accepted native source split. -/
theorem freeHopfInductionBase_contMDiff
    (H₀ : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hH : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ H₀)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ f) :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k + (2 + m)))) ∞
      (freeHopfInductionBase C H₀ f) :=
  (freeInductionBase_contMDiff H₀ hH f hf).comp (freeHopfProductSplit_contMDiff C)

/-- The actual moving-frame Z is globally native smooth on the original product.
The source split is genuine and the target is the fixed common Euclidean block.
Source: the actual displacement in main.tex437–440. -/
theorem freeHopfInductionZ_contMDiff
    (ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n) :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k + (2 + m)))) ∞
      (freeHopfInductionZ C ν P Q η δ A n) :=
  (freeInductionZ_contMDiff ν hν P Q hP hQ η hη δ A n hA hn).comp
    (freeHopfProductSplit_contMDiff C)

/-- The actual old base derivative on the original product has exactly its old block.
Source: F0=(H,f,0_m), main.tex431. -/
theorem freeHopfInductionBase_deriv_old
    (H₀ : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hH : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ H₀)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar) (i : Fin m) (x : FreeHopfProduct C) :
    freeHopfDeriv C i.castSucc (freeHopfInductionBase C H₀ f) x =
      freeInductionBlock k m
        (freeHopfDeriv (freeHopfOldDimensions C) i H₀ (freeHopfProductSplit C x).1) 0 0 := by
  change freeHopfDeriv C i.castSucc
    (fun y ↦ freeInductionBase (m := m) H₀ f (freeHopfProductSplit C y)) x = _
  rw [freeHopfDeriv_split_old]
  exact freeInductionBase_old_orbitDeriv
    (freeHopfProductSmoothFlow (freeHopfOldDimensions C) i) H₀ hH f _ _

/-- The actual new base derivative on the original product has exactly its planar block.
Source: F0=(H,f,0_m), main.tex431. -/
theorem freeHopfInductionBase_deriv_last
    (H₀ : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ f)
    (x : FreeHopfProduct C) :
    freeHopfDeriv C (Fin.last m) (freeHopfInductionBase C H₀ f) x =
      freeInductionBlock k m 0
        (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2) 0 := by
  change freeHopfDeriv C (Fin.last m)
    (fun y ↦ freeInductionBase (m := m) H₀ f (freeHopfProductSplit C y)) x = _
  rw [freeHopfDeriv_split_last]
  exact freeInductionBase_active_orbitDeriv H₀ f hf _ _

/-- The actual old Z derivative retains its full outside-complement normal derivative
on the original product. Source: the moving frame at main.tex433–440. -/
theorem freeHopfInductionZ_deriv_old
    (ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ) (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n) (i : Fin m) (x : FreeHopfProduct C) :
    freeHopfDeriv C i.castSucc (freeHopfInductionZ C ν P Q η δ A n) x =
      let y := (freeHopfProductSplit C x).1
      let z := (freeHopfProductSplit C x).2
      freeComplementVariation (ν y) (freeHopfDeriv (freeHopfOldDimensions C) i ν y)
        (freeDisplacementVector P Q η δ (A y) (n y) z)
        (freeDisplacementOldVector P Q η δ
          (freeHopfDeriv (freeHopfOldDimensions C) i A y)
          (freeHopfDeriv (freeHopfOldDimensions C) i n y) z) := by
  change freeHopfDeriv C i.castSucc
    (fun y ↦ freeInductionZ ν P Q η δ A n (freeHopfProductSplit C y)) x = _
  rw [freeHopfDeriv_split_old]
  exact freeInductionZ_old_orbitDeriv
    (freeHopfProductSmoothFlow (freeHopfOldDimensions C) i) ν hν P Q η δ A n hA hn _ _

/-- The actual active Z derivative stays in the actual moving complement frame.
Source: XZ in main.tex444–453. -/
theorem freeHopfInductionZ_deriv_last
    (ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η) (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (x : FreeHopfProduct C) :
    freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n) x =
      let y := (freeHopfProductSplit C x).1
      let z := (freeHopfProductSplit C x).2
      freeComplementFrameCLM (ν y) (freeDisplacementActiveVector Q η δ (A y) (n y) z) := by
  change freeHopfDeriv C (Fin.last m)
    (fun y ↦ freeInductionZ ν P Q η δ A n (freeHopfProductSplit C y)) x = _
  rw [freeHopfDeriv_split_last]
  exact freeInductionZ_active_orbitDeriv ν P Q hP hQ hPQ η hη δ A n _ _

/-- Every physical mixed quadratic period is exactly zero on the original product.
All derivatives and the period integral are the original literal Hopf operations.
The proof pulls back the actual physical Z theorem, retaining all moving-normal
terms and the same matrix moments. Source: main.tex444–453. -/
theorem freeHopfInductionZ_mixed_period_zero
    (ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν) (hunit : ∀ x, ‖ν x‖ = 1)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (hSO : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin (m + 1)) ℝ)
    (hperiod : ∀ z, orbitAverage planarHopfFlow (fun w ↦ (P w).transpose * Q w) z = 0)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η)
    (hmean : ∀ z, orbitAverage planarHopfFlow η z = 0)
    (hquad : ∀ z, orbitAverage planarHopfFlow (fun w ↦
      η w ^ 2 • ((Q w).transpose * orbitDeriv planarHopfFlow Q w)) z = 0)
    (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (hnunit : ∀ x, ‖n x‖ = 1)
    (hnorth : ∀ x i, ⟪n x, freeHopfDeriv (freeHopfOldDimensions C) i A x⟫ = 0)
    (i : Fin m) (x : FreeHopfProduct C) :
    orbitAverage (freeHopfProductFlow C (Fin.last m))
      (fun y ↦ ⟪freeHopfDeriv C i.castSucc (freeHopfInductionZ C ν P Q η δ A n) y,
        freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n) y⟫) x = 0 := by
  let Z := freeInductionZ ν P Q η δ A n
  have he : (fun y ↦ ⟪freeHopfDeriv C i.castSucc (freeHopfInductionZ C ν P Q η δ A n) y,
        freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n) y⟫) =
      fun y ↦ ⟪orbitDeriv (fun t p ↦
          (freeHopfProductFlow (freeHopfOldDimensions C) i t p.1, p.2)) Z
            (freeHopfProductSplit C y),
        orbitDeriv (fun t p ↦ (p.1, planarHopfFlow t p.2)) Z (freeHopfProductSplit C y)⟫ := by
    funext y
    change ⟪freeHopfDeriv C i.castSucc (fun w ↦ Z (freeHopfProductSplit C w)) y,
      freeHopfDeriv C (Fin.last m) (fun w ↦ Z (freeHopfProductSplit C w)) y⟫ = _
    rw [freeHopfDeriv_split_old, freeHopfDeriv_split_last]
  rw [he]
  simp only [orbitAverage, freeHopfProductSplit_flow_last]
  exact freeInductionZ_mixed_period_zero
    (freeHopfProductSmoothFlow (freeHopfOldDimensions C) i) ν hν hunit
    P Q hP hQ hPQ hSO hperiod η hη hmean hquad δ A n hA hn hnunit
    (fun y ↦ (real_inner_comm _ _).trans (hnorth y i))
    (freeHopfProductSplit C x).1 (freeHopfProductSplit C x).2

/-- Normal orthogonality to the once-indexed sorted second columns implies normal
orthogonality to every actual ordered second derivative. The reversed case uses
W1's genuine Hopf-orbit Schwarz theorem, so no commutation hypothesis is added.
Source: the old free normal in main.tex431–442. -/
theorem freeHopf_normal_all_second {a N : ℕ} (dims : Fin a → ℕ)
    [∀ i, Fact (0 < dims i)]
    (H₀ ν : FreeHopfProduct dims → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff (freeHopfModel dims) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H₀)
    (hperp : ∀ x j, ⟪ν x, freeFlowColumns (freeHopfProductFlow dims) H₀ x j⟫ = 0)
    (x : FreeHopfProduct dims) (i j : Fin a) :
    ⟪ν x, freeHopfDeriv dims i (freeHopfDeriv dims j H₀) x⟫ = 0 := by
  by_cases hij : i ≤ j
  · exact hperp x (Sum.inr ⟨(i, j), hij⟩)
  · rw [freeHopfDeriv_commute_euclidean dims H₀ hH i j x]
    exact hperp x (Sum.inr ⟨(j, i), le_of_not_ge hij⟩)

/-- The same original-product F0 and Z have all actual first derivative pairings
zero. All old normal inputs are obtained from the unchanged selector induction
hypothesis, including ordered second normals via genuine commutation.
Source: the exact first cancellation in main.tex441–442. -/
theorem freeHopfInduction_first_pairing_zero
    (H₀ ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hIH : FreeSelectorProperties (freeHopfModel (freeHopfOldDimensions C))
      (freeHopfProductFlow (freeHopfOldDimensions C)) H₀ ν)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ f)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (x : FreeHopfProduct C) (i j : Fin (m + 1)) :
    ⟪freeHopfDeriv C i (freeHopfInductionBase C H₀ f) x,
      freeHopfDeriv C j (freeHopfInductionZ C ν P Q η δ A n) x⟫ = 0 := by
  have hperp := hIH.2.2.2.2.2
  have hpair := freeInduction_first_pairing_zero
    (fun i ↦ freeHopfProductSmoothFlow (freeHopfOldDimensions C) i)
    H₀ ν hIH.1 hIH.2.1
    (fun y i ↦ hperp y (Sum.inl i))
    (fun y i j ↦ freeHopf_normal_all_second (freeHopfOldDimensions C) H₀ ν hIH.1 hperp y i j)
    f hf P Q hP hQ hPQ η hη δ A n hA hn
  change ⟪freeHopfDeriv C i
      (fun y ↦ freeInductionBase (m := m) H₀ f (freeHopfProductSplit C y)) x,
    freeHopfDeriv C j
      (fun y ↦ freeInductionZ ν P Q η δ A n (freeHopfProductSplit C y)) x⟫ = 0
  rw [freeHopfDeriv_split, freeHopfDeriv_split]
  exact hpair (freeHopfProductSplit C x).1 (freeHopfProductSplit C x).2 i j

/-- The genuine native first metric variation is zero on the original whole Hopf
product, in precisely the canonical generator frame used by balanced correction.
No formal derivative or desired cancellation is assumed. Source: main.tex442. -/
theorem freeHopfInduction_first_variation_zero
    (H₀ ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hIH : FreeSelectorProperties (freeHopfModel (freeHopfOldDimensions C))
      (freeHopfProductFlow (freeHopfOldDimensions C)) H₀ ν)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ f)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (x : FreeHopfProduct C) :
    freeMetricCrossTerm (freeHopfInductionBase C H₀ f) (freeHopfInductionZ C ν P Q η δ A n)
      (freeHopfGeneratorSection C) x = 0 := by
  have hF := freeHopfInductionBase_contMDiff C H₀ hIH.1 f hf
  have hZ := freeHopfInductionZ_contMDiff C ν hIH.2.1 P Q hP hQ η hη δ A n hA hn
  have hz := freeHopfInduction_first_pairing_zero C H₀ ν hIH f hf
    P Q hP hQ hPQ η hη δ A n hA hn x
  ext i j
  change ⟪mvfderiv (freeHopfModel C) (freeHopfInductionBase C H₀ f) x
        (freeHopfGenerator C i x),
      mvfderiv (freeHopfModel C) (freeHopfInductionZ C ν P Q η δ A n) x
        (freeHopfGenerator C j x)⟫ +
    ⟪mvfderiv (freeHopfModel C) (freeHopfInductionZ C ν P Q η δ A n) x
        (freeHopfGenerator C i x),
      mvfderiv (freeHopfModel C) (freeHopfInductionBase C H₀ f) x
        (freeHopfGenerator C j x)⟫ = 0
  rw [freeHopfGenerator_mvfderiv C i _ hF x, freeHopfGenerator_mvfderiv C j _ hZ x,
    freeHopfGenerator_mvfderiv C i _ hZ x, freeHopfGenerator_mvfderiv C j _ hF x,
    hz i j, real_inner_comm, hz j i, add_zero]

end GlobalEmbedding.Paper
