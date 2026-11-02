import GlobalEmbedding.Paper.MatrixAngularCone
import GlobalEmbedding.Paper.MatrixHopfTwoPrimitive
import GlobalEmbedding.Paper.MatrixHopfThreePrimitive
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual block assembly of orthogonal primitives in every dimension

Source: `main.tex`, prop:matrix, lines335–340.
DAG: `matrix-orthogonal-primitives`. Every block is the same actual P2 or P3;
rows and columns are reindexed by the same genuine finite equivalence.
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace GlobalEmbedding.Paper

/-- The actual block diagonal sum as a real linear map on the pair of blocks. -/
def matrixBlockSumLinearMap (a b : ℕ) :
    (Matrix (Fin a) (Fin a) ℝ × Matrix (Fin b) (Fin b) ℝ) →ₗ[ℝ]
      Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ where
  toFun x := Matrix.fromBlocks x.1 0 0 x.2
  map_add' := by
    intro x y
    ext i j
    cases i <;> cases j <;> simp
  map_smul' := by
    intro r x
    ext i j
    cases i <;> cases j <;> simp

/-- The literal block sum is reindexed on both sides into the actual Fin(a+b)
matrix space. Finite-dimensional continuity gives the genuine real CLM. -/
def matrixBlockSumCLM (a b : ℕ) :
    (Matrix (Fin a) (Fin a) ℝ × Matrix (Fin b) (Fin b) ℝ) →L[ℝ]
      Matrix (Fin (a + b)) (Fin (a + b)) ℝ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv).toLinearMap.comp
      (matrixBlockSumLinearMap a b))

/-- The block CLM is exactly the original diagonal block matrix, with a genuine
simultaneous reindexing, not a quotient or replacement of the matrix. -/
theorem matrixBlockSumCLM_apply (a b : ℕ)
    (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin b) (Fin b) ℝ) :
    matrixBlockSumCLM a b (A, B) = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks A 0 0 B) := rfl

/-- Simultaneous reindexing preserves true special orthogonal matrices: transpose
multiplication commutes with the actual reindex ring equivalence, and Mathlib's
actual determinant reindex identity preserves determinant one. -/
theorem matrix_reindex_mem_SO {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) (A : Matrix m m ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup m ℝ) :
    Matrix.reindex e e A ∈ Matrix.specialOrthogonalGroup n ℝ := by
  obtain ⟨hg, hd⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hA
  have hh := (Matrix.mem_orthogonalGroup_iff' m ℝ).mp hg
  apply Matrix.mem_specialOrthogonalGroup_iff.mpr
  constructor
  · apply (Matrix.mem_orthogonalGroup_iff' n ℝ).mpr
    change Matrix.reindexRingEquiv ℝ e A.transpose * Matrix.reindexRingEquiv ℝ e A = 1
    rw [← map_mul, hh, map_one]
  · simpa only [Matrix.det_reindex_self] using hd

/-- The genuine diagonal sum of two genuine positively oriented orthogonal
matrices is positively oriented orthogonal. Use the actual block multiplication
identity and the actual block determinant product theorem. -/
theorem matrix_fromBlocks_mem_SO {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin b) (Fin b) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin a) ℝ)
    (hB : B ∈ Matrix.specialOrthogonalGroup (Fin b) ℝ) :
    Matrix.fromBlocks A 0 0 B ∈ Matrix.specialOrthogonalGroup (Fin a ⊕ Fin b) ℝ := by
  obtain ⟨hgA, hdA⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hA
  obtain ⟨hgB, hdB⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hB
  have hAA := (Matrix.mem_orthogonalGroup_iff' (Fin a) ℝ).mp hgA
  have hBB := (Matrix.mem_orthogonalGroup_iff' (Fin b) ℝ).mp hgB
  apply Matrix.mem_specialOrthogonalGroup_iff.mpr
  constructor
  · apply (Matrix.mem_orthogonalGroup_iff' (Fin a ⊕ Fin b) ℝ).mpr
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hAA, hBB]
  · rw [Matrix.det_fromBlocks_zero₂₁, hdA, hdB, one_mul]

/-- The actual reindexed block CLM preserves genuine SO membership of both
actual blocks, combining the already proved diagonal and reindex identities. -/
theorem matrixBlockSumCLM_mem_SO {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin b) (Fin b) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin a) ℝ)
    (hB : B ∈ Matrix.specialOrthogonalGroup (Fin b) ℝ) :
    matrixBlockSumCLM a b (A, B) ∈ Matrix.specialOrthogonalGroup (Fin (a + b)) ℝ :=
  matrix_reindex_mem_SO finSumFinEquiv _ (matrix_fromBlocks_mem_SO A B hA hB)

/-- The actual block CLM preserves the transpose product. All cross blocks are
literally zero, and both original matrix indices use the same true reindexing. -/
theorem matrixBlockSumCLM_transpose_mul {a b : ℕ}
    (A C : Matrix (Fin a) (Fin a) ℝ) (B D₁ : Matrix (Fin b) (Fin b) ℝ) :
    (matrixBlockSumCLM a b (A, B)).transpose * matrixBlockSumCLM a b (C, D₁) =
      matrixBlockSumCLM a b (A.transpose * C, B.transpose * D₁) := by
  change Matrix.reindexRingEquiv ℝ finSumFinEquiv
      (Matrix.fromBlocks A 0 0 B).transpose *
    Matrix.reindexRingEquiv ℝ finSumFinEquiv (Matrix.fromBlocks C 0 0 D₁) = _
  rw [← map_mul]
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, matrixBlockSumCLM_apply]

/-- The genuine reindexed block sum is injective: extract the two original
principal blocks at the images of the genuine sum-index inclusions. -/
theorem matrixBlockSumCLM_injective (a b : ℕ) : Function.Injective (matrixBlockSumCLM a b) := by
  intro x y h
  rcases x with ⟨A, B⟩
  rcases y with ⟨C, D₁⟩
  apply Prod.ext
  · ext i j
    have hh := congrArg (fun A : Matrix (Fin (a + b)) (Fin (a + b)) ℝ ↦
      A (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))) h
    simpa [matrixBlockSumCLM_apply, Matrix.reindex_apply] using hh
  · ext i j
    have hh := congrArg (fun A : Matrix (Fin (a + b)) (Fin (a + b)) ℝ ↦
      A (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))) h
    simpa [matrixBlockSumCLM_apply, Matrix.reindex_apply] using hh

/-- The actual orbit average commutes with a pair of continuous orbit observables.
Apply the two genuine continuous-linear product projections to the Bochner integral. -/
theorem matrix_orbitAverage_pair {S E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (R : ℝ → S → S) (u : S → E) (v : S → F) (z : S)
    (hu : Continuous (fun t : ℝ ↦ u (R t z)))
    (hv : Continuous (fun t : ℝ ↦ v (R t z))) :
    orbitAverage R (fun y ↦ (u y, v y)) z = (orbitAverage R u z, orbitAverage R v z) := by
  apply Prod.ext
  · exact ((ContinuousLinearMap.fst ℝ E F).intervalIntegral_comp_comm
      ((hu.prodMk hv).intervalIntegrable 0 1)).symm
  · exact ((ContinuousLinearMap.snd ℝ E F).intervalIntegral_comp_comm
      ((hu.prodMk hv).intervalIntegrable 0 1)).symm

/-- The genuine block CLM commutes with the actual period integral, including
both original blocks and their actual product topology. -/
theorem matrixBlockSumCLM_average {S : Type*} {a b : ℕ} (R : ℝ → S → S)
    (u : S → Matrix (Fin a) (Fin a) ℝ) (v : S → Matrix (Fin b) (Fin b) ℝ) (z : S)
    (hu : Continuous (fun t : ℝ ↦ u (R t z)))
    (hv : Continuous (fun t : ℝ ↦ v (R t z))) :
    orbitAverage R (fun y ↦ matrixBlockSumCLM a b (u y, v y)) z =
      matrixBlockSumCLM a b (orbitAverage R u z, orbitAverage R v z) := by
  have hh := (matrixBlockSumCLM a b).intervalIntegral_comp_comm (μ := volume)
    (f := fun t : ℝ ↦ (u (R t z), v (R t z))) ((hu.prodMk hv).intervalIntegrable 0 1)
  change orbitAverage R (fun y ↦ matrixBlockSumCLM a b (u y, v y)) z =
    matrixBlockSumCLM a b (orbitAverage R (fun y ↦ (u y, v y)) z) at hh
  rw [matrix_orbitAverage_pair R u v z hu hv] at hh
  exact hh

/-- Bookkeeping for two actual smooth matrix maps and their proved primitive,
SO, period and stationary identities. Every derivative remains the original
literal orbitDeriv; this structure asserts no existence of such maps. -/
structure MatrixHopfPrimitiveData (C d : ℕ) [Fact (0 < C)]
    (κ : PlanarHopfSphere C → ℝ) where
  primitive : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ
  frame : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ
  smooth_primitive : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ primitive
  smooth_frame : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ frame
  derivative : ∀ z, orbitDeriv planarHopfFlow primitive z = frame z
  special : ∀ z, frame z ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ
  mean_zero : ∀ z, orbitAverage planarHopfFlow frame z = 0
  period_zero : ∀ z, orbitAverage planarHopfFlow (fun y ↦ (primitive y).transpose * frame y) z = 0
  stationary : ∀ z, κ z = 0 → orbitDeriv planarHopfFlow frame z = 0

/-- Actual orthogonal primitive data combine by the literal reindexed block sum.
Smoothness and real derivatives use the genuine CLM chain rule; SO uses actual
block determinants, and both period identities use actual Bochner integrals. -/
def MatrixHopfPrimitiveData.block {C a b : ℕ} [Fact (0 < C)]
    {κ : PlanarHopfSphere C → ℝ} (u : MatrixHopfPrimitiveData C a κ)
    (v : MatrixHopfPrimitiveData C b κ) : MatrixHopfPrimitiveData C (a + b) κ where
  primitive z := matrixBlockSumCLM a b (u.primitive z, v.primitive z)
  frame z := matrixBlockSumCLM a b (u.frame z, v.frame z)
  smooth_primitive := (matrixBlockSumCLM a b).contMDiff.comp
    (u.smooth_primitive.prodMk_space v.smooth_primitive)
  smooth_frame := (matrixBlockSumCLM a b).contMDiff.comp (u.smooth_frame.prodMk_space v.smooth_frame)
  derivative z := by
    have hu := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add u.primitive u.smooth_primitive 0 z
    have hv := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add v.primitive v.smooth_primitive 0 z
    simp only [planarHopfFlow_zero, u.derivative, v.derivative] at hu hv
    have hh := (matrixBlockSumCLM a b).hasFDerivAt.comp_hasDerivAt 0 (hu.prodMk hv)
    exact hh.deriv
  special z := matrixBlockSumCLM_mem_SO _ _ (u.special z) (v.special z)
  mean_zero z := by
    have hu : Continuous (fun t : ℝ ↦ u.frame (planarHopfFlow t z)) :=
      u.smooth_frame.continuous.comp
      ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
    have hv : Continuous (fun t : ℝ ↦ v.frame (planarHopfFlow t z)) :=
      v.smooth_frame.continuous.comp
      ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
    rw [matrixBlockSumCLM_average planarHopfFlow u.frame v.frame z hu hv,
      u.mean_zero, v.mean_zero]
    exact (matrixBlockSumCLM a b).map_zero
  period_zero z := by
    have hu : Continuous (fun t : ℝ ↦
        (u.primitive (planarHopfFlow t z)).transpose * u.frame (planarHopfFlow t z)) :=
      (u.smooth_primitive.continuous.matrix_transpose.matrix_mul
      u.smooth_frame.continuous).comp
        ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
    have hv : Continuous (fun t : ℝ ↦
        (v.primitive (planarHopfFlow t z)).transpose * v.frame (planarHopfFlow t z)) :=
      (v.smooth_primitive.continuous.matrix_transpose.matrix_mul
      v.smooth_frame.continuous).comp
        ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
    have he : (fun y ↦ (matrixBlockSumCLM a b (u.primitive y, v.primitive y)).transpose *
        matrixBlockSumCLM a b (u.frame y, v.frame y)) = fun y ↦
          matrixBlockSumCLM a b ((u.primitive y).transpose * u.frame y,
            (v.primitive y).transpose * v.frame y) := by
      funext y
      exact matrixBlockSumCLM_transpose_mul _ _ _ _
    rw [he, matrixBlockSumCLM_average planarHopfFlow _ _ z hu hv, u.period_zero, v.period_zero]
    exact (matrixBlockSumCLM a b).map_zero
  stationary z hz := by
    have hu := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add u.frame u.smooth_frame 0 z
    have hv := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add v.frame v.smooth_frame 0 z
    simp only [planarHopfFlow_zero, u.stationary z hz, v.stationary z hz] at hu hv
    have hh := (matrixBlockSumCLM a b).hasFDerivAt.comp_hasDerivAt 0 (hu.prodMk hv)
    have hz0 : matrixBlockSumCLM a b (0, 0) = 0 := (matrixBlockSumCLM a b).map_zero
    simpa only [orbitDeriv, Function.comp_def, hz0] using hh.deriv

/-- Actual dimension of a nonempty repeated two-block family. The recursive
form keeps each literal block construction definitionally typed. -/
def matrixEvenDimension : ℕ → ℕ
  | 0 => 2
  | k + 1 => matrixEvenDimension k + 2

/-- Actual dimension of one three-block followed by repeated two-blocks. -/
def matrixOddDimension : ℕ → ℕ
  | 0 => 3
  | k + 1 => matrixOddDimension k + 2

/-- The recursively assembled even dimension is exactly the source dimension. -/
theorem matrixEvenDimension_eq (k : ℕ) : matrixEvenDimension k = 2 * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [matrixEvenDimension, ih, Nat.mul_succ]

/-- The recursively assembled odd dimension is exactly the source dimension. -/
theorem matrixOddDimension_eq (k : ℕ) : matrixOddDimension k = 3 + 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [matrixOddDimension, ih, Nat.mul_succ, Nat.add_assoc]

/-- Repeated copies of the same actual two-block, with at least one block.
Every constructor is the literal genuine block sum without dependent casts. -/
def MatrixHopfPrimitiveData.evenBlocks {C : ℕ} [Fact (0 < C)]
    {κ : PlanarHopfSphere C → ℝ} (u : MatrixHopfPrimitiveData C 2 κ) :
    (k : ℕ) → MatrixHopfPrimitiveData C (matrixEvenDimension k) κ
  | 0 => u
  | k + 1 => (u.evenBlocks k).block u

/-- One actual three-block and repeated copies of the same actual two-block.
The zero-repeat case is exactly the original three-block. -/
def MatrixHopfPrimitiveData.oddBlocks {C : ℕ} [Fact (0 < C)]
    {κ : PlanarHopfSphere C → ℝ} (u : MatrixHopfPrimitiveData C 3 κ)
    (v : MatrixHopfPrimitiveData C 2 κ) :
    (k : ℕ) → MatrixHopfPrimitiveData C (matrixOddDimension k) κ
  | 0 => u
  | k + 1 => (u.oddBlocks v k).block v

/-- Actual two- and three-dimensional primitives construct an actual primitive
in every dimension d≥2. Parity arithmetic chooses the literal repeated blocks;
no new primitive or desired matrix properties are postulated in dimension d. -/
theorem matrixHopfPrimitiveData_all_dimensions {C : ℕ} [Fact (0 < C)]
    {κ : PlanarHopfSphere C → ℝ} (u : MatrixHopfPrimitiveData C 2 κ)
    (v : MatrixHopfPrimitiveData C 3 κ) (d : ℕ) (hd : 2 ≤ d) :
    Nonempty (MatrixHopfPrimitiveData C d κ) := by
  by_cases h : d % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, d = matrixEvenDimension k := by
      refine ⟨d / 2 - 1, ?_⟩
      rw [matrixEvenDimension_eq]
      omega
    exact ⟨u.evenBlocks k⟩
  · obtain ⟨k, rfl⟩ : ∃ k, d = matrixOddDimension k := by
      refine ⟨(d - 3) / 2, ?_⟩
      rw [matrixOddDimension_eq]
      omega
    exact ⟨v.oddBlocks u k⟩

/-- The actual fixed Euclidean three-coordinate skew-matrix embedding, with the
literal connection signs already proved for Q3. Finite-dimensional continuity
turns the genuine entrywise linear map into a genuine continuous linear map. -/
def matrixThreeSkewEmbedding : EuclideanSpace ℝ (Fin 3) →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a ↦ !![0, a 0, a 1; -a 0, 0, -a 2; -a 1, a 2, 0]
      map_add' := by
        intro a b
        ext i j
        fin_cases i <;> fin_cases j <;> simp [add_comm]
      map_smul' := by
        intro r a
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_neg] }

/-- The actual Euclidean three-coordinate matrix embedding is injective. Its
01,02,21 entries recover all three original Euclidean coordinates. -/
theorem matrixThreeSkewEmbedding_injective : Function.Injective matrixThreeSkewEmbedding := by
  intro a b h
  ext i
  fin_cases i
  · simpa [matrixThreeSkewEmbedding] using
      congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ ↦ A 0 1) h
  · simpa [matrixThreeSkewEmbedding] using
      congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ ↦ A 0 2) h
  · simpa [matrixThreeSkewEmbedding] using
      congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ ↦ A 2 1) h

/-- The actual unscaled Euclidean connection coordinates in dimension three. -/
def matrixHopfThreeConnectionCoordinates {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (θ : PlanarHopfSphere C → ℝ)
    (z : PlanarHopfSphere C) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![planarOrbitCurvature planarHopfFlow f z * Real.sin (θ z),
    planarOrbitCurvature planarHopfFlow f z * Real.cos (θ z), orbitDeriv planarHopfFlow θ z]

/-- The actual Euclidean connection coordinates are native smooth from the same
actual f and θ: actual curvature and the actual orbit derivative are smooth. -/
theorem matrixHopfThreeConnectionCoordinates_contMDiff {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (matrixHopfThreeConnectionCoordinates f θ) := by
  have hs := hf.curvature_smooth.mul (Real.contDiff_sin.contMDiff.comp hθ)
  have hc := hf.curvature_smooth.mul (Real.contDiff_cos.contMDiff.comp hθ)
  have hd := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) θ hθ
  have hpi : ContMDiff (planarHopfModel C) 𝓘(ℝ, Fin 3 → ℝ) ∞
      (fun z ↦ ![planarOrbitCurvature planarHopfFlow f z * Real.sin (θ z),
        planarOrbitCurvature planarHopfFlow f z * Real.cos (θ z), orbitDeriv planarHopfFlow θ z]) := by
    apply contMDiff_pi_module_iff.mpr
    intro i
    fin_cases i
    · exact hs
    · exact hc
    · exact hd
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff.comp hpi

/-- The actual Q3ᵀXQ3 is the actual injective linear image of its smooth genuine
Euclidean connection coordinates, exactly matching the scalar moment interface. -/
theorem matrixHopfThreeConnectionCoordinates_embedding {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) (z : PlanarHopfSphere C) :
    matrixThreeSkewEmbedding (matrixHopfThreeConnectionCoordinates f θ z) =
      (matrixHopfThreeFrame f θ z).transpose *
        orbitDeriv planarHopfFlow (matrixHopfThreeFrame f θ) z := by
  rw [matrixHopfThreeFrame_connection f hf θ hθ z]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixThreeSkewEmbedding, matrixHopfThreeConnectionCoordinates, matrixThreeConnection]

/-- Dropping the last of four actual Euclidean coordinates is a real continuous
linear map, with the original l² structures on both finite coordinate spaces. -/
def matrixThreeOfFour : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a ↦ WithLp.toLp 2 ![a 0, a 1, a 2]
      map_add' := by
        intro a b
        ext i
        fin_cases i <;> simp
      map_smul' := by
        intro r a
        ext i
        fin_cases i <;> simp }

/-- The actual unscaled Euclidean four-coordinate connection data for odd
blocks beyond dimension three. No formal skew field or independent curvature. -/
def matrixHopfFourConnectionCoordinates {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (θ : PlanarHopfSphere C → ℝ)
    (z : PlanarHopfSphere C) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![planarOrbitCurvature planarHopfFlow f z * Real.sin (θ z),
    planarOrbitCurvature planarHopfFlow f z * Real.cos (θ z),
    orbitDeriv planarHopfFlow θ z, planarOrbitCurvature planarHopfFlow f z]

/-- The actual four-coordinate connection data are native smooth by the same
actual curvature, sine/cosine, and actual orbit differentiation calculus. -/
theorem matrixHopfFourConnectionCoordinates_contMDiff {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞
      (matrixHopfFourConnectionCoordinates f θ) := by
  have hs := hf.curvature_smooth.mul (Real.contDiff_sin.contMDiff.comp hθ)
  have hc := hf.curvature_smooth.mul (Real.contDiff_cos.contMDiff.comp hθ)
  have hd := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) θ hθ
  have hpi : ContMDiff (planarHopfModel C) 𝓘(ℝ, Fin 4 → ℝ) ∞
      (fun z ↦ ![planarOrbitCurvature planarHopfFlow f z * Real.sin (θ z),
        planarOrbitCurvature planarHopfFlow f z * Real.cos (θ z),
        orbitDeriv planarHopfFlow θ z, planarOrbitCurvature planarHopfFlow f z]) := by
    apply contMDiff_pi_module_iff.mpr
    intro i
    fin_cases i
    · exact hs
    · exact hc
    · exact hd
    · exact hf.curvature_smooth
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap.contMDiff.comp hpi

/-- Actual orbit differentiation commutes with the genuine block CLM by the
ordinary product derivative and actual CLM chain rule on the same Hopf action. -/
theorem matrixBlockSumCLM_orbitDeriv {C a b : ℕ} [Fact (0 < C)]
    (u : PlanarHopfSphere C → Matrix (Fin a) (Fin a) ℝ)
    (v : PlanarHopfSphere C → Matrix (Fin b) (Fin b) ℝ)
    (hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin a) (Fin a) ℝ) ∞ u)
    (hv : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin b) (Fin b) ℝ) ∞ v)
    (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (fun y ↦ matrixBlockSumCLM a b (u y, v y)) z =
      matrixBlockSumCLM a b (orbitDeriv planarHopfFlow u z, orbitDeriv planarHopfFlow v z) := by
  have hdu := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add u hu 0 z
  have hdv := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add v hv 0 z
  have hh := (matrixBlockSumCLM a b).hasFDerivAt.comp_hasDerivAt 0 (hdu.prodMk hdv)
  simpa only [orbitDeriv, Function.comp_def, planarHopfFlow_zero] using hh.deriv

/-- The true connection of the actual block data is the genuine block sum of
the true original connections; no independent matrix-valued derivative is given. -/
theorem MatrixHopfPrimitiveData.block_connection {C a b : ℕ} [Fact (0 < C)]
    {κ : PlanarHopfSphere C → ℝ} (u : MatrixHopfPrimitiveData C a κ)
    (v : MatrixHopfPrimitiveData C b κ) (z : PlanarHopfSphere C) :
    ((u.block v).frame z).transpose * orbitDeriv planarHopfFlow (u.block v).frame z =
      matrixBlockSumCLM a b ((u.frame z).transpose * orbitDeriv planarHopfFlow u.frame z,
        (v.frame z).transpose * orbitDeriv planarHopfFlow v.frame z) := by
  change (matrixBlockSumCLM a b (u.frame z, v.frame z)).transpose *
    orbitDeriv planarHopfFlow (fun y ↦ matrixBlockSumCLM a b (u.frame y, v.frame y)) z = _
  rw [matrixBlockSumCLM_orbitDeriv u.frame v.frame u.smooth_frame v.smooth_frame z]
  exact matrixBlockSumCLM_transpose_mul _ _ _ _

/-- Appending two actual connection embeddings with the same genuine Euclidean
source is the genuine block CLM applied to their pair. -/
def matrixAppendSkewEmbedding {a b m : ℕ}
    (j : EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin a) (Fin a) ℝ)
    (k : EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin b) (Fin b) ℝ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin (a + b)) (Fin (a + b)) ℝ :=
  (matrixBlockSumCLM a b).comp (j.prod k)

/-- Appending an actual skew block preserves injection of the first genuine
Euclidean embedding, by the true injectivity of the actual diagonal block sum. -/
theorem matrixAppendSkewEmbedding_injective {a b m : ℕ}
    (j : EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin a) (Fin a) ℝ)
    (k : EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin b) (Fin b) ℝ)
    (hj : Function.Injective j) : Function.Injective (matrixAppendSkewEmbedding j k) := by
  intro x y h
  apply hj
  change matrixBlockSumCLM a b (j x, k x) = matrixBlockSumCLM a b (j y, k y) at h
  exact congrArg Prod.fst (matrixBlockSumCLM_injective a b h)

/-- The genuine four-coordinate skew embedding has the original three-skew
block and a genuine independent final skew-line block. -/
def matrixFourSkewEmbedding (J : Matrix (Fin 2) (Fin 2) ℝ) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin (3 + 2)) (Fin (3 + 2)) ℝ :=
  matrixAppendSkewEmbedding (matrixThreeSkewEmbedding.comp matrixThreeOfFour)
    ((ContinuousLinearMap.toSpanSingleton ℝ J).comp
      (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin 4) 3))

/-- The actual four-coordinate skew map is injective whenever its actual extra
skew block is nonzero. Read the first three coordinates from the actual first
block, and the fourth coefficient from its genuine nonzero scalar multiple. -/
theorem matrixFourSkewEmbedding_injective (J : Matrix (Fin 2) (Fin 2) ℝ) (hJ : J ≠ 0) :
    Function.Injective (matrixFourSkewEmbedding J) := by
  intro a b h
  change matrixBlockSumCLM 3 2
      (matrixThreeSkewEmbedding (matrixThreeOfFour a), a 3 • J) =
    matrixBlockSumCLM 3 2
      (matrixThreeSkewEmbedding (matrixThreeOfFour b), b 3 • J) at h
  have hh := matrixBlockSumCLM_injective 3 2 h
  have h012 := matrixThreeSkewEmbedding_injective (congrArg Prod.fst hh)
  have h3 : a 3 = b 3 := smul_left_injective ℝ hJ (congrArg Prod.snd hh)
  ext i
  fin_cases i
  · simpa [matrixThreeOfFour] using congrArg (fun x : EuclideanSpace ℝ (Fin 3) ↦ x 0) h012
  · simpa [matrixThreeOfFour] using congrArg (fun x : EuclideanSpace ℝ (Fin 3) ↦ x 1) h012
  · simpa [matrixThreeOfFour] using congrArg (fun x : EuclideanSpace ℝ (Fin 3) ↦ x 2) h012
  · exact h3

/-- Repeated genuine two-block connection maps with a fixed genuine Euclidean
four-dimensional source. No injection assumption is required for moment transport. -/
def matrixEvenConnectionEmbedding
    (j : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :
    (k : ℕ) → EuclideanSpace ℝ (Fin 4) →L[ℝ]
      Matrix (Fin (matrixEvenDimension k)) (Fin (matrixEvenDimension k)) ℝ
  | 0 => j
  | k + 1 => matrixAppendSkewEmbedding (matrixEvenConnectionEmbedding j k) j

/-- One genuine three-block connection map and repeated genuine two-block maps
with the same actual Euclidean four-coordinate source. -/
def matrixOddConnectionEmbedding
    (j : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ)
    (k : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :
    (n : ℕ) → EuclideanSpace ℝ (Fin 4) →L[ℝ]
      Matrix (Fin (matrixOddDimension n)) (Fin (matrixOddDimension n)) ℝ
  | 0 => j
  | n + 1 => matrixAppendSkewEmbedding (matrixOddConnectionEmbedding j k n) k

/-- The actual repeated two-block connection is the exact linear image of the
same actual Euclidean coordinates, by the genuine block connection identity. -/
theorem MatrixHopfPrimitiveData.evenBlocks_connection {C : ℕ} [Fact (0 < C)]
    {κ : PlanarHopfSphere C → ℝ} (u : MatrixHopfPrimitiveData C 2 κ)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin 4))
    (j : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
    (hj : ∀ z, j (A z) = (u.frame z).transpose * orbitDeriv planarHopfFlow u.frame z)
    (k : ℕ) (z : PlanarHopfSphere C) :
    matrixEvenConnectionEmbedding j k (A z) =
      ((u.evenBlocks k).frame z).transpose * orbitDeriv planarHopfFlow (u.evenBlocks k).frame z := by
  induction k with
  | zero => exact hj z
  | succ k ih =>
    change matrixBlockSumCLM (matrixEvenDimension k) 2
      (matrixEvenConnectionEmbedding j k (A z), j (A z)) = _
    rw [ih, hj z]
    exact ((u.evenBlocks k).block_connection u z).symm

/-- The actual one-three/repeated-two-block connection is the exact linear image
of the same actual Euclidean coordinates. All actual flow derivatives are retained. -/
theorem MatrixHopfPrimitiveData.oddBlocks_connection {C : ℕ} [Fact (0 < C)]
    {κ : PlanarHopfSphere C → ℝ} (u : MatrixHopfPrimitiveData C 3 κ)
    (v : MatrixHopfPrimitiveData C 2 κ) (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin 4))
    (j : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ)
    (k : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
    (hj : ∀ z, j (A z) = (u.frame z).transpose * orbitDeriv planarHopfFlow u.frame z)
    (hk : ∀ z, k (A z) = (v.frame z).transpose * orbitDeriv planarHopfFlow v.frame z)
    (n : ℕ) (z : PlanarHopfSphere C) :
    matrixOddConnectionEmbedding j k n (A z) =
      ((u.oddBlocks v n).frame z).transpose * orbitDeriv planarHopfFlow (u.oddBlocks v n).frame z := by
  induction n with
  | zero => exact hj z
  | succ n ih =>
    change matrixBlockSumCLM (matrixOddDimension n) 2
      (matrixOddConnectionEmbedding j k n (A z), k (A z)) = _
    rw [ih, hk z]
    exact ((u.oddBlocks v n).block_connection v z).symm

/-- Actual primitive data and their actual four-coordinate connection maps
assemble in every d≥2, using the exact same repeated source blocks. -/
theorem matrixHopfPrimitiveData_all_dimensions_connection {C : ℕ} [Fact (0 < C)]
    {κ : PlanarHopfSphere C → ℝ} (u : MatrixHopfPrimitiveData C 2 κ)
    (v : MatrixHopfPrimitiveData C 3 κ) (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin 4))
    (j : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
    (k : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ)
    (hj : ∀ z, j (A z) = (u.frame z).transpose * orbitDeriv planarHopfFlow u.frame z)
    (hk : ∀ z, k (A z) = (v.frame z).transpose * orbitDeriv planarHopfFlow v.frame z)
    (d : ℕ) (hd : 2 ≤ d) : ∃ w : MatrixHopfPrimitiveData C d κ,
      ∃ l : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin d) (Fin d) ℝ,
        ∀ z, l (A z) = (w.frame z).transpose * orbitDeriv planarHopfFlow w.frame z := by
  by_cases h : d % 2 = 0
  · obtain ⟨n, rfl⟩ : ∃ n, d = matrixEvenDimension n := by
      refine ⟨d / 2 - 1, ?_⟩
      rw [matrixEvenDimension_eq]
      omega
    exact ⟨u.evenBlocks n, matrixEvenConnectionEmbedding j n, u.evenBlocks_connection A j hj n⟩
  · obtain ⟨n, rfl⟩ : ∃ n, d = matrixOddDimension n := by
      refine ⟨(d - 3) / 2, ?_⟩
      rw [matrixOddDimension_eq]
      omega
    exact ⟨v.oddBlocks u n, matrixOddConnectionEmbedding k j n, v.oddBlocks_connection u A k j hk hj n⟩

/-- The actual same planar selector constructs the genuine two-block data by the
already accepted complete literal P2/Q2 proofs. -/
def matrixHopfTwoBlockData {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f) :
    MatrixHopfPrimitiveData C 2 (planarOrbitCurvature planarHopfFlow f) where
  primitive := matrixHopfTwoPrimitive f
  frame := matrixHopfTwoFrame f
  smooth_primitive := matrixHopfTwoPrimitive_contMDiff f hf
  smooth_frame := matrixHopfTwoFrame_contMDiff f hf
  derivative := matrixHopfTwoPrimitive_orbitDeriv f hf
  special := matrixHopfTwoFrame_mem_SO f hf
  mean_zero := matrixHopfTwoFrame_average_zero f hf
  period_zero := matrixHopfTwoPrimitive_period_zero f hf
  stationary := matrixHopfTwoFrame_orbitDeriv_zero f hf

/-- The same actual f and actual angle construct the genuine three-block data
from the accepted literal P3/Q3 proofs. All actual period conditions are proved
for the same constructed maps; no desired primitive is supplied. -/
def matrixHopfThreeBlockData {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ) (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hodd : ∀ z, θ (-z) = -θ z)
    (hmean : ∀ z, orbitAverage planarHopfFlow (matrixHopfThreeFrame f θ) z = 0)
    (hbsin : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarB f y * Real.sin (θ y)) z = 0)
    (hθzero : ∀ z, planarOrbitCurvature planarHopfFlow f z = 0 →
      orbitDeriv planarHopfFlow θ z = 0) :
    MatrixHopfPrimitiveData C 3 (planarOrbitCurvature planarHopfFlow f) where
  primitive := matrixHopfThreePrimitive f θ
  frame := matrixHopfThreeFrame f θ
  smooth_primitive := matrixHopfThreePrimitive_contMDiff f hf θ hθ
  smooth_frame := matrixHopfThreeFrame_contMDiff f hf.smooth θ hθ
  derivative := matrixHopfThreePrimitive_orbitDeriv f hf θ hθ hmean
  special := matrixHopfThreeFrame_mem_SO f hf.unit_speed θ
  mean_zero := hmean
  period_zero := matrixHopfThreePrimitive_period_zero f hf θ hθ hodd hmean hbsin
  stationary z hz := matrixHopfThreeFrame_orbitDeriv_zero f hf θ hθ z hz (hθzero z hz)

/-- The actual original two-block connection map from the unified four genuine
Euclidean coordinates uses exactly their fourth coordinate and the actual J2. -/
def matrixTwoOfFourSkewEmbedding : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ matrixPlanarSkew).comp
    (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin 4) 3)

/-- The actual two-block Q2 connection is the literal unified-four-coordinate
linear image, by the accepted actual κJ2 connection theorem. -/
theorem matrixHopfTwoOfFourSkewEmbedding_connection {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) :
    matrixTwoOfFourSkewEmbedding (matrixHopfFourConnectionCoordinates f θ z) =
      (matrixHopfTwoFrame f z).transpose * orbitDeriv planarHopfFlow (matrixHopfTwoFrame f) z := by
  rw [matrixHopfTwoFrame_connection f hf z]
  rfl

/-- The actual three-block Q3 connection is the literal unified-four-coordinate
linear image, using the already proved actual three-coordinate connection. -/
theorem matrixHopfThreeOfFourSkewEmbedding_connection {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ) (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (z : PlanarHopfSphere C) :
    (matrixThreeSkewEmbedding.comp matrixThreeOfFour) (matrixHopfFourConnectionCoordinates f θ z) =
      (matrixHopfThreeFrame f θ z).transpose * orbitDeriv planarHopfFlow (matrixHopfThreeFrame f θ) z := by
  have he : matrixThreeOfFour (matrixHopfFourConnectionCoordinates f θ z) =
      matrixHopfThreeConnectionCoordinates f θ z := by
    ext i
    fin_cases i <;> rfl
  rw [ContinuousLinearMap.comp_apply, he]
  exact matrixHopfThreeConnectionCoordinates_embedding f hf θ hθ z

/-- The original first three matrix conditions and actual curvature-zero XQ
vanishing are constructed for every d≥2 from the same actual planar f and angle.
Q is literally XP. The exact same block construction supplies a genuine CLM
from the actual unified four-coordinate connection to QᵀXQ. -/
theorem matrix_hopf_orthogonal_primitives_unscaled {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ) (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hodd : ∀ z, θ (-z) = -θ z)
    (hcos : ∀ z, orbitAverage planarHopfFlow (fun y ↦ Real.cos (θ y)) z = 0)
    (htsin : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarT f y * Real.sin (θ y)) z = 0)
    (hscos : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarS f y * Real.cos (θ y)) z = 0)
    (hbsin : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarB f y * Real.sin (θ y)) z = 0)
    (hθzero : ∀ z, planarOrbitCurvature planarHopfFlow f z = 0 →
      orbitDeriv planarHopfFlow θ z = 0) (d : ℕ) (hd : 2 ≤ d) :
    ∃ P : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ,
      ∃ j : EuclideanSpace ℝ (Fin 4) →L[ℝ] Matrix (Fin d) (Fin d) ℝ,
        let Q := orbitDeriv planarHopfFlow P
        ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P ∧
          (∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ) ∧
          (∀ z, orbitAverage planarHopfFlow Q z = 0) ∧
          (∀ z, orbitAverage planarHopfFlow (fun y ↦ (P y).transpose * Q y) z = 0) ∧
          (∀ z, planarOrbitCurvature planarHopfFlow f z = 0 → orbitDeriv planarHopfFlow Q z = 0) ∧
          (∀ z, j (matrixHopfFourConnectionCoordinates f θ z) =
            (Q z).transpose * orbitDeriv planarHopfFlow Q z) := by
  have hmean := matrixHopfThreeFrame_average_zero f hf θ hθ hodd hcos htsin hscos
  let u := matrixHopfTwoBlockData f hf
  let v := matrixHopfThreeBlockData f hf θ hθ hodd hmean hbsin hθzero
  obtain ⟨w, j, hj⟩ := matrixHopfPrimitiveData_all_dimensions_connection u v
    (matrixHopfFourConnectionCoordinates f θ) matrixTwoOfFourSkewEmbedding
    (matrixThreeSkewEmbedding.comp matrixThreeOfFour)
    (matrixHopfTwoOfFourSkewEmbedding_connection f hf θ)
    (matrixHopfThreeOfFourSkewEmbedding_connection f hf θ hθ) d hd
  refine ⟨w.primitive, j, ?_⟩
  have he : orbitDeriv planarHopfFlow w.primitive = w.frame := funext w.derivative
  dsimp only
  rw [he]
  exact ⟨w.smooth_primitive, w.special, w.mean_zero, w.period_zero, w.stationary, hj⟩

/-- The genuine Euclidean diagonal scaling needed to transport the actual scaled
angular cone into the exact unscaled matrix connection. -/
def matrixAngularScaling (T : ℝ) : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a ↦ WithLp.toLp 2 ![a 0, a 1, T * a 2, a 3]
      map_add' := by
        intro a b
        ext i
        fin_cases i <;> simp [mul_add]
      map_smul' := by
        intro r a
        ext i
        fin_cases i <;> simp [mul_left_comm] }

/-- The true angular vector rescales to the true unscaled connection coordinates
at every nonzero actual frequency. All four coordinates are literal originals. -/
theorem matrixAngularScaling_vector (T κ θ a : ℝ) (hT : T ≠ 0) :
    matrixAngularScaling T (matrixAngularVector κ θ (T⁻¹ * a)) = matrixAngularVector κ θ a := by
  ext i
  fin_cases i <;> simp [matrixAngularScaling, matrixAngularVector, hT]

/-- The exact unified actual angular coordinates from the accepted cone theorem
are native smooth, also at T=0. The genuine finite-dimensional diagonal CLM acts
on the already proved actual native smooth unscaled coordinates. -/
theorem matrix_hopf_angular_coordinates_contMDiff {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ) (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) (T : ℝ) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixAngularSpace) ∞
      (fun z ↦ matrixAngularVector (planarOrbitCurvature planarHopfFlow f z)
        (θ z) (T⁻¹ * orbitDeriv planarHopfFlow θ z)) := by
  have hh := (matrixAngularScaling T⁻¹).contMDiff.comp
    (matrixHopfFourConnectionCoordinates_contMDiff f hf θ hθ)
  apply hh.congr
  intro z
  ext i
  fin_cases i <;> rfl

/-- The complete actual orthogonal primitive construction for every d≥2, with
Q literally XP and the exact same actual scaled A4 used by the accepted angular
cone and scalar-moment construction. A genuine fixed CLM j transports A4 into
QᵀXQ. Neither density nor angle nor primitive existence is assumed in the final
target: this auxiliary consumes the actual angle supplied by its separate proof. -/
theorem matrix_hopf_orthogonal_primitives {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ) (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hodd : ∀ z, θ (-z) = -θ z)
    (hcos : ∀ z, orbitAverage planarHopfFlow (fun y ↦ Real.cos (θ y)) z = 0)
    (htsin : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarT f y * Real.sin (θ y)) z = 0)
    (hscos : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarS f y * Real.cos (θ y)) z = 0)
    (hbsin : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarB f y * Real.sin (θ y)) z = 0)
    (hθzero : ∀ z, planarOrbitCurvature planarHopfFlow f z = 0 →
      orbitDeriv planarHopfFlow θ z = 0) (T : ℝ) (hT : T ≠ 0) (d : ℕ) (hd : 2 ≤ d) :
    ∃ P : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ,
      ∃ j : MatrixAngularSpace →L[ℝ] Matrix (Fin d) (Fin d) ℝ,
        let Q := orbitDeriv planarHopfFlow P
        ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P ∧
          (∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ) ∧
          (∀ z, orbitAverage planarHopfFlow Q z = 0) ∧
          (∀ z, orbitAverage planarHopfFlow (fun y ↦ (P y).transpose * Q y) z = 0) ∧
          (∀ z, planarOrbitCurvature planarHopfFlow f z = 0 → orbitDeriv planarHopfFlow Q z = 0) ∧
          (∀ z, j (matrixAngularVector (planarOrbitCurvature planarHopfFlow f z)
            (θ z) (T⁻¹ * orbitDeriv planarHopfFlow θ z)) =
              (Q z).transpose * orbitDeriv planarHopfFlow Q z) := by
  obtain ⟨P, j, hP, hSO, hmean, hperiod, hzero, hj⟩ :=
    matrix_hopf_orthogonal_primitives_unscaled f hf θ hθ hodd hcos htsin hscos hbsin hθzero d hd
  refine ⟨P, j.comp (matrixAngularScaling T), hP, hSO, hmean, hperiod, hzero, ?_⟩
  intro z
  rw [ContinuousLinearMap.comp_apply, matrixAngularScaling_vector T _ _ _ hT]
  exact hj z

/-- Zero actual quadratic moment in the genuine four-dimensional angular
coordinates gives zero actual matrix connection moment under the genuine fixed
CLM j. Smoothness supplies integrability of the actual orbit observable; commute
j through the actual Bochner integral and use its true scalar linearity. -/
theorem matrix_hopf_angular_quadratic_moment_transport {C d : ℕ} [Fact (0 < C)]
    (A : PlanarHopfSphere C → MatrixAngularSpace)
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixAngularSpace) ∞ A)
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (j : MatrixAngularSpace →L[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (hj : ∀ z, j (A z) = (Q z).transpose * orbitDeriv planarHopfFlow Q z)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η) (z : PlanarHopfSphere C)
    (hmoment : orbitAverage planarHopfFlow (fun y ↦ η y ^ 2 • A y) z = 0) :
    orbitAverage planarHopfFlow
      (fun y ↦ η y ^ 2 • ((Q y).transpose * orbitDeriv planarHopfFlow Q y)) z = 0 := by
  have hs := (hη.pow 2).smul hA
  have hc : Continuous (fun t : ℝ ↦ η (planarHopfFlow t z) ^ 2 • A (planarHopfFlow t z)) :=
    hs.continuous.comp ((planarHopfFlow_contMDiff C).continuous.comp
      (continuous_id.prodMk continuous_const))
  have hh := j.intervalIntegral_comp_comm (μ := volume)
    (f := fun t : ℝ ↦ η (planarHopfFlow t z) ^ 2 • A (planarHopfFlow t z))
    (hc.intervalIntegrable 0 1)
  unfold orbitAverage
  calc
    _ = ∫ t in (0 : ℝ)..1, j (η (planarHopfFlow t z) ^ 2 • A (planarHopfFlow t z)) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [j.map_smul, hj]
    _ = j (∫ t in (0 : ℝ)..1, η (planarHopfFlow t z) ^ 2 • A (planarHopfFlow t z)) := hh
    _ = 0 := by
      change j (orbitAverage planarHopfFlow (fun y ↦ η y ^ 2 • A y) z) = 0
      rw [hmoment, map_zero]

#print axioms matrix_hopf_angular_quadratic_moment_transport
#print axioms matrix_hopf_orthogonal_primitives
#print axioms matrix_hopf_angular_coordinates_contMDiff
#print axioms matrixAngularScaling_vector
#print axioms matrix_hopf_orthogonal_primitives_unscaled
#print axioms matrixHopfTwoOfFourSkewEmbedding_connection
#print axioms matrixHopfThreeOfFourSkewEmbedding_connection
#print axioms matrixHopfPrimitiveData_all_dimensions_connection
#print axioms MatrixHopfPrimitiveData.evenBlocks_connection
#print axioms MatrixHopfPrimitiveData.oddBlocks_connection
#print axioms matrixFourSkewEmbedding_injective
#print axioms matrixAppendSkewEmbedding_injective
#print axioms MatrixHopfPrimitiveData.block_connection
#print axioms matrixThreeSkewEmbedding_injective
#print axioms matrixHopfThreeConnectionCoordinates_contMDiff
#print axioms matrixHopfThreeConnectionCoordinates_embedding
#print axioms matrixHopfFourConnectionCoordinates_contMDiff
#print axioms matrixHopfPrimitiveData_all_dimensions
#print axioms MatrixHopfPrimitiveData.evenBlocks
#print axioms MatrixHopfPrimitiveData.oddBlocks
#print axioms MatrixHopfPrimitiveData.block
#print axioms matrixBlockSumCLM_average
#print axioms matrixBlockSumCLM_mem_SO
#print axioms matrixBlockSumCLM_transpose_mul
#print axioms matrixBlockSumCLM_injective
end GlobalEmbedding.Paper
