import GlobalEmbedding.Paper.PlanarHopfFlow
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The literal complement coordinates of the free-induction displacement

Source: `main.tex`, `thm:free`, equations(4.4)–(4.5), lines431–459.
DAG: `free-displacement-coordinates`; exclusive owner W2.
All matrix actions use Mathlib's original Euclidean l2 linear operator.
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise

namespace GlobalEmbedding.Paper

variable {C d : ℕ}

local instance freeDisplacementMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The literal complement coordinate vector P a + delta eta Q n of (4.4). -/
def freeDisplacementVector
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (η : PlanarHopfSphere C → ℝ) (δ : ℝ)
    (a n : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C) :
    EuclideanSpace ℝ (Fin d) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (P z) a + δ • (η z • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (Q z) n)

/-- The literal active derivative Qa + delta((Xeta)Q + eta XQ)n. -/
def freeDisplacementActiveVector
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (η : PlanarHopfSphere C → ℝ) (δ : ℝ)
    (a n : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C) :
    EuclideanSpace ℝ (Fin d) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (Q z) a + δ •
    (orbitDeriv planarHopfFlow η z • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (Q z) n +
      η z • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (orbitDeriv planarHopfFlow Q z) n)

/-- The true old-coordinate variation is the same affine expression with da,dn. -/
def freeDisplacementOldVector
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (η : PlanarHopfSphere C → ℝ) (δ : ℝ)
    (da dn : EuclideanSpace ℝ (Fin d)) : PlanarHopfSphere C → EuclideanSpace ℝ (Fin d) :=
  freeDisplacementVector P Q η δ da dn

/-- The literal mixed column M_i of (4.5), retaining the actual XQ contribution. -/
def freeDisplacementMixedVector
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (η : PlanarHopfSphere C → ℝ) (δ : ℝ)
    (da dn : EuclideanSpace ℝ (Fin d)) : PlanarHopfSphere C → EuclideanSpace ℝ (Fin d) :=
  freeDisplacementActiveVector Q η δ da dn

private def matrixOperator (d : ℕ) : Matrix (Fin d) (Fin d) ℝ →L[ℝ]
    (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
  ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) :
    Matrix (Fin d) (Fin d) ℝ ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))).toContinuousLinearEquiv.toContinuousLinearMap

variable [Fact (0 < C)]

/-- Native smooth matrices act natively smoothly on every fixed actual Euclidean vector. -/
theorem free_matrix_action_contMDiff
    (P : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P)
    (a : EuclideanSpace ℝ (Fin d)) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞
      (fun z ↦ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (P z) a) :=
  ((matrixOperator d).contMDiff.comp hP).clm_apply contMDiff_const

/-- The genuine matrix-vector action commutes with the actual Hopf derivative. -/
theorem free_matrix_action_hasDerivAt
    (P : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P)
    (a : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C) :
    HasDerivAt (fun t ↦ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (P (planarHopfFlow t z)) a)
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (orbitDeriv planarHopfFlow P z) a) 0 := by
  let L : Matrix (Fin d) (Fin d) ℝ →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d)) a).comp (matrixOperator d)
  have h := L.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add P hP 0 z)
  change HasDerivAt (fun t ↦ L (P (planarHopfFlow t z)))
    (L (orbitDeriv planarHopfFlow P z)) 0
  simpa only [Function.comp_def, planarHopfFlow_zero] using h

/-- The actual source displacement coordinate field is natively smooth. -/
theorem freeDisplacementVector_contMDiff
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (a n : EuclideanSpace ℝ (Fin d)) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞
      (freeDisplacementVector P Q η δ a n) := by
  have hc : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞
      (fun z ↦ η z • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (Q z)) n) :=
    hη.smul (free_matrix_action_contMDiff Q hQ n)
  have hδ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun _ : PlanarHopfSphere C ↦ δ) := contMDiff_const
  exact (free_matrix_action_contMDiff P hP a).add (hδ.smul hc)

/-- Actual differentiation of literal V gives precisely its displayed active vector. -/
theorem freeDisplacementVector_orbitDeriv
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (a n : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (freeDisplacementVector P Q η δ a n) z =
      freeDisplacementActiveVector Q η δ a n z := by
  have hp := free_matrix_action_hasDerivAt P hP a z
  rw [hPQ z] at hp
  have hq := free_matrix_action_hasDerivAt Q hQ n z
  have he := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add η hη 0 z
  have h := hp.fun_add ((he.smul hq).const_smul δ)
  simpa only [orbitDeriv, freeDisplacementVector, freeDisplacementActiveVector,
    Pi.add_apply, Pi.smul_apply, Pi.smul_apply', planarHopfFlow_zero, add_comm] using h.deriv

omit [Fact (0 < C)] in
/-- The old variation is an actual derivative with respect to an actual old curve,
with the new-sphere point fixed. No derivative of the moving complement frame is
discarded here: this statement concerns only its displayed complement coordinates. -/
theorem freeDisplacementVector_old_hasDerivAt
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (η : PlanarHopfSphere C → ℝ) (δ : ℝ)
    (a n : ℝ → EuclideanSpace ℝ (Fin d))
    (da dn : EuclideanSpace ℝ (Fin d))
    (ha : HasDerivAt a da 0) (hn : HasDerivAt n dn 0) (z : PlanarHopfSphere C) :
    HasDerivAt (fun s ↦ freeDisplacementVector P Q η δ (a s) (n s) z)
      (freeDisplacementOldVector P Q η δ da dn z) 0 := by
  have hp := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (P z)).hasFDerivAt.comp_hasDerivAt 0 ha
  have hq := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (Q z)).hasFDerivAt.comp_hasDerivAt 0 hn
  have h := hp.fun_add ((hq.const_smul (η z)).const_smul δ)
  simpa only [freeDisplacementVector, freeDisplacementOldVector, Function.comp_def,
    Pi.add_apply, Pi.smul_apply] using h

/-- The literal active and mixed coordinate fields are natively smooth. -/
theorem freeDisplacementActiveVector_contMDiff
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (a n : EuclideanSpace ℝ (Fin d)) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞
      (freeDisplacementActiveVector Q η δ a n) := by
  have he := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) η hη
  have hq := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) Q hQ
  have hc : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞
      (fun z ↦ orbitDeriv planarHopfFlow η z •
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (Q z)) n +
          η z • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
            (orbitDeriv planarHopfFlow Q z)) n) :=
    (he.smul (free_matrix_action_contMDiff Q hQ n)).add
      (hη.smul (free_matrix_action_contMDiff _ hq n))
  exact (free_matrix_action_contMDiff Q hQ a).add
    ((contMDiff_const : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun _ : PlanarHopfSphere C ↦ δ)).smul hc)

/-- The source vector (4.4) is jointly native smooth in the actual old manifold
and new Hopf factor, for genuinely smooth old A,n and new P,Q,eta. -/
theorem freeDisplacementVector_joint_contMDiff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (a n : M → EuclideanSpace ℝ (Fin d))
    (ha : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ a)
    (hn : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ n) (δ : ℝ) :
    ContMDiff (I.prod (planarHopfModel C)) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞
      (fun p : M × PlanarHopfSphere C ↦ freeDisplacementVector P Q η δ (a p.1) (n p.1) p.2) := by
  have hp := ((matrixOperator d).contMDiff.comp hP).comp
    (contMDiff_snd : ContMDiff (I.prod (planarHopfModel C)) (planarHopfModel C) ∞
      (Prod.snd : M × PlanarHopfSphere C → PlanarHopfSphere C))
  have hq := ((matrixOperator d).contMDiff.comp hQ).comp
    (contMDiff_snd : ContMDiff (I.prod (planarHopfModel C)) (planarHopfModel C) ∞
      (Prod.snd : M × PlanarHopfSphere C → PlanarHopfSphere C))
  have hpv := hp.clm_apply (ha.comp contMDiff_fst)
  have hqv := hq.clm_apply (hn.comp contMDiff_fst)
  have he := hη.comp
    (contMDiff_snd : ContMDiff (I.prod (planarHopfModel C)) (planarHopfModel C) ∞
      (Prod.snd : M × PlanarHopfSphere C → PlanarHopfSphere C))
  exact hpv.add ((contMDiff_const : ContMDiff (I.prod (planarHopfModel C)) 𝓘(ℝ, ℝ) ∞
    (fun _ : M × PlanarHopfSphere C ↦ δ)).smul (he.smul hqv))

end GlobalEmbedding.Paper
