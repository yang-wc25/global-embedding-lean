import GlobalEmbedding.Paper.PlanarPeriodOneCalculus
import GlobalEmbedding.Paper.FreeDisplacementCoordinates
import GlobalEmbedding.Paper.FreeInductionEuclideanBlocks
import GlobalEmbedding.Paper.FreeMixedCoordinatePeriod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The literal moving-frame displacement in the free induction

Source: `main.tex`, `thm:free`, (4.4), lines431–453.
DAG: `free-induction-displacement`; exclusive owner W2.
The target retains its genuine Euclidean norm. Products below are only block
coordinates; their continuous linear equivalence is not asserted isometric.
-/

noncomputable section
open scoped RealInnerProductSpace Manifold ContDiff Matrix.Norms.Elementwise

namespace GlobalEmbedding.Paper

local instance freeInductionDisplacementMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Actual Euclidean block reconstruction of (old,planar,appended) coordinates. -/
def freeAugmentCLM (k m : ℕ) :
    EuclideanSpace ℝ (Fin k) × (Planar × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k + (2 + m))) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p ↦ freeInductionBlock k m p.1 p.2.1 p.2.2
    map_add' := by
      intro p q
      ext j
      obtain ⟨j, rfl⟩ := (freeInductionIndexEquiv k m).surjective j
      rcases j with j | (j | j) <;>
        simp [freeInductionBlock_coordinate]
    map_smul' := by
      intro a p
      ext j
      obtain ⟨j, rfl⟩ := (freeInductionIndexEquiv k m).surjective j
      rcases j with j | (j | j) <;>
        simp [freeInductionBlock_coordinate]
  }

/-- The continuous linear wrapper uses precisely the common accepted target block. -/
@[simp] theorem freeAugmentCLM_eq_block (k m : ℕ)
    (p : EuclideanSpace ℝ (Fin k) × (Planar × EuclideanSpace ℝ (Fin m))) :
    freeAugmentCLM k m p = freeInductionBlock k m p.1 p.2.1 p.2.2 := rfl

/-- The actual block map has the original literal appended coordinate values. -/
theorem freeAugmentCLM_apply (k m : ℕ)
    (p : EuclideanSpace ℝ (Fin k) × (Planar × EuclideanSpace ℝ (Fin m))) :
    freeAugmentCLM k m p = WithLp.toLp 2 (Fin.append (fun i ↦ p.1 i)
      (Fin.append (fun i ↦ p.2.1 i) (fun i ↦ p.2.2 i))) := by
  ext j
  obtain ⟨j, rfl⟩ := (freeInductionIndexEquiv k m).surjective j
  change freeInductionBlock k m p.1 p.2.1 p.2.2 (freeInductionIndexEquiv k m j) = _
  rw [freeInductionBlock_coordinate]
  rcases j with j | (j | j) <;> simp [freeInductionIndexEquiv]

/-- The genuine Euclidean inner product splits into the three actual blocks. -/
theorem freeAugmentCLM_inner (k m : ℕ)
    (p q : EuclideanSpace ℝ (Fin k) × (Planar × EuclideanSpace ℝ (Fin m))) :
    ⟪freeAugmentCLM k m p, freeAugmentCLM k m q⟫ =
      ⟪p.1, q.1⟫ + ⟪p.2.1, q.2.1⟫ + ⟪p.2.2, q.2.2⟫ := by
  rw [freeAugmentCLM_eq_block, freeAugmentCLM_eq_block, freeInductionBlock_inner]
  ring

/-- The actual tail coordinate operator of R^(m+1), retaining the l2 target norm. -/
def freeTailCLM (m : ℕ) : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j ↦ EuclideanSpace.proj (𝕜 := ℝ) (Fin.succ j))

/-- The tail map is the literal remaining coefficient list. -/
@[simp] theorem freeTailCLM_apply (m : ℕ) (u : EuclideanSpace ℝ (Fin (m + 1))) (j : Fin m) :
    freeTailCLM m u j = u j.succ := rfl

/-- Actual complement-frame map T=(nu,e2,...), without assuming nu constant. -/
def freeComplementFrameCLM {k m : ℕ} (ν : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + (2 + m))) :=
  (freeAugmentCLM k m).comp
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (m + 1))).smulRight ν).prod
      ((0 : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] Planar).prod (freeTailCLM m)))

/-- Evaluation of the moving complement frame in the shared genuine target block. -/
@[simp] theorem freeComplementFrameCLM_apply {k m : ℕ}
    (ν : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin (m + 1))) :
    freeComplementFrameCLM ν v = freeInductionBlock k m (v 0 • ν) 0 (freeTailCLM m v) := rfl

/-- The true old derivative of the moving-frame vector retains the V0 Yi nu term. -/
def freeComplementVariation {k m : ℕ} (ν μ : EuclideanSpace ℝ (Fin k))
    (v u : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin (k + (2 + m))) :=
  freeAugmentCLM k m (u 0 • ν + v 0 • μ, 0, freeTailCLM m u)

private theorem coefficient_inner_head_tail {m : ℕ}
    (u v : EuclideanSpace ℝ (Fin (m + 1))) :
    ⟪u, v⟫ = u 0 * v 0 + ⟪freeTailCLM m u, freeTailCLM m v⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    star_trivial, Fin.sum_univ_succ, freeTailCLM_apply]
  ring

/-- Unit nu makes the actual complement-frame map preserve the true Euclidean inner product. -/
theorem freeComplementFrameCLM_inner {k m : ℕ} (ν : EuclideanSpace ℝ (Fin k))
    (hν : ‖ν‖ = 1) (u v : EuclideanSpace ℝ (Fin (m + 1))) :
    ⟪freeComplementFrameCLM ν u, freeComplementFrameCLM ν v⟫ = ⟪u, v⟫ := by
  change ⟪freeAugmentCLM k m (u 0 • ν, 0, freeTailCLM m u),
    freeAugmentCLM k m (v 0 • ν, 0, freeTailCLM m v)⟫ = _
  rw [freeAugmentCLM_inner, coefficient_inner_head_tail u v]
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hν, one_pow, mul_one, inner_zero_left, add_zero]
  ring

/-- Only the inner product with nu cancels the outside complement derivative;
the actual derivative vector mu itself is still present in the variation. -/
theorem freeComplementVariation_inner {k m : ℕ} (ν μ : EuclideanSpace ℝ (Fin k))
    (hν : ‖ν‖ = 1) (hμ : ⟪μ, ν⟫ = 0)
    (v u w : EuclideanSpace ℝ (Fin (m + 1))) :
    ⟪freeComplementVariation ν μ v u, freeComplementFrameCLM ν w⟫ = ⟪u, w⟫ := by
  change ⟪freeAugmentCLM k m (u 0 • ν + v 0 • μ, 0, freeTailCLM m u),
    freeAugmentCLM k m (w 0 • ν, 0, freeTailCLM m w)⟫ = _
  rw [freeAugmentCLM_inner, coefficient_inner_head_tail u w]
  simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hν, one_pow, mul_one, hμ, mul_zero, add_zero, inner_zero_left]
  ring

/-- Differentiating a genuine unit-vector curve gives the needed normal pairing zero. -/
theorem free_unit_curve_derivative_orthogonal {k : ℕ}
    (ν : ℝ → EuclideanSpace ℝ (Fin k)) (μ : EuclideanSpace ℝ (Fin k))
    (hd : HasDerivAt ν μ 0) (hunit : ∀ s, ‖ν s‖ = 1) : ⟪μ, ν 0⟫ = 0 := by
  have h := (hd.inner ℝ hd).deriv
  have he : (fun s ↦ ⟪ν s, ν s⟫) = fun _ : ℝ ↦ (1 : ℝ) := by
    funext s
    rw [real_inner_self_eq_norm_sq, hunit s, one_pow]
  rw [he, deriv_const] at h
  have hc := real_inner_comm (ν 0) μ
  linarith

/-- The actual moving-frame chain rule includes every derivative of nu. -/
theorem freeComplementFrameCLM_hasDerivAt {k m : ℕ}
    (ν : ℝ → EuclideanSpace ℝ (Fin k)) (v : ℝ → EuclideanSpace ℝ (Fin (m + 1)))
    (μ : EuclideanSpace ℝ (Fin k)) (u : EuclideanSpace ℝ (Fin (m + 1)))
    (hν : HasDerivAt ν μ 0) (hv : HasDerivAt v u 0) :
    HasDerivAt (fun s ↦ freeComplementFrameCLM (ν s) (v s))
      (freeComplementVariation (ν 0) μ (v 0) u) 0 := by
  change HasDerivAt
    (fun s ↦ freeAugmentCLM k m ((v s) 0 • ν s, 0, freeTailCLM m (v s)))
    (freeAugmentCLM k m (u 0 • ν 0 + (v 0) 0 • μ, 0, freeTailCLM m u)) 0
  have hh := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (m + 1))).hasFDerivAt.comp_hasDerivAt 0 hv
  have ht := (freeTailCLM m).hasFDerivAt.comp_hasDerivAt 0 hv
  have hp := (hh.smul hν).prodMk ((hasDerivAt_const (0 : ℝ) (0 : Planar)).prodMk ht)
  have h := (freeAugmentCLM k m).hasFDerivAt.comp_hasDerivAt 0 hp
  simp only [Function.comp_def, Pi.smul_apply', add_comm] at h
  convert h using 1 <;> rfl

/-- The literal original base map F0=(H,f,0_m) in the actual augmented target. -/
def freeInductionBase {M : Type*} {k m C : ℕ}
    (H : M → EuclideanSpace ℝ (Fin k)) (f : PlanarHopfSphere C → Planar)
    (p : M × PlanarHopfSphere C) : EuclideanSpace ℝ (Fin (k + (2 + m))) :=
  freeAugmentCLM k m (H p.1, f p.2, 0)

/-- The actual displacement Z=T(PA+delta eta Qn), with the genuine moving nu. -/
def freeInductionZ {M : Type*} {k m C : ℕ}
    (ν : M → EuclideanSpace ℝ (Fin k))
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere C → ℝ) (δ : ℝ)
    (A n : M → EuclideanSpace ℝ (Fin (m + 1))) (p : M × PlanarHopfSphere C) :
    EuclideanSpace ℝ (Fin (k + (2 + m))) :=
  freeComplementFrameCLM (ν p.1) (freeDisplacementVector P Q η δ (A p.1) (n p.1) p.2)

section Native
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {k m C : ℕ} [Fact (0 < C)]

omit [IsManifold I ∞ M] in
/-- The original actual base map is jointly native smooth on the whole product. -/
theorem freeInductionBase_contMDiff
    (H₀ : M → EuclideanSpace ℝ (Fin k)) (hH : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ H₀)
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f) :
    ContMDiff (I.prod (planarHopfModel C)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k + (2 + m)))) ∞
      (freeInductionBase (m := m) H₀ f) := by
  exact (freeAugmentCLM k m).contMDiff.comp
    ((hH.comp contMDiff_fst).prodMk_space ((hf.comp contMDiff_snd).prodMk_space contMDiff_const))

omit [IsManifold I ∞ M] in
/-- The literal actual Z, including its moving complement, is jointly native smooth. -/
theorem freeInductionZ_contMDiff
    (ν : M → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν)
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (η : PlanarHopfSphere C → ℝ) (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (A n : M → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n) :
    ContMDiff (I.prod (planarHopfModel C)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k + (2 + m)))) ∞
      (freeInductionZ ν P Q η δ A n) := by
  have hv := freeDisplacementVector_joint_contMDiff P Q hP hQ η hη A n hA hn δ
  have hhead := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (m + 1))).contMDiff.comp hv
  have htail := (freeTailCLM m).contMDiff.comp hv
  have hz : ContMDiff (I.prod (planarHopfModel C)) 𝓘(ℝ, Planar) ∞
      (fun _ : M × PlanarHopfSphere C ↦ (0 : Planar)) := contMDiff_const
  have h := (freeAugmentCLM k m).contMDiff.comp
    ((hhead.smul (hν.comp contMDiff_fst)).prodMk_space (hz.prodMk_space htail))
  convert h using 1
  funext p
  rfl

omit [TopologicalSpace M] in
/-- The active derivative of the literal Z has exactly the genuine active coordinate vector. -/
theorem freeInductionZ_active_orbitDeriv
    (ν : M → EuclideanSpace ℝ (Fin k))
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere C → ℝ) (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (A n : M → EuclideanSpace ℝ (Fin (m + 1)))
    (x : M) (z : PlanarHopfSphere C) :
    orbitDeriv (fun t (p : M × PlanarHopfSphere C) ↦ (p.1, planarHopfFlow t p.2))
      (freeInductionZ ν P Q η δ A n) (x, z) =
        freeComplementFrameCLM (ν x) (freeDisplacementActiveVector Q η δ (A x) (n x) z) := by
  have hv := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C) planarHopfFlow_add
    (freeDisplacementVector P Q η δ (A x) (n x))
    (freeDisplacementVector_contMDiff P Q hP hQ η hη δ (A x) (n x)) 0 z
  rw [planarHopfFlow_zero, freeDisplacementVector_orbitDeriv P Q hP hQ hPQ η hη δ] at hv
  have h := (freeComplementFrameCLM (ν x)).hasFDerivAt.comp_hasDerivAt 0 hv
  simpa only [orbitDeriv, freeInductionZ, Function.comp_def] using h.deriv

omit [Fact (0 < C)] [IsManifold I ∞ M] in
/-- The true old derivative of Z includes V0 times the old derivative of nu. -/
theorem freeInductionZ_old_orbitDeriv
    (S : PeriodOneSmoothFlow I M)
    (ν : M → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν)
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere C → ℝ) (δ : ℝ)
    (A n : M → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (x : M) (z : PlanarHopfSphere C) :
    orbitDeriv (fun t (p : M × PlanarHopfSphere C) ↦ (S.flow t p.1, p.2))
      (freeInductionZ ν P Q η δ A n) (x, z) =
      freeComplementVariation (ν x) (orbitDeriv S.flow ν x)
        (freeDisplacementVector P Q η δ (A x) (n x) z)
        (freeDisplacementOldVector P Q η δ (orbitDeriv S.flow A x) (orbitDeriv S.flow n x) z) := by
  have ha := hasDerivAt_orbit S.flow S.smooth S.flow_add A hA 0 x
  have hn' := hasDerivAt_orbit S.flow S.smooth S.flow_add n hn 0 x
  have hν' := hasDerivAt_orbit S.flow S.smooth S.flow_add ν hν 0 x
  simp only [S.flow_zero] at ha hn' hν'
  have hv := freeDisplacementVector_old_hasDerivAt P Q η δ
    (fun s ↦ A (S.flow s x)) (fun s ↦ n (S.flow s x))
    (orbitDeriv S.flow A x) (orbitDeriv S.flow n x) ha hn' z
  have h := freeComplementFrameCLM_hasDerivAt
    (fun s ↦ ν (S.flow s x))
    (fun s ↦ freeDisplacementVector P Q η δ (A (S.flow s x)) (n (S.flow s x)) z)
    (orbitDeriv S.flow ν x)
    (freeDisplacementOldVector P Q η δ (orbitDeriv S.flow A x) (orbitDeriv S.flow n x) z)
    hν' hv
  simpa only [orbitDeriv, freeInductionZ, S.flow_zero] using h.deriv

omit [IsManifold I ∞ M] in
/-- The actual moving-frame mixed pairing equals its literal complement-coordinate pairing.
Only its inner product vanishes for the outside derivative, never the derivative vector itself. -/
theorem freeInductionZ_mixed_inner
    (S : PeriodOneSmoothFlow I M)
    (ν : M → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν) (hunit : ∀ x, ‖ν x‖ = 1)
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere C → ℝ) (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (A n : M → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (x : M) (z : PlanarHopfSphere C) :
    ⟪orbitDeriv (fun t (p : M × PlanarHopfSphere C) ↦ (S.flow t p.1, p.2))
        (freeInductionZ ν P Q η δ A n) (x, z),
      orbitDeriv (fun t (p : M × PlanarHopfSphere C) ↦ (p.1, planarHopfFlow t p.2))
        (freeInductionZ ν P Q η δ A n) (x, z)⟫ =
    ⟪freeDisplacementOldVector P Q η δ (orbitDeriv S.flow A x) (orbitDeriv S.flow n x) z,
      freeDisplacementActiveVector Q η δ (A x) (n x) z⟫ := by
  have hd := hasDerivAt_orbit S.flow S.smooth S.flow_add ν hν 0 x
  simp only [S.flow_zero] at hd
  have horth := free_unit_curve_derivative_orthogonal
    (fun s ↦ ν (S.flow s x)) (orbitDeriv S.flow ν x) hd (fun s ↦ hunit (S.flow s x))
  simp only [S.flow_zero] at horth
  rw [freeInductionZ_old_orbitDeriv S ν hν P Q η δ A n hA hn,
    freeInductionZ_active_orbitDeriv ν P Q hP hQ hPQ η hη δ A n]
  exact freeComplementVariation_inner _ _ (hunit x) horth _ _ _

omit [IsManifold I ∞ M] [Fact (0 < C)] in
/-- A normal orthogonal to an actual first column and its actual old derivative has
old derivative orthogonal to that first column. Differentiate the actual identically
zero pairing; the second-column normal identity kills the other product-rule term.
Source: the old free normal in main.tex431–442. -/
theorem free_old_normal_derivative_inner
    (S : PeriodOneSmoothFlow I M) (ν B : M → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν)
    (hB : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ B)
    (hfirst : ∀ x, ⟪ν x, B x⟫ = 0)
    (hsecond : ∀ x, ⟪ν x, orbitDeriv S.flow B x⟫ = 0) (x : M) :
    ⟪orbitDeriv S.flow ν x, B x⟫ = 0 := by
  have dν := hasDerivAt_orbit S.flow S.smooth S.flow_add ν hν 0 x
  have dB := hasDerivAt_orbit S.flow S.smooth S.flow_add B hB 0 x
  simp only [S.flow_zero] at dν dB
  have hd := (dν.inner ℝ dB).deriv
  have he : (fun t : ℝ ↦ ⟪ν (S.flow t x), B (S.flow t x)⟫) = fun _ ↦ 0 :=
    funext fun t ↦ hfirst _
  rw [he, deriv_const, S.flow_zero, hsecond, zero_add] at hd
  exact hd.symm

omit [IsManifold I ∞ M] [Fact (0 < C)] in
/-- The old derivative of the actual base map is exactly its old target block.
The planar and appended coordinates are truly constant along this old orbit.
Source: F0=(H,f,0_m), main.tex431. -/
theorem freeInductionBase_old_orbitDeriv
    (S : PeriodOneSmoothFlow I M)
    (H₀ : M → EuclideanSpace ℝ (Fin k))
    (hH : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ H₀)
    (f : PlanarHopfSphere C → Planar) (x : M) (z : PlanarHopfSphere C) :
    orbitDeriv (fun t (p : M × PlanarHopfSphere C) ↦ (S.flow t p.1, p.2))
      (freeInductionBase (m := m) H₀ f) (x, z) =
      freeInductionBlock k m (orbitDeriv S.flow H₀ x) 0 0 := by
  have dh := hasDerivAt_orbit S.flow S.smooth S.flow_add H₀ hH 0 x
  simp only [S.flow_zero] at dh
  have hd := freeInductionBlock_hasDerivAt k m (fun t ↦ H₀ (S.flow t x))
    (fun _ : ℝ ↦ f z) (fun _ : ℝ ↦ (0 : EuclideanSpace ℝ (Fin m))) _ 0 0 0
    dh (hasDerivAt_const 0 _) (hasDerivAt_const 0 _)
  exact hd.deriv

omit [TopologicalSpace M] in
/-- The active derivative of the actual base map lies in the planar target block.
Source: F0=(H,f,0_m), main.tex431. -/
theorem freeInductionBase_active_orbitDeriv
    (H₀ : M → EuclideanSpace ℝ (Fin k)) (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (x : M) (z : PlanarHopfSphere C) :
    orbitDeriv (fun t (p : M × PlanarHopfSphere C) ↦ (p.1, planarHopfFlow t p.2))
      (freeInductionBase (m := m) H₀ f) (x, z) =
      freeInductionBlock k m 0 (orbitDeriv planarHopfFlow f z) 0 := by
  have df := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add f hf 0 z
  simp only [planarHopfFlow_zero] at df
  have hd := freeInductionBlock_hasDerivAt k m (fun _ : ℝ ↦ H₀ x)
    (fun t ↦ f (planarHopfFlow t z)) (fun _ : ℝ ↦ (0 : EuclideanSpace ℝ (Fin m)))
    0 _ 0 0 (hasDerivAt_const 0 _) df (hasDerivAt_const 0 _)
  exact hd.deriv

omit [IsManifold I ∞ M] in
/-- The actual mixed quadratic period of Z vanishes for the same P/Q/eta and
actual old immersive normal. The moving-frame pairing identity reduces the literal
physical derivative pairing to the accepted four-term coordinate theorem; unit n
is differentiated here, so no vanishing mixed period or derivative pairing is assumed.
Source: main.tex444–453. -/
theorem freeInductionZ_mixed_period_zero
    (S : PeriodOneSmoothFlow I M)
    (ν : M → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν) (hunit : ∀ x, ‖ν x‖ = 1)
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (hSO : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin (m + 1)) ℝ)
    (hperiod : ∀ z, orbitAverage planarHopfFlow (fun w ↦ (P w).transpose * Q w) z = 0)
    (η : PlanarHopfSphere C → ℝ) (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (hmean : ∀ z, orbitAverage planarHopfFlow η z = 0)
    (hquad : ∀ z, orbitAverage planarHopfFlow (fun w ↦
      η w ^ 2 • ((Q w).transpose * orbitDeriv planarHopfFlow Q w)) z = 0)
    (δ : ℝ) (A n : M → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (hnunit : ∀ x, ‖n x‖ = 1)
    (hnorth : ∀ x, ⟪orbitDeriv S.flow A x, n x⟫ = 0)
    (x : M) (z : PlanarHopfSphere C) :
    orbitAverage (fun t (p : M × PlanarHopfSphere C) ↦ (p.1, planarHopfFlow t p.2))
      (fun p ↦ ⟪orbitDeriv (fun t (q : M × PlanarHopfSphere C) ↦ (S.flow t q.1, q.2))
          (freeInductionZ ν P Q η δ A n) p,
        orbitDeriv (fun t (q : M × PlanarHopfSphere C) ↦ (q.1, planarHopfFlow t q.2))
          (freeInductionZ ν P Q η δ A n) p⟫) (x, z) = 0 := by
  have dn := hasDerivAt_orbit S.flow S.smooth S.flow_add n hn 0 x
  simp only [S.flow_zero] at dn
  have hnormal := free_unit_curve_derivative_orthogonal
    (fun t ↦ n (S.flow t x)) (orbitDeriv S.flow n x) dn (fun t ↦ hnunit _)
  simp only [S.flow_zero] at hnormal
  have he : (fun w : PlanarHopfSphere C ↦
      ⟪orbitDeriv (fun t (q : M × PlanarHopfSphere C) ↦ (S.flow t q.1, q.2))
          (freeInductionZ ν P Q η δ A n) (x, w),
        orbitDeriv (fun t (q : M × PlanarHopfSphere C) ↦ (q.1, planarHopfFlow t q.2))
          (freeInductionZ ν P Q η δ A n) (x, w)⟫) =
      (fun w ↦ ⟪freeDisplacementOldVector P Q η δ
        (orbitDeriv S.flow A x) (orbitDeriv S.flow n x) w,
        freeDisplacementActiveVector Q η δ (A x) (n x) w⟫) := by
    funext w
    exact freeInductionZ_mixed_inner S ν hν hunit P Q hP hQ hPQ η hη δ A n hA hn x w
  change orbitAverage planarHopfFlow (fun w : PlanarHopfSphere C ↦
      ⟪orbitDeriv (fun t (q : M × PlanarHopfSphere C) ↦ (S.flow t q.1, q.2))
          (freeInductionZ ν P Q η δ A n) (x, w),
        orbitDeriv (fun t (q : M × PlanarHopfSphere C) ↦ (q.1, planarHopfFlow t q.2))
          (freeInductionZ ν P Q η δ A n) (x, w)⟫) z = 0
  rw [he]
  exact free_mixed_coordinate_period_zero P Q hP hQ hPQ hSO hperiod η hη hmean hquad δ
    (A x) (orbitDeriv S.flow A x) (n x) (orbitDeriv S.flow n x) (hnorth x) hnormal z

/-- Every actual first column of F0 is orthogonal to every actual first column
of Z. Old-old rows differentiate the genuine first-column normal equation and use
the genuine old second-column normal equation; active rows use the actual planar
block orthogonality. Thus this statement computes the actual derivative pairings,
not a formal substitute for the first metric variation. Source: main.tex441–442. -/
theorem freeInduction_first_pairing_zero
    (S : Fin m → PeriodOneSmoothFlow I M)
    (H₀ ν : M → EuclideanSpace ℝ (Fin k))
    (hH : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ H₀)
    (hν : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν)
    (hfirst : ∀ x i, ⟪ν x, orbitDeriv (S i).flow H₀ x⟫ = 0)
    (hsecond : ∀ x i j,
      ⟪ν x, orbitDeriv (S i).flow (orbitDeriv (S j).flow H₀) x⟫ = 0)
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere C → ℝ) (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (A n : M → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n) :
    let R : Fin (m + 1) → ℝ → (M × PlanarHopfSphere C) → M × PlanarHopfSphere C :=
      Fin.lastCases (fun t p ↦ (p.1, planarHopfFlow t p.2))
        (fun i t p ↦ ((S i).flow t p.1, p.2))
    ∀ (x : M) (z : PlanarHopfSphere C) i j,
      ⟪orbitDeriv (R i) (freeInductionBase (m := m) H₀ f) (x, z),
        orbitDeriv (R j) (freeInductionZ ν P Q η δ A n) (x, z)⟫ = 0 := by
  dsimp only
  intro x z i j
  have hνH (i : Fin m) : ⟪orbitDeriv (S i).flow H₀ x, ν x⟫ = 0 := by
    rw [real_inner_comm]
    exact hfirst x i
  have hμH (i j : Fin m) :
      ⟪orbitDeriv (S i).flow H₀ x, orbitDeriv (S j).flow ν x⟫ = 0 := by
    rw [real_inner_comm]
    exact free_old_normal_derivative_inner (S j) ν (orbitDeriv (S i).flow H₀) hν
      (contMDiff_orbitDeriv (S i).flow (S i).smooth H₀ hH)
      (fun y ↦ hfirst y i) (fun y ↦ hsecond y j i) x
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp only [Fin.lastCases_last]
      rw [freeInductionBase_active_orbitDeriv H₀ f hf,
        freeInductionZ_active_orbitDeriv ν P Q hP hQ hPQ η hη δ A n]
      simp only [freeComplementFrameCLM_apply, freeInductionBlock_inner,
        inner_zero_left, inner_zero_right, add_zero]
    · simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      rw [freeInductionBase_active_orbitDeriv H₀ f hf,
        freeInductionZ_old_orbitDeriv (S j) ν hν P Q η δ A n hA hn]
      simp only [freeComplementVariation, freeAugmentCLM_eq_block,
        freeInductionBlock_inner, inner_zero_left, inner_zero_right, add_zero]
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
      rw [freeInductionBase_old_orbitDeriv (S i) H₀ hH f,
        freeInductionZ_active_orbitDeriv ν P Q hP hQ hPQ η hη δ A n]
      simp only [freeComplementFrameCLM_apply, freeInductionBlock_inner,
        real_inner_smul_right, hνH, mul_zero, inner_zero_left, add_zero]
    · simp only [Fin.lastCases_castSucc]
      rw [freeInductionBase_old_orbitDeriv (S i) H₀ hH f,
        freeInductionZ_old_orbitDeriv (S j) ν hν P Q η δ A n hA hn]
      simp only [freeComplementVariation, freeAugmentCLM_eq_block,
        freeInductionBlock_inner, inner_add_right, real_inner_smul_right,
        hνH, hμH, mul_zero, inner_zero_left, add_zero]

/-- The literal first metric variation Dgamma(F0)Z is zero in every actual
old or active row. Both product-rule terms are the genuine derivatives of the
same fixed F0 and Z; the preceding actual pairing theorem kills each one.
Source: main.tex442, before any quadratic W correction. -/
theorem freeInduction_first_variation_zero
    (S : Fin m → PeriodOneSmoothFlow I M)
    (H₀ ν : M → EuclideanSpace ℝ (Fin k))
    (hH : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ H₀)
    (hν : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν)
    (hfirst : ∀ x i, ⟪ν x, orbitDeriv (S i).flow H₀ x⟫ = 0)
    (hsecond : ∀ x i j,
      ⟪ν x, orbitDeriv (S i).flow (orbitDeriv (S j).flow H₀) x⟫ = 0)
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere C → ℝ) (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (A n : M → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n) :
    let R : Fin (m + 1) → ℝ → (M × PlanarHopfSphere C) → M × PlanarHopfSphere C :=
      Fin.lastCases (fun t p ↦ (p.1, planarHopfFlow t p.2))
        (fun i t p ↦ ((S i).flow t p.1, p.2))
    ∀ (x : M) (z : PlanarHopfSphere C) i j,
      ⟪orbitDeriv (R i) (freeInductionBase (m := m) H₀ f) (x, z),
        orbitDeriv (R j) (freeInductionZ ν P Q η δ A n) (x, z)⟫ +
      ⟪orbitDeriv (R i) (freeInductionZ ν P Q η δ A n) (x, z),
        orbitDeriv (R j) (freeInductionBase (m := m) H₀ f) (x, z)⟫ = 0 := by
  have hz := freeInduction_first_pairing_zero S H₀ ν hH hν hfirst hsecond f hf
    P Q hP hQ hPQ η hη δ A n hA hn
  dsimp only at hz ⊢
  intro x z i j
  rw [hz x z i j, real_inner_comm, hz x z j i, add_zero]

end Native

end GlobalEmbedding.Paper
