import GlobalEmbedding.Paper.FreeInductionDisplacement
import GlobalEmbedding.Paper.FreeMixedPeriodIdentity
import GlobalEmbedding.Paper.FreeUniformPivotEstimates

/-!
# The genuine mixed second displacement columns in the common moving frame

Source: `main.tex`, `thm:free`, lines444–469.
DAG: `free-induction-columns`; exclusive owner W2.
F0 base-column normalization and annihilation belong solely to W4.
-/

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace Matrix.Norms.Elementwise

namespace GlobalEmbedding.Paper

local instance freeInductionMixedColumnsMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The true old derivative of the active coordinate vector is exactly the existing
mixed coordinate M_i. Fixed genuine matrix CLMs act on the actual old A/n curves;
no derivative of the old moving frame is hidden in this coordinate statement.
Source: (4.5), main.tex455–459. -/
theorem freeDisplacementActiveVector_old_hasDerivAt {C d : ℕ}
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (η : PlanarHopfSphere C → ℝ) (δ : ℝ)
    (a n : ℝ → EuclideanSpace ℝ (Fin d)) (da dn : EuclideanSpace ℝ (Fin d))
    (ha : HasDerivAt a da 0) (hn : HasDerivAt n dn 0) (z : PlanarHopfSphere C) :
    HasDerivAt (fun s ↦ freeDisplacementActiveVector Q η δ (a s) (n s) z)
      (freeDisplacementMixedVector Q η δ da dn z) 0 := by
  have hqa := (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z)).hasFDerivAt.comp_hasDerivAt 0 ha
  have hqn := (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z)).hasFDerivAt.comp_hasDerivAt 0 hn
  have hxn := (Matrix.toEuclideanCLM (𝕜 := ℝ)
    (orbitDeriv planarHopfFlow Q z)).hasFDerivAt.comp_hasDerivAt 0 hn
  have hd := hqa.fun_add (((hqn.const_smul (orbitDeriv planarHopfFlow η z)).fun_add
    (hxn.const_smul (η z))).const_smul δ)
  simpa only [freeDisplacementActiveVector, freeDisplacementMixedVector,
    Function.comp_def, Pi.add_apply, Pi.smul_apply] using hd

/-- The same genuine complement frame preserves the actual Euclidean norm.
Source: the orthonormal complement T in main.tex433–435. -/
theorem freeComplementFrameCLM_norm {k m : ℕ} (ν : EuclideanSpace ℝ (Fin k))
    (hν : ‖ν‖ = 1) (v : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖freeComplementFrameCLM ν v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, freeComplementFrameCLM_inner ν hν]
  exact (norm_eq_sqrt_real_inner v).symm

/-- The actual normal error is transported isometrically by the same frame.
Source: the projected-normal error in main.tex461–469. -/
theorem freeComplementFrameCLM_norm_sub {k m : ℕ} (ν : EuclideanSpace ℝ (Fin k))
    (hν : ‖ν‖ = 1) (v w : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖freeComplementFrameCLM ν v - freeComplementFrameCLM ν w‖ = ‖v - w‖ := by
  rw [← map_sub, freeComplementFrameCLM_norm ν hν]

section Native
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {k m C : ℕ}

/-- Differentiating the actual active-frame map along an old orbit retains the
entire outside-complement term, with its complement coefficient exactly M_i.
Source: (4.5) in main.tex455–459 and the actual moving frame at433–435. -/
theorem freeInductionActiveFrame_old_orbitDeriv
    (S : PeriodOneSmoothFlow I M)
    (ν : M → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν)
    (Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere C → ℝ) (δ : ℝ)
    (A n : M → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (x : M) (z : PlanarHopfSphere C) :
    orbitDeriv (fun t (p : M × PlanarHopfSphere C) ↦ (S.flow t p.1, p.2))
      (fun p ↦ freeComplementFrameCLM (ν p.1)
        (freeDisplacementActiveVector Q η δ (A p.1) (n p.1) p.2)) (x, z) =
      freeComplementVariation (ν x) (orbitDeriv S.flow ν x)
        (freeDisplacementActiveVector Q η δ (A x) (n x) z)
        (freeDisplacementMixedVector Q η δ (orbitDeriv S.flow A x) (orbitDeriv S.flow n x) z) := by
  have ha := hasDerivAt_orbit S.flow S.smooth S.flow_add A hA 0 x
  have hn' := hasDerivAt_orbit S.flow S.smooth S.flow_add n hn 0 x
  have hν' := hasDerivAt_orbit S.flow S.smooth S.flow_add ν hν 0 x
  simp only [S.flow_zero] at ha hn' hν'
  have hv := freeDisplacementActiveVector_old_hasDerivAt Q η δ
    (fun s ↦ A (S.flow s x)) (fun s ↦ n (S.flow s x))
    (orbitDeriv S.flow A x) (orbitDeriv S.flow n x) ha hn' z
  have hd := freeComplementFrameCLM_hasDerivAt
    (fun s ↦ ν (S.flow s x))
    (fun s ↦ freeDisplacementActiveVector Q η δ (A (S.flow s x)) (n (S.flow s x)) z)
    (orbitDeriv S.flow ν x)
    (freeDisplacementMixedVector Q η δ (orbitDeriv S.flow A x) (orbitDeriv S.flow n x) z)
    hν' hv
  simpa only [orbitDeriv, S.flow_zero] using hd.deriv

variable [Fact (0 < C)]

omit [TopologicalSpace M] in
/-- The actual active second derivative of the actual Z is T times the actual
second derivative of its original coordinate vector. The old normal is fixed on
the genuine active orbit; no coordinate pivot identity is reproved here.
Source: X²Z in main.tex461–469. -/
theorem freeInductionZ_active_second
    (ν : M → EuclideanSpace ℝ (Fin k))
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere C → ℝ) (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (A n : M → EuclideanSpace ℝ (Fin (m + 1)))
    (x : M) (z : PlanarHopfSphere C) :
    orbitDeriv (fun t (p : M × PlanarHopfSphere C) ↦ (p.1, planarHopfFlow t p.2))
      (orbitDeriv (fun t (p : M × PlanarHopfSphere C) ↦ (p.1, planarHopfFlow t p.2))
        (freeInductionZ ν P Q η δ A n)) (x, z) =
      freeComplementFrameCLM (ν x) (orbitDeriv planarHopfFlow
        (orbitDeriv planarHopfFlow (freeDisplacementVector P Q η δ (A x) (n x))) z) := by
  have he : orbitDeriv (fun t (p : M × PlanarHopfSphere C) ↦ (p.1, planarHopfFlow t p.2))
      (freeInductionZ ν P Q η δ A n) = fun p ↦ freeComplementFrameCLM (ν p.1)
        (orbitDeriv planarHopfFlow (freeDisplacementVector P Q η δ (A p.1) (n p.1)) p.2) := by
    funext p
    rw [freeInductionZ_active_orbitDeriv ν P Q hP hQ hPQ η hη δ A n,
      freeDisplacementVector_orbitDeriv P Q hP hQ hPQ η hη δ]
  rw [he]
  have hV := freeDisplacementVector_contMDiff P Q hP hQ η hη δ (A x) (n x)
  have hXV := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ hV
  have hd := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add _ hXV 0 z
  rw [planarHopfFlow_zero] at hd
  have hh := (freeComplementFrameCLM (ν x)).hasFDerivAt.comp_hasDerivAt 0 hd
  simpa only [orbitDeriv, Function.comp_def] using hh.deriv

end Native

section Hopf
variable {m k : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]

local instance freeMixedColumnsOldPositive (i : Fin m) :
    Fact (0 < freeHopfOldDimensions C i) := inferInstanceAs (Fact (0 < C i.castSucc))

/-- The genuine original mixed second column of Z equals the moving-frame
variation with exactly the already defined coordinate M_i. The full outside term
(XV)_0 Yi nu remains in the displayed actual vector. Source: main.tex455–459. -/
theorem freeHopfInductionZ_mixed_second
    (ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η) (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n) (i : Fin m) (x : FreeHopfProduct C) :
    freeHopfDeriv C i.castSucc
      (freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n)) x =
      let y := (freeHopfProductSplit C x).1
      let z := (freeHopfProductSplit C x).2
      freeComplementVariation (ν y) (freeHopfDeriv (freeHopfOldDimensions C) i ν y)
        (freeDisplacementActiveVector Q η δ (A y) (n y) z)
        (freeDisplacementMixedVector Q η δ
          (freeHopfDeriv (freeHopfOldDimensions C) i A y)
          (freeHopfDeriv (freeHopfOldDimensions C) i n y) z) := by
  let G := fun p : FreeHopfProduct (freeHopfOldDimensions C) ×
      PlanarHopfSphere (C (Fin.last m)) ↦ freeComplementFrameCLM (ν p.1)
        (freeDisplacementActiveVector Q η δ (A p.1) (n p.1) p.2)
  have he : freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n) =
      fun y ↦ G (freeHopfProductSplit C y) := by
    funext y
    exact freeHopfInductionZ_deriv_last C ν P Q hP hQ hPQ η hη δ A n y
  rw [he, freeHopfDeriv_split_old]
  exact freeInductionActiveFrame_old_orbitDeriv
    (freeHopfProductSmoothFlow (freeHopfOldDimensions C) i) ν hν Q η δ A n hA hn _ _

/-- The genuine original active second column of Z is the same T applied to
W3's actual coordinate X²V. This uses the accepted true active differentiation
and does not rederive the coordinate second-derivative or pivot calculation.
Source: main.tex461–469. -/
theorem freeHopfInductionZ_active_second
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
    freeHopfDeriv C (Fin.last m)
      (freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n)) x =
      freeComplementFrameCLM (ν (freeHopfProductSplit C x).1)
        (freePivotActiveSecond (freeHopfOldDimensions C) P Q η A n δ (freeHopfProductSplit C x)) := by
  let G := freeInductionZ ν P Q η δ A n
  have he : freeHopfDeriv C (Fin.last m) (fun y ↦ G (freeHopfProductSplit C y)) =
      fun y ↦ orbitDeriv (fun t p ↦ (p.1, planarHopfFlow t p.2)) G (freeHopfProductSplit C y) := by
    funext y
    exact freeHopfDeriv_split_last C G y
  change freeHopfDeriv C (Fin.last m)
    (freeHopfDeriv C (Fin.last m) (fun y ↦ G (freeHopfProductSplit C y))) x = _
  rw [he, freeHopfDeriv_split_last]
  exact freeInductionZ_active_second ν P Q hP hQ hPQ η hη δ A n _ _

/-- Pairing the true mixed second column with any actual complement-frame vector
is precisely pairing the same vector with W3's coordinate M_i. Only the scalar
normal pairing vanishes; the full outside Yi nu term remains in the actual column.
Source: (4.5), main.tex455–469. -/
theorem freeHopfInductionZ_mixed_frame_inner
    (ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν) (hunit : ∀ y, ‖ν y‖ = 1)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η) (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n) (i : Fin m) (x : FreeHopfProduct C)
    (w : EuclideanSpace ℝ (Fin (m + 1))) :
    ⟪freeComplementFrameCLM (ν (freeHopfProductSplit C x).1) w,
      freeHopfDeriv C i.castSucc
        (freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n)) x⟫ =
      ⟪w, freeDisplacementMixedVector Q η δ
        (freeHopfDeriv (freeHopfOldDimensions C) i A (freeHopfProductSplit C x).1)
        (freeHopfDeriv (freeHopfOldDimensions C) i n (freeHopfProductSplit C x).1)
        (freeHopfProductSplit C x).2⟫ := by
  let y := (freeHopfProductSplit C x).1
  let S := freeHopfProductSmoothFlow (freeHopfOldDimensions C) i
  have hd := hasDerivAt_orbit S.flow S.smooth S.flow_add ν hν 0 y
  simp only [S.flow_zero] at hd
  have ho := free_unit_curve_derivative_orthogonal
    (fun t ↦ ν (S.flow t y)) (orbitDeriv S.flow ν y) hd (fun t ↦ hunit _)
  simp only [S.flow_zero] at ho
  change ⟪freeHopfDeriv (freeHopfOldDimensions C) i ν y, ν y⟫ = 0 at ho
  rw [freeHopfInductionZ_mixed_second C ν hν P Q hP hQ hPQ η hη δ A n hA hn i x]
  dsimp only
  rw [real_inner_comm]
  rw [freeComplementVariation_inner (ν y)
    (freeHopfDeriv (freeHopfOldDimensions C) i ν y) (hunit y) ho]
  exact real_inner_comm _ _

/-- The actual active pivot pairing is exactly its existing coordinate pivot,
for every complement vector. In particular this applies to W3's actual projected
normal and preserves its actual buffered lower bound. Source: main.tex461–469. -/
theorem freeHopfInductionZ_active_frame_inner
    (ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hunit : ∀ y, ‖ν y‖ = 1)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η) (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (x : FreeHopfProduct C)
    (w : EuclideanSpace ℝ (Fin (m + 1))) :
    ⟪freeComplementFrameCLM (ν (freeHopfProductSplit C x).1) w,
      freeHopfDeriv C (Fin.last m)
        (freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n)) x⟫ =
      ⟪w, freePivotActiveSecond (freeHopfOldDimensions C) P Q η A n δ
        (freeHopfProductSplit C x)⟫ := by
  rw [freeHopfInductionZ_active_second C ν P Q hP hQ hPQ η hη δ A n x,
    freeComplementFrameCLM_inner _ (hunit _)]

/-- W3's same genuinely projected coordinate normal, placed in the true moving
frame, is perpendicular to every actual mixed second Z column, including its
outside-complement contribution. No rank or normal orthogonality is assumed.
Source: the actual normal direction in main.tex461–469. -/
theorem freeHopfInductionZ_pivot_normal_mixed_zero
    (ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin k))
    (hν : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ ν) (hunit : ∀ y, ‖ν y‖ = 1)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η) (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n) (i : Fin m) (x : FreeHopfProduct C) :
    let p := freeHopfProductSplit C x
    ⟪freeComplementFrameCLM (ν p.1)
        (freePivotNormal (freeHopfOldDimensions C) Q η A n δ p),
      freeHopfDeriv C i.castSucc
        (freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n)) x⟫ = 0 := by
  dsimp only
  rw [freeHopfInductionZ_mixed_frame_inner C ν hν hunit P Q hP hQ hPQ η hη δ A n hA hn]
  let p := freeHopfProductSplit C x
  let L := freePivotMixedFrame (freeHopfOldDimensions C) Q η A n δ p
  have hmem : freeDisplacementMixedVector Q η δ
      (freeHopfDeriv (freeHopfOldDimensions C) i A p.1)
      (freeHopfDeriv (freeHopfOldDimensions C) i n p.1) p.2 ∈ LinearMap.range L.toLinearMap := by
    refine ⟨EuclideanSpace.single i 1, ?_⟩
    simp [L, freePivotMixedFrame, freeColumnOperator_apply]
  exact Submodule.inner_left_of_mem_orthogonal hmem
    (Submodule.starProjection_apply_mem (LinearMap.range L.toLinearMap)ᗮ
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1)))

end Hopf

end GlobalEmbedding.Paper
