import GlobalEmbedding.Paper.FreeSelectorProperties
import GlobalEmbedding.Paper.FrameGramInverseIdentities
import GlobalEmbedding.Paper.SmoothFrameGramCoefficients
import GlobalEmbedding.Paper.ManifoldFiniteOperatorSmoothness
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Constructing the actual old free pairing solution

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 472–473.
DAG node: `free-old-pairing-lift`.
The inverse-Gram identities and smoothness are reused, not proved again.
-/

noncomputable section

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/- This private finite-sum adapter follows the private framedCoordinateOperator in
FramedDistributionSmoothCoframe, generalized only from Fin b to the actual finite index.
The source's private declaration is unavailable through the normal public import API. -/
private def freeOldSynthesis (v : κ → V) : EuclideanSpace ℝ κ →L[ℝ] V :=
  ∑ i, (EuclideanSpace.proj i).smulRight (v i)

omit [DecidableEq κ] [CompleteSpace V] in
private theorem freeOldSynthesis_apply (v : κ → V) (a : EuclideanSpace ℝ κ) :
    freeOldSynthesis v a = ∑ i, a i • v i := by
  simp [freeOldSynthesis]

omit [CompleteSpace V] in
private theorem freeOldSynthesis_single (v : κ → V) (i : κ) :
    freeOldSynthesis v (EuclideanSpace.single i 1) = v i := by
  rw [freeOldSynthesis_apply]
  simp [EuclideanSpace.single]

omit [DecidableEq κ] [CompleteSpace V] in
private theorem freeOldSynthesis_injective (v : κ → V) (hv : LinearIndependent ℝ v) :
    Function.Injective (freeOldSynthesis v) := by
  intro a b hab
  have hcoeff : (fun i ↦ a i) = (fun i ↦ b i) :=
    hv.fintypeLinearCombination_injective (by
      simpa only [Fintype.linearCombination_apply, freeOldSynthesis_apply] using hab)
  ext i
  exact congrFun hcoeff i

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Actual independent smooth columns admit a smooth solution of every full pairing
datum. The accepted smooth inverse-Gram coefficient operator L satisfies L A=id.
Set W=L* g. On each real coordinate vector, the adjoint identity gives
inner(v_i,W)=inner(L A e_i,g)=g_i. Thus neither the inverse nor W is an input.
This is the actual finite-dimensional construction used for W_H at line 472.
Empty index families and arbitrary native source models are included. -/
theorem free_smooth_pairing_lift (v : κ → M → V)
    (hv : ∀ i, ContMDiff I 𝓘(ℝ, V) ∞ (v i))
    (hind : ∀ x, LinearIndependent ℝ (fun i ↦ v i x))
    (g : M → EuclideanSpace ℝ κ)
    (hg : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ κ) ∞ g) :
    ∃ W : M → V, ContMDiff I 𝓘(ℝ, V) ∞ W ∧
      ∀ x i, inner ℝ (v i x) (W x) = g x i := by
  let A (x : M) : EuclideanSpace ℝ κ →L[ℝ] V := freeOldSynthesis (fun i ↦ v i x)
  have hA : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ κ →L[ℝ] V) ∞ A := by
    intro x
    apply (manifold_finite_operator_smooth_iff A x).mpr
    intro a
    have hs : ContMDiff I 𝓘(ℝ, V) ∞ (fun y ↦ ∑ i, a i • v i y) :=
      contMDiff_finsetSum fun i _ ↦
        (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ a i)).smul (hv i)
    simpa only [A, freeOldSynthesis_apply] using hs.contMDiffAt (x := x)
  have hinj (x : M) : Function.Injective (A x) :=
    freeOldSynthesis_injective _ (hind x)
  let L (x : M) : V →L[ℝ] EuclideanSpace ℝ κ :=
    ((A x).adjoint.comp (A x)).inverse.comp (A x).adjoint
  have hL : ContMDiff I 𝓘(ℝ, V →L[ℝ] EuclideanSpace ℝ κ) ∞ L := by
    exact contMDiffOn_univ.mp
      (smooth_frame_gram_coefficients A (s := Set.univ) hA.contMDiffOn (fun x _ ↦ hinj x))
  let adj : (V →L[ℝ] EuclideanSpace ℝ κ) →L[ℝ]
      (EuclideanSpace ℝ κ →L[ℝ] V) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := EuclideanSpace ℝ κ)).toContinuousLinearEquiv.toContinuousLinearMap
  have hLadj : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ κ →L[ℝ] V) ∞
      (fun x ↦ (L x).adjoint) := adj.contDiff.contMDiff.comp hL
  refine ⟨fun x ↦ (L x).adjoint (g x), hLadj.clm_apply hg, ?_⟩
  intro x i
  have hi := congrArg (fun T : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ ↦
    T (EuclideanSpace.single i 1)) (frame_gram_inverse_identities (A x) (hinj x)).1
  change L x (A x (EuclideanSpace.single i 1)) = EuclideanSpace.single i 1 at hi
  have hAi : A x (EuclideanSpace.single i 1) = v i x := freeOldSynthesis_single _ i
  rw [hAi] at hi
  rw [ContinuousLinearMap.adjoint_inner_right, hi]
  simp [EuclideanSpace.inner_single_left]

/-- The full old first/second datum used in the source's actual W_H construction.
Both differentiated w terms and the genuine quadratic displacement pairing occur.
Every symmetric second coordinate is retained, including i=j.
Source: the two pairing equations at line 472. -/
def freeOldPairingData {a N : ℕ} (S : Fin a → ℝ → M → M)
    (w : Fin a → M → ℝ) (Z : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    EuclideanSpace ℝ (BalancedPairingIndex a) :=
  WithLp.toLp 2 (fun j ↦ match j with
    | Sum.inl i => w i x
    | Sum.inr ij => (orbitDeriv (S ij.val.1) (w ij.val.2) x +
        orbitDeriv (S ij.val.2) (w ij.val.1) x +
        inner ℝ (orbitDeriv (S ij.val.1) Z x) (orbitDeriv (S ij.val.2) Z x)) / 2)

/-- The actual W_H datum is native smooth. Each coordinate uses the accepted
actual smooth orbit derivative and genuine inner-product calculus, so there is
no assumed smooth pairing operator or formal derivative in this construction.
Source: the old free pairing data at line 472. -/
theorem freeOldPairingData_contMDiff [IsManifold I ∞ M] {a N : ℕ}
    (S : Fin a → PeriodOneSmoothFlow I M)
    (w : Fin a → M → ℝ) (hw : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (w i))
    (Z : M → EuclideanSpace ℝ (Fin N))
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex a)) ∞
      (freeOldPairingData (fun i ↦ (S i).flow) w Z) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : BalancedPairingIndex a ↦ ℝ)).symm
  apply e.contDiff.contMDiff.comp
  apply contMDiff_pi_module_iff.mpr
  intro j
  cases j with
  | inl i => exact hw i
  | inr ij =>
    have h1 := contMDiff_orbitDeriv (S ij.val.1).flow (S ij.val.1).smooth _ (hw ij.val.2)
    have h2 := contMDiff_orbitDeriv (S ij.val.2).flow (S ij.val.2).smooth _ (hw ij.val.1)
    have hZi := contMDiff_orbitDeriv (S ij.val.1).flow (S ij.val.1).smooth Z hZ
    have hZj := contMDiff_orbitDeriv (S ij.val.2).flow (S ij.val.2).smooth Z hZ
    exact ((h1.add h2).add
      ((contDiff_inner (𝕜 := ℝ)).contMDiff.comp (hZi.prodMk_space hZj))).div_const 2

/-- The original old free columns themselves construct W_H with exactly the
source's first and ordered symmetric second pairings. Apply the proved smooth
pairing lift to the literal old flow columns and the actual data just defined.
There is no desired W_H, Gram inverse, or old pairing solution among the inputs.
Source: lines 472–473 of the free-selector induction. -/
theorem free_old_second_correction_exists [IsManifold I ∞ M] {a K N : ℕ}
    (S : Fin a → PeriodOneSmoothFlow I M)
    (F : M → EuclideanSpace ℝ (Fin K))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ F)
    (hind : ∀ x, LinearIndependent ℝ (freeFlowColumns (fun i ↦ (S i).flow) F x))
    (w : Fin a → M → ℝ) (hw : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (w i))
    (Z : M → EuclideanSpace ℝ (Fin N))
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z) :
    ∃ W : M → EuclideanSpace ℝ (Fin K),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ W ∧
      (∀ x i, inner ℝ (orbitDeriv (S i).flow F x) (W x) = w i x) ∧
      (∀ x (ij : {p : Fin a × Fin a // p.1 ≤ p.2}),
        2 * inner ℝ (orbitDeriv (S ij.val.1).flow (orbitDeriv (S ij.val.2).flow F) x)
          (W x) = orbitDeriv (S ij.val.1).flow (w ij.val.2) x +
            orbitDeriv (S ij.val.2).flow (w ij.val.1) x +
            inner ℝ (orbitDeriv (S ij.val.1).flow Z x)
              (orbitDeriv (S ij.val.2).flow Z x)) := by
  have hc (j : BalancedPairingIndex a) :
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞
        (fun x ↦ freeFlowColumns (fun i ↦ (S i).flow) F x j) := by
    cases j with
    | inl i => exact contMDiff_orbitDeriv (S i).flow (S i).smooth F hF
    | inr ij =>
      exact contMDiff_orbitDeriv (S ij.val.1).flow (S ij.val.1).smooth _
        (contMDiff_orbitDeriv (S ij.val.2).flow (S ij.val.2).smooth F hF)
  obtain ⟨W, hW, hpair⟩ := free_smooth_pairing_lift
    (fun j x ↦ freeFlowColumns (fun i ↦ (S i).flow) F x j) hc hind
    (freeOldPairingData (fun i ↦ (S i).flow) w Z)
    (freeOldPairingData_contMDiff S w hw Z hZ)
  refine ⟨W, hW, fun x i ↦ hpair x (Sum.inl i), ?_⟩
  intro x ij
  have hs := hpair x (Sum.inr ij)
  change inner ℝ (orbitDeriv (S ij.val.1).flow (orbitDeriv (S ij.val.2).flow F) x)
      (W x) = (_ + _ + _) / 2 at hs
  linarith

#print axioms free_smooth_pairing_lift
#print axioms freeOldPairingData_contMDiff
#print axioms free_old_second_correction_exists

end GlobalEmbedding.Paper
