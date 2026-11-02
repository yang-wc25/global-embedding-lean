import GlobalEmbedding.Paper.FreeHopfProductNative
import GlobalEmbedding.Paper.PlanarHopfGenerator
import GlobalEmbedding.Paper.FramedDistribution
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# The genuine native generators and frame on the whole Hopf product

Source: `literature/parallelizable-stable-plus-one/main.tex`, setup:partial, lines216–232.
DAG node: `free-hopf-product-generators`.
-/

noncomputable section

open Manifold
open Bundle (TotalSpace)
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]

/-- The genuine tangent map of the actual i-th factor action on the time-unit tangent. -/
def freeHopfGeneratorTangentLift (i : Fin a) (x : FreeHopfProduct C) :
    TangentBundle (freeHopfModel C) (FreeHopfProduct C) :=
  tangentMap (𝓘(ℝ, ℝ).prod (freeHopfModel C)) (freeHopfModel C)
    (fun p : ℝ × FreeHopfProduct C ↦ freeHopfProductFlow C i p.1 p.2)
    ((equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ (freeHopfModel C) (FreeHopfProduct C)).symm
      (TotalSpace.mk' ℝ 0 (1 : ℝ), TotalSpace.mk' (FreeHopfModelSpace C) x 0))

/-- Actual smoothness of the flow tangent map gives the native smooth tangent lift. -/
theorem freeHopfGeneratorTangentLift_contMDiff (i : Fin a) :
    ContMDiff (freeHopfModel C) (freeHopfModel C).tangent ∞
      (freeHopfGeneratorTangentLift C i) := by
  exact ((freeHopfProductFlow_contMDiff C i).contMDiff_tangentMap (by simp)).comp
    (contMDiff_equivTangentBundleProd_symm.comp
      (contMDiff_const.prodMk (Bundle.contMDiff_zeroSection ℝ
        (TangentSpace (freeHopfModel C) : FreeHopfProduct C → Type _))))

/-- The actual tangent lift lies over its original product point. -/
theorem freeHopfGeneratorTangentLift_base (i : Fin a) (x : FreeHopfProduct C) :
    (freeHopfGeneratorTangentLift C i x).proj = x := freeHopfProductFlow_zero C i x

/-- The genuine native i-th Hopf tangent vector, with no supplied formal frame. -/
def freeHopfGenerator (i : Fin a) (x : FreeHopfProduct C) :
    TangentSpace (freeHopfModel C) x :=
  cast (congrArg (TangentSpace (freeHopfModel C))
    (freeHopfGeneratorTangentLift_base C i x)) (freeHopfGeneratorTangentLift C i x).2

/-- The actual section has exactly the tangent-map total-space value. -/
theorem freeHopfGenerator_totalSpace (i : Fin a) (x : FreeHopfProduct C) :
    TotalSpace.mk' (FreeHopfModelSpace C) x (freeHopfGenerator C i x) =
      freeHopfGeneratorTangentLift C i x :=
  TotalSpace.mk_cast (freeHopfGeneratorTangentLift_base C i x) _

/-- Each actual factor generator is a globally native smooth tangent section. -/
def freeHopfGeneratorSection (i : Fin a) :
    ContMDiffSection (freeHopfModel C) (FreeHopfModelSpace C) ∞
      (TangentSpace (freeHopfModel C) : FreeHopfProduct C → Type _) where
  toFun := freeHopfGenerator C i
  contMDiff_toFun := by
    simpa only [freeHopfGenerator_totalSpace] using
      freeHopfGeneratorTangentLift_contMDiff C i

/-- The actual tangent generator is the mfderiv of the genuine orbit at time zero. -/
theorem freeHopfGenerator_eq_orbit_mfderiv (i : Fin a) (x : FreeHopfProduct C) :
    freeHopfGenerator C i x =
      cast (congrArg (TangentSpace (freeHopfModel C)) (freeHopfProductFlow_zero C i x))
        (mfderiv 𝓘(ℝ, ℝ) (freeHopfModel C)
          (fun t : ℝ ↦ freeHopfProductFlow C i t x) 0 (1 : ℝ)) := by
  have h := mfderiv_comp (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, ℝ).prod (freeHopfModel C)) (I'' := freeHopfModel C)
    (f := fun t : ℝ ↦ (t, x))
    (g := fun p : ℝ × FreeHopfProduct C ↦ freeHopfProductFlow C i p.1 p.2) (x := 0)
    ((freeHopfProductFlow_contMDiff C i).mdifferentiableAt (by simp))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  rw [mfderiv_prod_left] at h
  unfold freeHopfGenerator
  congr 1
  change mfderiv (𝓘(ℝ, ℝ).prod (freeHopfModel C)) (freeHopfModel C)
    (fun p : ℝ × FreeHopfProduct C ↦ freeHopfProductFlow C i p.1 p.2) (0, x) (1, 0) = _
  exact (congrArg (fun L ↦ L (1 : ℝ)) h).symm

/-- Native differentiation along the actual field is exactly the literal Hopf partial. -/
theorem freeHopfGenerator_mvfderiv (i : Fin a)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : FreeHopfProduct C → F) (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ f)
    (x : FreeHopfProduct C) :
    mvfderiv (freeHopfModel C) f x (freeHopfGenerator C i x) = freeHopfDeriv C i f x := by
  have horbit : MDifferentiableAt 𝓘(ℝ, ℝ) (freeHopfModel C)
      (fun t : ℝ ↦ freeHopfProductFlow C i t x) 0 :=
    (((freeHopfProductFlow_contMDiff C i).comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp))
  have h := mvfderiv_comp (I := freeHopfModel C) (I' := 𝓘(ℝ, ℝ)) 0
    (hf.mdifferentiableAt (by simp)) horbit
  have he := congrArg (fun T : ℝ →L[ℝ] F ↦ T (1 : ℝ)) h
  rw [mvfderiv_eq_fderiv] at he
  change fderiv ℝ (fun t : ℝ ↦ f (freeHopfProductFlow C i t x)) 0 (1 : ℝ) =
    mvfderiv (freeHopfModel C) f (freeHopfProductFlow C i 0 x)
      (mfderiv 𝓘(ℝ, ℝ) (freeHopfModel C)
        (fun t : ℝ ↦ freeHopfProductFlow C i t x) 0 (1 : ℝ)) at he
  rw [freeHopfProductFlow_zero] at he
  rw [freeHopfGenerator_eq_orbit_mfderiv]
  exact he.symm

/-- Each actual ambient factor inclusion is native smooth. -/
theorem freeHopfProduct_contMDiff_ambient (j : Fin a) :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, PlanarHopfAmbient (C j)) ∞
      (fun x : FreeHopfProduct C ↦ (x j : PlanarHopfAmbient (C j))) :=
  (planarHopfSphere_contMDiff_coe (C j)).comp (freeHopfProduct_contMDiff_apply C j)

/-- Ambient factor projections detect the genuine 2π-normalized generator and all zeros. -/
theorem freeHopfGenerator_ambient (i j : Fin a) (x : FreeHopfProduct C) :
    mvfderiv (freeHopfModel C)
      (fun y : FreeHopfProduct C ↦ (y j : PlanarHopfAmbient (C j))) x
      (freeHopfGenerator C i x) =
        if j = i then ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) •
          (x j : PlanarHopfAmbient (C j))) else 0 := by
  rw [freeHopfGenerator_mvfderiv C i _ (freeHopfProduct_contMDiff_ambient C j)]
  unfold freeHopfDeriv orbitDeriv
  by_cases hji : j = i
  · subst j
    simp only [freeHopfProductFlow_apply, ite_true]
    exact (planarHopfOrbit_hasDerivAt (x i)).deriv
  · simp only [freeHopfProductFlow_apply_ne C i j hji, ite_eq_right hji, deriv_const]

/-- The true generators are pointwise independent, since each nonzero factor detects one.

Proof: apply the actual ambient derivative of the j-th factor projection to any zero
linear combination. All other actual generators have zero image; the j-th image is
2πi times its norm-one sphere vector and is nonzero. Thus each coefficient is zero.
This includes the empty frame. Source: setup:partial, lines216–232. -/
theorem freeHopfGenerator_independent (x : FreeHopfProduct C) :
    LinearIndependent ℝ (fun i ↦ freeHopfGenerator C i x) := by
  apply Fintype.linearIndependent_iff.2
  intro c hc j
  have hj := congrArg (fun v ↦ mvfderiv (freeHopfModel C)
    (fun y : FreeHopfProduct C ↦ (y j : PlanarHopfAmbient (C j))) x v) hc
  simp only [map_sum, map_smul, map_zero, freeHopfGenerator_ambient] at hj
  have he : c j • ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) •
      (x j : PlanarHopfAmbient (C j))) = 0 := by
    simpa [smul_ite] using hj
  have hs : ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) •
      (x j : PlanarHopfAmbient (C j))) ≠ 0 :=
    smul_ne_zero (mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero))
      Complex.I_ne_zero) (ne_zero_of_mem_unit_sphere (x j))
  exact (smul_eq_zero.mp he).resolve_right hs

/-- The actual native Hopf fields give the genuine framed tangent distribution. -/
def freeHopfFramedDistribution : FramedDistribution (freeHopfModel C)
    (M := FreeHopfProduct C) a where
  frame := freeHopfGeneratorSection C
  independent := freeHopfGenerator_independent C

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopfGenerator_mvfderiv
#print axioms GlobalEmbedding.Paper.freeHopfGenerator_ambient
#print axioms GlobalEmbedding.Paper.freeHopfGenerator_independent
#print axioms GlobalEmbedding.Paper.freeHopfFramedDistribution
