import GlobalEmbedding.Paper.PrincipalTorusBundle
import GlobalEmbedding.Paper.PeriodicFlatTorusProjectionSmooth
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Actual fundamental vertical sections of a period-one principal torus bundle

Source: `main.tex`, `lem:balanced`, lines371–418. The native tangent map of the actual
coordinate orbit gives the section. No commuting derivation or vector field is supplied
as additional bundle data. The proved quotient atlas and genuine native action are reused.
-/

noncomputable section
open Set WithLp IsManifold
open Bundle (TotalSpace)
open scoped Manifold ContDiff
namespace GlobalEmbedding.Paper

local instance (a : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) :=
  periodicFlatTorusChartedSpace a
local instance (a : ℕ) : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞ (PeriodOneTorus a) :=
  periodic_flat_torus_isManifold a ∞

/-- The actual period-one quotient of the i-th real coordinate line. -/
def periodOneCoordinateOrbit {a : ℕ} (i : Fin a) (t : ℝ) : PeriodOneTorus a :=
  toLp 2 (fun j ↦ ((t • EuclideanSpace.single i (1 : ℝ)) j : AddCircle (1 : ℝ)))

theorem contMDiff_periodOneCoordinateOrbit {a : ℕ} (i : Fin a) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞ (periodOneCoordinateOrbit i) := by
  exact (periodic_flat_torus_projection_contMDiff a ∞).comp
    (contMDiff_id.smul contMDiff_const)

@[simp] theorem periodOneCoordinateOrbit_zero {a : ℕ} (i : Fin a) :
    periodOneCoordinateOrbit i 0 = 0 := by
  simp [periodOneCoordinateOrbit, Pi.zero_def]

theorem periodOneCoordinateOrbit_add {a : ℕ} (i : Fin a) (s t : ℝ) :
    periodOneCoordinateOrbit i (s + t) =
      periodOneCoordinateOrbit i s + periodOneCoordinateOrbit i t := by
  apply PiLp.ext
  intro j
  simp [periodOneCoordinateOrbit, add_smul]

@[simp] theorem periodOneCoordinateOrbit_one {a : ℕ} (i : Fin a) :
    periodOneCoordinateOrbit i 1 = 0 := by
  apply PiLp.ext
  intro j
  by_cases h : i = j
  · subst j
    simp [periodOneCoordinateOrbit, AddCircle.coe_period]
  · simp [periodOneCoordinateOrbit, Ne.symm h]

/-- The time parameter has the original period one, including the zero-dimensional case. -/
theorem periodOneCoordinateOrbit_periodic {a : ℕ} (i : Fin a) :
    Function.Periodic (periodOneCoordinateOrbit i) 1 := by
  intro t
  rw [periodOneCoordinateOrbit_add, periodOneCoordinateOrbit_one, add_zero]

variable {E H EB HB M B ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace HB B]

namespace PrincipalTorusBundle
variable {a : ℕ} {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ EB HB}
  {π : M → B} [IsManifold I ∞ M] [IsManifold J ∞ B]
  [AddAction (PeriodOneTorus a) M]
  (S : PrincipalTorusBundle (ι := ι) a I J π)

include S

/-- The genuine orbit map, with time and starting point as joint variables. -/
def coordinateFlow (_S : PrincipalTorusBundle (ι := ι) a I J π) (i : Fin a) (p : ℝ × M) : M :=
  periodOneCoordinateOrbit i p.1 +ᵥ p.2

theorem contMDiff_coordinateFlow (i : Fin a) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (S.coordinateFlow i) := by
  have := S.smooth_action
  exact contMDiff_vadd.comp
    (((contMDiff_periodOneCoordinateOrbit i).comp contMDiff_fst).prodMk contMDiff_snd)

@[simp] theorem coordinateFlow_zero (i : Fin a) (x : M) :
    S.coordinateFlow i (0, x) = x := by
  simp [coordinateFlow]

theorem coordinateFlow_add (i : Fin a) (s t : ℝ) (x : M) :
    S.coordinateFlow i (s + t, x) =
      S.coordinateFlow i (s, S.coordinateFlow i (t, x)) := by
  simp only [coordinateFlow, periodOneCoordinateOrbit_add, add_vadd]

/-- The genuine coordinate flows commute because they belong to the same torus action. -/
theorem coordinateFlow_comm (i j : Fin a) (s t : ℝ) (x : M) :
    S.coordinateFlow i (s, S.coordinateFlow j (t, x)) =
      S.coordinateFlow j (t, S.coordinateFlow i (s, x)) := by
  simp only [coordinateFlow, ← add_vadd, add_comm]

theorem coordinateFlow_periodic (i : Fin a) (x : M) :
    Function.Periodic (fun t : ℝ ↦ S.coordinateFlow i (t, x)) 1 := by
  intro t
  exact congrArg (fun q ↦ q +ᵥ x) (periodOneCoordinateOrbit_periodic i t)

/-- Tangent lift of the actual time-unit vector at (0,x), a genuine smooth total-space map. -/
def coordinateTangentLift (i : Fin a) (x : M) : TangentBundle I M :=
  tangentMap (𝓘(ℝ, ℝ).prod I) I (S.coordinateFlow i)
    ((equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ I M).symm
      (TotalSpace.mk' ℝ 0 (1 : ℝ), TotalSpace.mk' E x 0))

theorem contMDiff_coordinateTangentLift (i : Fin a) :
    ContMDiff I I.tangent ∞ (S.coordinateTangentLift i) := by
  exact ((S.contMDiff_coordinateFlow i).contMDiff_tangentMap (by simp)).comp
    (contMDiff_equivTangentBundleProd_symm.comp
      (contMDiff_const.prodMk (Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _))))

theorem coordinateTangentLift_base (i : Fin a) (x : M) :
    (S.coordinateTangentLift i x).proj = x := by
  change S.coordinateFlow i (0, x) = x
  exact S.coordinateFlow_zero i x

/-- The actual fundamental tangent vector; transport only uses the genuine base identity. -/
def verticalGenerator (i : Fin a) (x : M) : TangentSpace I x :=
  cast (congrArg (TangentSpace I) (S.coordinateTangentLift_base i x))
    (S.coordinateTangentLift i x).2

theorem verticalGenerator_totalSpace (i : Fin a) (x : M) :
    TotalSpace.mk' E x (S.verticalGenerator i x) = S.coordinateTangentLift i x :=
  TotalSpace.mk_cast (S.coordinateTangentLift_base i x) _

theorem contMDiff_verticalGenerator (i : Fin a) :
    ContMDiff I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (S.verticalGenerator i x)) := by
  simpa only [S.verticalGenerator_totalSpace i] using S.contMDiff_coordinateTangentLift i

/-- The native smooth section with exactly the actual fundamental vector values. -/
def verticalGeneratorSection (i : Fin a) : ContMDiffSection I E ∞ (fun x : M ↦ TangentSpace I x) where
  toFun := S.verticalGenerator i
  contMDiff_toFun := S.contMDiff_verticalGenerator i

@[simp] theorem verticalGeneratorSection_apply (i : Fin a) (x : M) :
    S.verticalGeneratorSection i x = S.verticalGenerator i x := rfl

/-- Identification with the actual derivative of the coordinate orbit curve at zero. -/
theorem verticalGenerator_eq_orbit_mfderiv (i : Fin a) (x : M) :
    S.verticalGenerator i x =
      cast (congrArg (TangentSpace I) (S.coordinateFlow_zero i x))
        (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ ↦ S.coordinateFlow i (t, x)) 0 (1 : ℝ)) := by
  have h := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ).prod I) (I'' := I)
    (f := fun t : ℝ ↦ (t, x)) (g := S.coordinateFlow i) (x := 0)
    ((S.contMDiff_coordinateFlow i).mdifferentiableAt (by simp))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  rw [mfderiv_prod_left] at h
  unfold verticalGenerator
  congr 1
  change mfderiv (𝓘(ℝ, ℝ).prod I) I (S.coordinateFlow i) (0, x) (1, 0) = _
  exact (congrArg (fun L ↦ L (1 : ℝ)) h).symm

#print axioms coordinateFlow_comm
#print axioms verticalGenerator_eq_orbit_mfderiv
#print axioms periodOneCoordinateOrbit_periodic
#print axioms contMDiff_coordinateFlow
#print axioms contMDiff_coordinateTangentLift
#print axioms contMDiff_verticalGenerator
#print axioms verticalGeneratorSection_apply
end PrincipalTorusBundle
end GlobalEmbedding.Paper
