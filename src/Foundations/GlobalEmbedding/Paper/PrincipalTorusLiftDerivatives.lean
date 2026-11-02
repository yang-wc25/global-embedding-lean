import GlobalEmbedding.Paper.PrincipalTorusVerticalCalculus
import GlobalEmbedding.Paper.PrincipalTorusOverlap
import GlobalEmbedding.Paper.BalancedDirectionalCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Actual coordinate-lift differentials of principal torus bundles

Source: `main.tex`, `lem:balanced`, lines371–418. Only native actual orbit and
inverse-chart identities are used; the vector fields are not extra source hypotheses.
-/

noncomputable section
open Set WithLp IsManifold
open scoped Manifold ContDiff
namespace GlobalEmbedding.Paper
local instance principalTorusLiftDerivativesChartedSpace (a : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) :=
  periodicFlatTorusChartedSpace a
local instance principalTorusLiftDerivativesIsManifold (a : ℕ) : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞ (PeriodOneTorus a) :=
  periodic_flat_torus_isManifold a ∞

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

/-- An actual equivariant lift pushes the coordinate direction to the actual fundamental field. -/
theorem verticalGenerator_eq_lift_mfderiv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : V → M) (hφ : ContMDiff 𝓘(ℝ, V) I ∞ φ) (i : Fin a) (y v : V)
    (hcurve : ∀ t : ℝ, φ (y + t • v) = S.coordinateFlow i (t, φ y)) :
    S.verticalGenerator i (φ y) =
      mfderiv 𝓘(ℝ, V) I φ y ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v) := by
  have hline : ContDiff ℝ ∞ (fun t : ℝ ↦ y + t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hzero : y + (0 : ℝ) • v = y := by simp
  have hc := mfderiv_comp_of_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, V)) (I'' := I)
    (f := fun t : ℝ ↦ y + t • v) (g := φ) (x := 0)
    (hφ.mdifferentiableAt (by simp)) ((hline.differentiable (by simp)).differentiableAt.mdifferentiableAt) hzero
  have hd0 : HasFDerivAt (fun t : ℝ ↦ y + t • v)
      (ContinuousLinearMap.toSpanSingleton ℝ v) 0 :=
    (ContinuousLinearMap.toSpanSingleton ℝ v).hasFDerivAt.const_add y
  have hd : fderiv ℝ (fun t : ℝ ↦ y + t • v) 0 (1 : ℝ) = v := by
    rw [hd0.fderiv]
    simp
  have he : (fun t : ℝ ↦ φ (y + t • v)) =
      (fun t : ℝ ↦ S.coordinateFlow i (t, φ y)) := funext hcurve
  rw [S.verticalGenerator_eq_orbit_mfderiv]
  change mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ ↦ S.coordinateFlow i (t, φ y)) 0 (1 : ℝ) = _
  rw [← he]
  have hc' := congrArg (fun L ↦ L (1 : ℝ)) hc
  rw [mfderiv_eq_fderiv] at hc'
  change mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ ↦ φ (y + t • v)) 0 (1 : ℝ) =
    mfderiv 𝓘(ℝ, V) I φ (y + (0 : ℝ) • v)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (y + (0 : ℝ) • v)).symm
        (fderiv ℝ (fun t : ℝ ↦ y + t • v) 0 (1 : ℝ))) at hc'
  rw [hd] at hc'
  have hzv := congrArg (fun z : V ↦ (show E from
    mfderiv 𝓘(ℝ, V) I φ z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v))) hzero
  exact hc'.trans hzv


/-- The actual native inverse chart composed with the original Euclidean quotient. -/
def fiberEuclideanLift (i : ι) (b : B) (y : EuclideanSpace ℝ (Fin a)) : M :=
  S.fiberChartPoint i b (toLp 2 (fun j ↦ (y j : AddCircle (1 : ℝ))))

theorem contMDiff_fiberEuclideanLift (i : ι) {b : B}
    (hb : b ∈ (S.trivialization i).baseSet) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) I ∞ (S.fiberEuclideanLift i b) := by
  exact (S.smooth_inverse i).comp_contMDiff
    (contMDiff_const.prodMk (periodic_flat_torus_projection_contMDiff a ∞))
    (fun y ↦ (S.trivialization i).mem_target.mpr hb)

/-- The coordinate line in the genuine lift is exactly the actual period-one action orbit. -/
theorem fiberEuclideanLift_coordinate_line (i : ι) {b : B}
    (hb : b ∈ (S.trivialization i).baseSet) (y : EuclideanSpace ℝ (Fin a))
    (j : Fin a) (t : ℝ) :
    S.fiberEuclideanLift i b (y + t • EuclideanSpace.single j (1 : ℝ)) =
      S.coordinateFlow j (t, S.fiberEuclideanLift i b y) := by
  have hq :
      toLp 2 (fun k ↦ ((y + t • EuclideanSpace.single j (1 : ℝ)) k : AddCircle (1 : ℝ))) =
        toLp 2 (fun k ↦ (y k : AddCircle (1 : ℝ))) + periodOneCoordinateOrbit j t := by
    apply PiLp.ext
    intro k
    simp [periodOneCoordinateOrbit]
  change S.fiberChartPoint i b _ = periodOneCoordinateOrbit j t +ᵥ S.fiberChartPoint i b _
  rw [hq, S.action_fiberChartPoint i hb]

/-- The real local lift sends each unit coordinate vector to the actual fundamental vector.
This is the exact hD interface consumed by the already proved generic Gram pullback. -/
theorem verticalGenerator_eq_fiberEuclideanLift_mfderiv (i : ι) {b : B}
    (hb : b ∈ (S.trivialization i).baseSet) (y : EuclideanSpace ℝ (Fin a)) (j : Fin a) :
    S.verticalGenerator j (S.fiberEuclideanLift i b y) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) I (S.fiberEuclideanLift i b) y
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm
          (EuclideanSpace.single j (1 : ℝ))) :=
  S.verticalGenerator_eq_lift_mfderiv _ (S.contMDiff_fiberEuclideanLift i hb) j y _
    (S.fiberEuclideanLift_coordinate_line i hb y j)

/-- Every point in a genuine bundle chart has an actual Euclidean lift in that chart. -/
theorem exists_fiberEuclideanLift (i : ι) {x : M}
    (hx : x ∈ (S.trivialization i).source) :
    ∃ y : EuclideanSpace ℝ (Fin a), S.fiberEuclideanLift i (π x) y = x := by
  obtain ⟨y, hy⟩ := periodic_flat_torus_projection.surjective (S.trivialization i x).2
  refine ⟨y, ?_⟩
  have he : (π x, toLp 2 (fun k ↦ (y k : AddCircle (1 : ℝ)))) = S.trivialization i x :=
    Prod.ext ((S.trivialization i).coe_fst hx).symm hy
  change (S.trivialization i).toOpenPartialHomeomorph.symm _ = x
  rw [he]
  exact (S.trivialization i).toOpenPartialHomeomorph.left_inv hx

#print axioms exists_fiberEuclideanLift
#print axioms verticalGenerator_eq_fiberEuclideanLift_mfderiv
#print axioms contMDiff_fiberEuclideanLift
#print axioms verticalGenerator_eq_lift_mfderiv
end PrincipalTorusBundle
end GlobalEmbedding.Paper
