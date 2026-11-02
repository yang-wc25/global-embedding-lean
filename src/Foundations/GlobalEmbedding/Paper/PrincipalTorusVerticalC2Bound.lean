import GlobalEmbedding.Paper.PrincipalTorusLiftDerivatives
import GlobalEmbedding.Paper.PrincipalTorusVerticalNorm
import GlobalEmbedding.Paper.BalancedPairingLiftPullback
import GlobalEmbedding.Paper.BalancedVerticalC2Size

/-!
# Actual principal-torus vertical derivatives and the original C² estimate

Source: `main.tex`, `lem:balanced`, lines371–418. This applies W3's genuine local lift
chain rule and Schwarz theorem to W5's actual inverse-chart pushforward. The original
little Hölder norm controls the actual native derivatives and W6's canonical C² sum.
-/

noncomputable section
open Set WithLp IsManifold
open scoped Manifold ContDiff
namespace GlobalEmbedding.Paper
local instance principalTorusVerticalC2ChartedSpace (a : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) :=
  periodicFlatTorusChartedSpace a
local instance principalTorusVerticalC2IsManifold (a : ℕ) :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞ (PeriodOneTorus a) :=
  periodic_flat_torus_isManifold a ∞

variable {E H EB HB M B ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace HB B]
namespace PrincipalTorusBundle
variable {a N : ℕ} {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ EB HB}
  {π : M → B} [IsManifold I ∞ M] [IsManifold J ∞ B]
  [AddAction (PeriodOneTorus a) M]
  (S : PrincipalTorusBundle (ι := ι) a I J π)
include S

/-- Actual first derivatives in the actual inverse-chart lift are coordinate derivatives. -/
theorem vertical_first_fiberEuclideanLift
    (U : M → EuclideanSpace ℝ (Fin N))
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (i : ι) {b : B} (hb : b ∈ (S.trivialization i).baseSet)
    (y : EuclideanSpace ℝ (Fin a)) (j : Fin a) :
    balancedDirectionalDerivative U (S.verticalGenerator j) (S.fiberEuclideanLift i b y) =
      fderiv ℝ (U ∘ S.fiberEuclideanLift i b) y (EuclideanSpace.single j (1 : ℝ)) :=
  balanced_directional_lift_pullback_at U (S.verticalGenerator j)
    (S.fiberEuclideanLift i b) y (EuclideanSpace.single j (1 : ℝ))
    (hU.mdifferentiableAt (by simp))
    ((S.contMDiff_fiberEuclideanLift i hb).mdifferentiableAt (by simp))
    (S.verticalGenerator_eq_fiberEuclideanLift_mfderiv i hb y j)

/-- Actual ordered second derivatives are the coordinate second derivatives of the true lift. -/
theorem vertical_second_fiberEuclideanLift
    (U : M → EuclideanSpace ℝ (Fin N))
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (i : ι) {b : B} (hb : b ∈ (S.trivialization i).baseSet)
    (y : EuclideanSpace ℝ (Fin a)) (j k : Fin a) :
    balancedDirectionalDerivative (balancedDirectionalDerivative U (S.verticalGenerator k))
      (S.verticalGenerator j) (S.fiberEuclideanLift i b y) =
      fderiv ℝ (fun z ↦ fderiv ℝ (U ∘ S.fiberEuclideanLift i b) z
        (EuclideanSpace.single k (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ)) :=
  balanced_second_directional_lift_pullback_at U hU
    (S.verticalGeneratorSection j) (S.verticalGeneratorSection k)
    (S.fiberEuclideanLift i b) univ isOpen_univ
    (S.contMDiff_fiberEuclideanLift i hb).contMDiffOn y (mem_univ y)
    (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single k (1 : ℝ))
    (fun z _ ↦ S.verticalGenerator_eq_fiberEuclideanLift_mfderiv i hb z j)
    (fun z _ ↦ S.verticalGenerator_eq_fiberEuclideanLift_mfderiv i hb z k)

/-- The actual native generators commute on every actual smooth Euclidean-valued function.
This is derived from the true local lifts, with no commutation added to the bundle data. -/
theorem vertical_directional_commute
    (U : M → EuclideanSpace ℝ (Fin N))
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (j k : Fin a) (x : M) :
    balancedDirectionalDerivative (balancedDirectionalDerivative U (S.verticalGenerator k))
      (S.verticalGenerator j) x =
    balancedDirectionalDerivative (balancedDirectionalDerivative U (S.verticalGenerator j))
      (S.verticalGenerator k) x := by
  obtain ⟨i, hi⟩ := S.exists_mem_source x
  have hb := (S.trivialization i).mem_source.mp hi
  obtain ⟨y, hy⟩ := S.exists_fiberEuclideanLift i hi
  have hc := balanced_directional_commute_of_lift U hU
    (S.verticalGeneratorSection j) (S.verticalGeneratorSection k)
    (S.fiberEuclideanLift i (π x)) univ isOpen_univ
    (S.contMDiff_fiberEuclideanLift i hb).contMDiffOn y (mem_univ y)
    (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single k (1 : ℝ))
    (fun z _ ↦ S.verticalGenerator_eq_fiberEuclideanLift_mfderiv i hb z j)
    (fun z _ ↦ S.verticalGenerator_eq_fiberEuclideanLift_mfderiv i hb z k)
  change balancedDirectionalDerivative (balancedDirectionalDerivative U (S.verticalGenerator k))
      (S.verticalGenerator j) (S.fiberEuclideanLift i (π x) y) =
    balancedDirectionalDerivative (balancedDirectionalDerivative U (S.verticalGenerator j))
      (S.verticalGenerator k) (S.fiberEuclideanLift i (π x) y) at hc
  simpa only [hy] using hc

/-- The original little Hölder norm bounds the canonical actual vertical C² finite sum.
The only identification input says f is the actual lift of U in this native chart. -/
theorem verticalC2Size_le_little_norm {α : ℝ}
    (U : M → EuclideanSpace ℝ (Fin N))
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (i : ι) {b : B} (hb : b ∈ (S.trivialization i).baseSet)
    (f : LittlePeriodicCAlphaFunction a N 2 α)
    (hlift : ∀ y, U (S.fiberEuclideanLift i b y) = f.val.toFun y)
    (y : EuclideanSpace ℝ (Fin a)) :
    balancedVerticalC2Size S.verticalGenerator U (S.fiberEuclideanLift i b y) ≤
      (1 + (a : ℝ) + (a : ℝ) ^ 2) * ‖f‖ := by
  have he : U ∘ S.fiberEuclideanLift i b = f.val.toFun := funext hlift
  apply balancedVerticalC2Size_le_of_components _ _ _ ‖f‖
  · rw [hlift]
    exact littlePeriodicCAlpha_value_norm_le f y
  · intro j
    rw [S.vertical_first_fiberEuclideanLift U hU i hb y j, he]
    exact littlePeriodicCAlpha_first_coordinate_norm_le f y j
  · intro j k
    rw [S.vertical_second_fiberEuclideanLift U hU i hb y j k, he]
    exact littlePeriodicCAlpha_second_coordinate_norm_le f y j k

#print axioms vertical_first_fiberEuclideanLift
#print axioms vertical_second_fiberEuclideanLift
#print axioms vertical_directional_commute
#print axioms verticalC2Size_le_little_norm
end PrincipalTorusBundle
end GlobalEmbedding.Paper
