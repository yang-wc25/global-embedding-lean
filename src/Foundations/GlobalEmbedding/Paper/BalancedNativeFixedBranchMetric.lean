import GlobalEmbedding.Paper.BalancedActualFixedBranchPairings
import GlobalEmbedding.Paper.BalancedLiftMetricAlgebra
import GlobalEmbedding.Paper.BalancedQuadraticIdentities
import GlobalEmbedding.Paper.PrincipalTorusVerticalC2Bound

/-!
# Literal fixed branches give the original native balanced metric

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines403–418.
DAG node: `balanced-native-fixed-branch-metric`.
-/

open Set Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper
namespace PrincipalTorusBundle

/-- The actual fiber fixed branch yields the original native identity Gram.

Apply the actual-Qcal pairings theorem at every genuine fiber-lift point. The entire
native correction lift is epsilon times the actual little branch, so the proved genuine
fiber pushforward identifies its actual first derivatives. The proved canonical actual-Q
identity (4.2) and actual Qij index symmetry give exactly the quadratic
inputs of the accepted lift-only metric cancellation theorem. That theorem differentiates
only along the genuine fiber and derives commutation from actual Schwarz; no openness of
the fiber image or global scalar-Q extension is needed. The Fin1 scalar projection chain
rule reads the genuine whole-function quadratic identity in the exact real scalar form
needed by native metric cancellation. No desired quadratic identity is an extra premise. -/
theorem balanced_native_fixed_branch_metric
    {E H EB HB M B ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace B] [ChartedSpace HB B]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ EB HB}
    [IsManifold I ∞ M] [IsManifold J ∞ B]
    {a N : ℕ} {π : M → B} [AddAction (PeriodOneTorus a) M]
    (S : PrincipalTorusBundle (ι := ι) a I J π)
    (P U : M → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (i : ι) {b : B} (hb : b ∈ (S.trivialization i).baseSet)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ε : ℝ)
    (S3 S4 : M → Matrix (Fin a) (Fin a) ℝ)
    (C Ctilde : M → EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (v : LittlePeriodicCAlphaFunction a N 2 α)
    (hlift : ∀ y, U (S.fiberEuclideanLift i b y) = (ε • v).val.toFun y)
    (herror : ∀ y, balancedGeometry P hP S.verticalGeneratorSection
        (S.fiberEuclideanLift i b y) =
      1 + ε ^ 3 • S3 (S.fiberEuclideanLift i b y) +
        ε ^ 4 • S4 (S.fiberEuclideanLift i b y))
    (hC : ∀ y, IsBalancedPairingRightInverse P S.verticalGenerator
      (S.fiberEuclideanLift i b y) (C (S.fiberEuclideanLift i b y)))
    (hnormalized : ∀ y, Ctilde (S.fiberEuclideanLift i b y) =
      ε • C (S.fiberEuclideanLift i b y))
    (hv : ∀ y, v.val.toFun y =
      Ctilde (S.fiberEuclideanLift i b y)
          (balancedNormalizedResidualData ε
            (S3 (S.fiberEuclideanLift i b y)) (S4 (S.fiberEuclideanLift i b y))) +
      Ctilde (S.fiberEuclideanLift i b y) ((balancedPairingDataCoordinates a).symm
        ((balancedQuadraticDataOperator hα0 hα1 v v).val.toFun y))) :
    ∀ y, balancedGeometry (P + U) (hP.add hU) S.verticalGeneratorSection
      (S.fiberEuclideanLift i b y) = 1 := by
  let w := ε • v
  let W := littlePeriodicCAlphaShiftedLaplacianInverse (a := a) (N := 1) hα0 hα1
  let q := fun j z ↦ (balancedQuadraticFirst W hα1.le j w w).val.toFun z 0
  have hproj (f : LittlePeriodicCAlphaFunction a 1 2 α)
      (y u : EuclideanSpace ℝ (Fin a)) :
      fderiv ℝ (fun z ↦ f.val.toFun z 0) y u = (fderiv ℝ f.val.toFun y u) 0 := by
    let e : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 ↦ ℝ) 0
    have hf := (f.val.contDiff.differentiable (by norm_num)) y
    have hc := e.hasFDerivAt.comp y hf.hasFDerivAt
    exact congrArg (fun T : EuclideanSpace ℝ (Fin a) →L[ℝ] ℝ ↦ T u) hc.fderiv
  have hidentity : ∀ j k y,
      inner ℝ (fderiv ℝ (ε • v).val.toFun y (EuclideanSpace.single j 1))
          (fderiv ℝ (ε • v).val.toFun y (EuclideanSpace.single k 1)) =
        fderiv ℝ (fun z ↦ (balancedQuadraticFirst
          (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1) hα1.le k
            (ε • v) (ε • v)).val.toFun z 0) y (EuclideanSpace.single j 1) +
        fderiv ℝ (fun z ↦ (balancedQuadraticFirst
          (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1) hα1.le j
            (ε • v) (ε • v)).val.toFun z 0) y (EuclideanSpace.single k 1) +
        (balancedQuadraticSecond (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
          hα1.le j k (ε • v) (ε • v)).val.toFun y 0 := by
    intro j k y
    rw [hproj, hproj]
    have hvect := balancedQuadraticIdentity_value hα0 hα1 j k w y
    exact (congrArg (fun z : EuclideanSpace ℝ (Fin 1) ↦ z 0) hvect).symm
  have he : U ∘ S.fiberEuclideanLift i b = w.val.toFun := funext hlift
  have hpair (y : EuclideanSpace ℝ (Fin a)) :=
    balanced_actual_fixed_branch_pairings hα0 hα1 P S.verticalGenerator
      (S.fiberEuclideanLift i b y) (C (S.fiberEuclideanLift i b y))
      (Ctilde (S.fiberEuclideanLift i b y)) (hC y) ε (hnormalized y)
      (S3 (S.fiberEuclideanLift i b y)) (S4 (S.fiberEuclideanLift i b y)) v y (hv y)
  intro y
  let r := fun j k ↦ (balancedQuadraticSecond W hα1.le j k w w).val.toFun y 0
  let h := ε ^ 3 • S3 (S.fiberEuclideanLift i b y) +
    ε ^ 4 • S4 (S.fiberEuclideanLift i b y)
  apply balanced_metric_eq_one_of_lift_pairings P U hP hU S.verticalGeneratorSection
    (S.fiberEuclideanLift i b) univ isOpen_univ
    (S.contMDiff_fiberEuclideanLift i hb).contMDiffOn y (mem_univ y)
    (fun j ↦ EuclideanSpace.single j 1)
    (fun z _ j ↦ S.verticalGenerator_eq_fiberEuclideanLift_mfderiv i hb z j) q r h
  · simpa only [h, add_assoc] using herror y
  · intro j
    apply Filter.Eventually.of_forall
    intro z
    change inner ℝ (balancedDirectionalDerivative P (S.verticalGenerator j)
      (S.fiberEuclideanLift i b z)) (U (S.fiberEuclideanLift i b z)) = -q j z
    rw [hlift]
    exact (hpair z).1 j
  · intro j k hjk
    change 2 * inner ℝ (balancedDirectionalDerivative
        (balancedDirectionalDerivative P (S.verticalGenerator k)) (S.verticalGenerator j)
        (S.fiberEuclideanLift i b y)) (U (S.fiberEuclideanLift i b y)) =
      ε ^ 3 * S3 (S.fiberEuclideanLift i b y) j k +
        ε ^ 4 * S4 (S.fiberEuclideanLift i b y) j k + r j k
    rw [hlift]
    exact (hpair y).2 ⟨(j, k), hjk⟩
  · intro j k
    exact congrArg (fun f : LittlePeriodicCAlphaFunction a 1 2 α ↦ f.val.toFun y 0)
      (balancedQuadraticSecond_index_symmetric W hα1.le j k w w)
  · intro j k
    change inner ℝ (balancedDirectionalDerivative U (S.verticalGenerator j)
        (S.fiberEuclideanLift i b y))
        (balancedDirectionalDerivative U (S.verticalGenerator k)
          (S.fiberEuclideanLift i b y)) = _
    rw [S.vertical_first_fiberEuclideanLift U hU i hb y j,
      S.vertical_first_fiberEuclideanLift U hU i hb y k, he]
    exact hidentity j k y

end PrincipalTorusBundle
end GlobalEmbedding.Paper
