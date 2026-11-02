import GlobalEmbedding.Paper.FreeHopfOrbitLift
import GlobalEmbedding.Paper.BalancedActualFixedBranchPairings
import GlobalEmbedding.Paper.BalancedLiftMetricAlgebra
import GlobalEmbedding.Paper.BalancedQuadraticIdentities

/-!
# The actual whole-function Hopf branch gives the native identity Gram

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines403–418 and477–495.
DAG node: `free-hopf-fixed-branch-metric`.
-/

noncomputable section

open Set Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The genuine canonical fixed branch on an actual Hopf orbit has exact native Gram.

Proof: apply the accepted whole-function fixed-branch pairings at every true orbit point.
The genuine Hopf orbit lift and its actual generator pushforward identify first and second
native derivatives. The accepted actual canonical quadratic identity, followed by the true
scalar-coordinate derivative rule, supplies the exact quadratic cancellation. The accepted
native lift metric theorem then gives identity Gram. The only lift/source equations here
are those constructed by the orbit-correction parent from actual original input data;
neither a desired Gram identity nor principal CP-bundle geometry is assumed.
Source: lem:balanced, lines403–418. -/
theorem freeHopf_fixed_branch_metric {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (P U : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (hU : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (x : FreeHopfProduct C) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ε : ℝ)
    (S3 S4 : FreeHopfProduct C → Matrix (Fin a) (Fin a) ℝ)
    (A Atilde : FreeHopfProduct C → EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (v : LittlePeriodicCAlphaFunction a N 2 α)
    (hlift : ∀ y, U (freeHopfOrbitLift C x y) = (ε • v).val.toFun y)
    (herror : ∀ y, balancedGeometry P hP (freeHopfGeneratorSection C)
        (freeHopfOrbitLift C x y) =
      1 + ε ^ 3 • S3 (freeHopfOrbitLift C x y) + ε ^ 4 • S4 (freeHopfOrbitLift C x y))
    (hA : ∀ y, IsBalancedPairingRightInverse P (freeHopfGenerator C)
      (freeHopfOrbitLift C x y) (A (freeHopfOrbitLift C x y)))
    (hnormalized : ∀ y, Atilde (freeHopfOrbitLift C x y) =
      ε • A (freeHopfOrbitLift C x y))
    (hv : ∀ y, v.val.toFun y = Atilde (freeHopfOrbitLift C x y)
        (balancedNormalizedResidualData ε
          (S3 (freeHopfOrbitLift C x y)) (S4 (freeHopfOrbitLift C x y))) +
      Atilde (freeHopfOrbitLift C x y) ((balancedPairingDataCoordinates a).symm
        ((balancedQuadraticDataOperator hα0 hα1 v v).val.toFun y))) :
    ∀ y, balancedGeometry (P + U) (hP.add hU) (freeHopfGeneratorSection C)
      (freeHopfOrbitLift C x y) = 1 := by
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
    exact (congrArg (fun z : EuclideanSpace ℝ (Fin 1) ↦ z 0)
      (balancedQuadraticIdentity_value hα0 hα1 j k w y)).symm
  have he : U ∘ freeHopfOrbitLift C x = w.val.toFun := funext hlift
  have hpair (y : EuclideanSpace ℝ (Fin a)) :=
    balanced_actual_fixed_branch_pairings hα0 hα1 P (freeHopfGenerator C)
      (freeHopfOrbitLift C x y) (A (freeHopfOrbitLift C x y))
      (Atilde (freeHopfOrbitLift C x y)) (hA y) ε (hnormalized y)
      (S3 (freeHopfOrbitLift C x y)) (S4 (freeHopfOrbitLift C x y)) v y (hv y)
  intro y
  let r := fun j k ↦ (balancedQuadraticSecond W hα1.le j k w w).val.toFun y 0
  let h := ε ^ 3 • S3 (freeHopfOrbitLift C x y) + ε ^ 4 • S4 (freeHopfOrbitLift C x y)
  apply balanced_metric_eq_one_of_lift_pairings P U hP hU (freeHopfGeneratorSection C)
    (freeHopfOrbitLift C x) univ isOpen_univ
    (freeHopfOrbitLift_contMDiff C x).contMDiffOn y (mem_univ y)
    (fun j ↦ EuclideanSpace.single j 1)
    (fun z _ j ↦ freeHopfGenerator_eq_orbitLift_mfderiv C x z j) q r h
  · simpa only [h, add_assoc] using herror y
  · intro j
    apply Filter.Eventually.of_forall
    intro z
    change inner ℝ (balancedDirectionalDerivative P (freeHopfGenerator C j)
      (freeHopfOrbitLift C x z)) (U (freeHopfOrbitLift C x z)) = -q j z
    rw [hlift]
    exact (hpair z).1 j
  · intro j k hjk
    change 2 * inner ℝ (balancedDirectionalDerivative
      (balancedDirectionalDerivative P (freeHopfGenerator C k)) (freeHopfGenerator C j)
      (freeHopfOrbitLift C x y)) (U (freeHopfOrbitLift C x y)) =
      ε ^ 3 * S3 (freeHopfOrbitLift C x y) j k +
        ε ^ 4 * S4 (freeHopfOrbitLift C x y) j k + r j k
    rw [hlift]
    exact (hpair y).2 ⟨(j, k), hjk⟩
  · intro j k
    exact congrArg (fun f : LittlePeriodicCAlphaFunction a 1 2 α ↦ f.val.toFun y 0)
      (balancedQuadraticSecond_index_symmetric W hα1.le j k w w)
  · intro j k
    change inner ℝ (balancedDirectionalDerivative U (freeHopfGenerator C j)
        (freeHopfOrbitLift C x y))
        (balancedDirectionalDerivative U (freeHopfGenerator C k)
          (freeHopfOrbitLift C x y)) = _
    rw [freeHopf_first_orbitLift C U hU x y j, freeHopf_first_orbitLift C U hU x y k, he]
    exact hidentity j k y

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopf_fixed_branch_metric
