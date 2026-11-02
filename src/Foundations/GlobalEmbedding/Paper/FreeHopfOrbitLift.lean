import GlobalEmbedding.Paper.FreeHopfProductGenerators
import GlobalEmbedding.Paper.BalancedPairingLiftPullback
import GlobalEmbedding.Paper.BalancedVerticalC2Size
import GlobalEmbedding.Paper.PrincipalTorusVerticalNorm

/-!
# The genuine multi-orbit lift and native vertical jet bounds

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines371–418 and477–495.
DAG node: `free-hopf-orbit-lift`.
-/

noncomputable section

open Set WithLp Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The true Euclidean multi-orbit through an actual sphere-product point. -/
def freeHopfOrbitLift {a : ℕ} (C : Fin a → ℕ) (x : FreeHopfProduct C)
    (y : EuclideanSpace ℝ (Fin a)) : FreeHopfProduct C :=
  freeHopfRealAction C (fun i ↦ y i) x

@[simp] theorem freeHopfOrbitLift_zero {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) : freeHopfOrbitLift C x 0 = x := by
  funext i
  exact planarHopfFlow_zero (x i)

/-- Actual joint real action smoothness gives genuine smoothness of every orbit lift. -/
theorem freeHopfOrbitLift_contMDiff {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (x : FreeHopfProduct C) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) (freeHopfModel C) ∞
      (freeHopfOrbitLift C x) := by
  have hc : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) 𝓘(ℝ, Fin a → ℝ) ∞
      (fun y : EuclideanSpace ℝ (Fin a) ↦ fun i ↦ y i) :=
    contMDiff_pi_module_iff.2 (fun i ↦
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin a) i).contMDiff)
  exact (freeHopfRealAction_contMDiff C).comp (hc.prodMk contMDiff_const)

/-- The actual coordinate line in the multi-orbit is precisely the literal factor flow. -/
theorem freeHopfOrbitLift_coordinate_line {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) (i : Fin a) (t : ℝ) :
    freeHopfOrbitLift C x (y + t • EuclideanSpace.single i 1) =
      freeHopfProductFlow C i t (freeHopfOrbitLift C x y) := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [freeHopfProductFlow_apply]
    change planarHopfFlow ((y + t • EuclideanSpace.single i 1 :
      EuclideanSpace ℝ (Fin a)) i) (x i) =
      planarHopfFlow t (planarHopfFlow (y i) (x i))
    rw [← planarHopfFlow_add]
    congr 1
    simp [EuclideanSpace.single, add_comm]
  · rw [freeHopfProductFlow_apply_ne C i j hji]
    change planarHopfFlow ((y + t • EuclideanSpace.single i 1 :
      EuclideanSpace ℝ (Fin a)) j) (x j) =
      planarHopfFlow (y j) (x j)
    congr 1
    simp [EuclideanSpace.single, hji]

/-- The genuine multi-orbit differential sends each real unit direction to its true field.

Proof: differentiate the actual affine coordinate line and compose its genuine mfderiv
with the actual orbit lift. The proved coordinate-line identity identifies the curve with
the original factor flow, whose time-unit mfderiv is the constructed native generator.
No principal Hopf quotient, assumed pushforward or formal vector field is used.
Source: actual vertical differentiation in lem:balanced, lines413–418. -/
theorem freeHopfGenerator_eq_orbitLift_mfderiv {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (x : FreeHopfProduct C)
    (y : EuclideanSpace ℝ (Fin a)) (i : Fin a) :
    freeHopfGenerator C i (freeHopfOrbitLift C x y) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) (freeHopfModel C)
        (freeHopfOrbitLift C x) y
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (EuclideanSpace.single i 1)) := by
  let v := EuclideanSpace.single i (1 : ℝ)
  have hline : ContDiff ℝ ∞ (fun t : ℝ ↦ y + t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hzero : y + (0 : ℝ) • v = y := by simp
  have hc := mfderiv_comp_of_eq (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) (I'' := freeHopfModel C)
    (f := fun t : ℝ ↦ y + t • v) (g := freeHopfOrbitLift C x) (x := 0)
    ((freeHopfOrbitLift_contMDiff C x).mdifferentiableAt (by simp))
    ((hline.differentiable (by simp)).differentiableAt.mdifferentiableAt) hzero
  have hd0 : HasFDerivAt (fun t : ℝ ↦ y + t • v)
      (ContinuousLinearMap.toSpanSingleton ℝ v) 0 :=
    (ContinuousLinearMap.toSpanSingleton ℝ v).hasFDerivAt.const_add y
  have hd : fderiv ℝ (fun t : ℝ ↦ y + t • v) 0 (1 : ℝ) = v := by
    rw [hd0.fderiv]
    simp
  have he : (fun t : ℝ ↦ freeHopfOrbitLift C x (y + t • v)) =
      (fun t : ℝ ↦ freeHopfProductFlow C i t (freeHopfOrbitLift C x y)) :=
    funext (freeHopfOrbitLift_coordinate_line C x y i)
  rw [freeHopfGenerator_eq_orbit_mfderiv]
  change mfderiv 𝓘(ℝ, ℝ) (freeHopfModel C)
    (fun t : ℝ ↦ freeHopfProductFlow C i t (freeHopfOrbitLift C x y)) 0 (1 : ℝ) = _
  rw [← he]
  have hc' := congrArg (fun L ↦ L (1 : ℝ)) hc
  rw [mfderiv_eq_fderiv] at hc'
  change mfderiv 𝓘(ℝ, ℝ) (freeHopfModel C)
      (fun t : ℝ ↦ freeHopfOrbitLift C x (y + t • v)) 0 (1 : ℝ) =
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) (freeHopfModel C)
      (freeHopfOrbitLift C x) (y + (0 : ℝ) • v)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (y + (0 : ℝ) • v)).symm
        (fderiv ℝ (fun t : ℝ ↦ y + t • v) 0 (1 : ℝ))) at hc'
  rw [hd] at hc'
  have hzv := congrArg (fun z : EuclideanSpace ℝ (Fin a) ↦
    (show FreeHopfModelSpace C from
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) (freeHopfModel C)
        (freeHopfOrbitLift C x) z
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v))) hzero
  exact hc'.trans hzv

/-- Actual native first derivatives are genuine coordinate derivatives of the orbit lift. -/
theorem freeHopf_first_orbitLift {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (U : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hU : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) (i : Fin a) :
    balancedDirectionalDerivative U (freeHopfGenerator C i) (freeHopfOrbitLift C x y) =
      fderiv ℝ (U ∘ freeHopfOrbitLift C x) y (EuclideanSpace.single i 1) :=
  balanced_directional_lift_pullback_at U (freeHopfGenerator C i)
    (freeHopfOrbitLift C x) y (EuclideanSpace.single i 1)
    (hU.mdifferentiableAt (by simp))
    ((freeHopfOrbitLift_contMDiff C x).mdifferentiableAt (by simp))
    (freeHopfGenerator_eq_orbitLift_mfderiv C x y i)

/-- Actual ordered second native derivatives equal the true second coordinate derivatives. -/
theorem freeHopf_second_orbitLift {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (U : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hU : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) (i j : Fin a) :
    balancedDirectionalDerivative (balancedDirectionalDerivative U (freeHopfGenerator C j))
      (freeHopfGenerator C i) (freeHopfOrbitLift C x y) =
      fderiv ℝ (fun z ↦ fderiv ℝ (U ∘ freeHopfOrbitLift C x) z
        (EuclideanSpace.single j 1)) y (EuclideanSpace.single i 1) :=
  balanced_second_directional_lift_pullback_at U hU
    (freeHopfGeneratorSection C i) (freeHopfGeneratorSection C j)
    (freeHopfOrbitLift C x) univ isOpen_univ
    (freeHopfOrbitLift_contMDiff C x).contMDiffOn y (mem_univ y)
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    (fun z _ ↦ freeHopfGenerator_eq_orbitLift_mfderiv C x z i)
    (fun z _ ↦ freeHopfGenerator_eq_orbitLift_mfderiv C x z j)

/-- The original little norm bounds the true native vertical C² size of its actual lift.

Proof: the genuine lift identity and the proved actual first/second chain rules identify
each native component with its original little-space value or coordinate derivative.
Apply the already accepted original little jet norm bounds, then sum the actual finite
family. This is only a lift-transfer theorem; the parent constructs the correction and
derives the lift identity by strict-small uniqueness rather than assuming either.
Source: the uniform vertical C² conclusion of lem:balanced, lines371–418. -/
theorem freeHopf_verticalC2Size_le_little_norm {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] {α : ℝ}
    (U : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hU : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (x : FreeHopfProduct C) (f : LittlePeriodicCAlphaFunction a N 2 α)
    (hlift : ∀ y, U (freeHopfOrbitLift C x y) = f.val.toFun y)
    (y : EuclideanSpace ℝ (Fin a)) :
    balancedVerticalC2Size (freeHopfGenerator C) U (freeHopfOrbitLift C x y) ≤
      (1 + (a : ℝ) + (a : ℝ) ^ 2) * ‖f‖ := by
  have he : U ∘ freeHopfOrbitLift C x = f.val.toFun := funext hlift
  apply balancedVerticalC2Size_le_of_components _ _ _ ‖f‖
  · rw [hlift]
    exact littlePeriodicCAlpha_value_norm_le f y
  · intro i
    rw [freeHopf_first_orbitLift C U hU x y i, he]
    exact littlePeriodicCAlpha_first_coordinate_norm_le f y i
  · intro i j
    rw [freeHopf_second_orbitLift C U hU x y i j, he]
    exact littlePeriodicCAlpha_second_coordinate_norm_le f y i j

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopfGenerator_eq_orbitLift_mfderiv
#print axioms GlobalEmbedding.Paper.freeHopf_first_orbitLift
#print axioms GlobalEmbedding.Paper.freeHopf_second_orbitLift
#print axioms GlobalEmbedding.Paper.freeHopf_verticalC2Size_le_little_norm
