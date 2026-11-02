import GlobalEmbedding.Paper.CollarEuclideanRealForm
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslate
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual source coefficient translation identity on canonical real parameters

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. This supplies the actual source parameter identity used by uniqueness.
-/

open Set Filter WithLp
open scoped Topology

namespace GlobalEmbedding.Paper

/-- The actual real joint base/translation parameter CLM into the canonical real submodule.
Source: Proposition `prop:collar`. Append the actual real Euclidean coordinates and apply
the canonical actual real-form isometry. No parameter inclusion is assumed. -/
noncomputable def collarRealJointParameter (b a : ℕ) :
    (EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a)) →L[ℝ]
      collarEuclideanRealSubmodule (b + a) := by
  let L : (EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (b + a)) :=
    { toFun := fun z ↦ toLp 2 (Fin.append (fun i ↦ z.1 i) (fun j ↦ z.2 j))
      map_add' := by intro z w; ext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
      map_smul' := by intro c z; ext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp }
  exact (collarEuclideanRealEquiv (b + a)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    L.toContinuousLinearMap

/-- Actual real base coordinates of the canonical joint parameter.
Source: Proposition `prop:collar`. Evaluate the explicit coordinate append and real inclusion. -/
theorem collar_real_joint_parameter_base {b a : ℕ}
    (z : EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a)) (i : Fin b) :
    (((collarRealJointParameter b a z).val (Fin.castAdd a i)).re) = z.1 i := by
  simp [collarRealJointParameter, collarEuclideanRealEquiv]

/-- Actual real orbit-translation coordinates of the canonical joint parameter.
Source: Proposition `prop:collar`. Evaluate the explicit coordinate append and real inclusion. -/
theorem collar_real_joint_parameter_shift {b a : ℕ}
    (z : EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a)) (j : Fin a) :
    (((collarRealJointParameter b a z).val (Fin.natAdd b j)).re) = z.2 j := by
  simp [collarRealJointParameter, collarEuclideanRealEquiv]

/-- The joint parameter at the real source base and zero translation is the actual base point.
Source: Proposition `prop:collar`. The canonical real append agrees at every finite coordinate. -/
theorem collar_real_joint_parameter_basepoint {b a : ℕ} (p₀ : Fin b → ℝ) :
    collarRealJointParameter b a (toLp 2 p₀, 0) = collarEuclideanRealEquiv (b + a)
      (toLp 2 (Fin.append p₀ (fun _ : Fin a ↦ (0 : ℝ)))) := by
  apply Subtype.ext
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [collarRealJointParameter, collarEuclideanRealEquiv]

/-- Actual real Holder coefficient families with exact translated source lifts satisfy the
actual little-space shift identity for all sufficiently near joint real parameters.

Source: Proposition `prop:collar`, proof lines 530–534. Pull the actual source lift identity
back along the actual joint parameter CLM and along its base/zero-translation restriction.
Both maps are continuous and have the same actual base point. For nearby parameters, actual
Holder translation evaluates the base slice at y+α. The two exact source formulas coincide
at every lift point, so actual carrier injectivity proves equality in the original normed space.
No shift identity, continuous source family or alternate translation operation is assumed. -/
theorem collar_source_holder_translation_identity {b a N k : ℕ} {α : ℝ}
    (f : (Fin (b + a) → ℝ) → (Fin N → ℝ)) (p₀ : Fin b → ℝ)
    (F : collarEuclideanRealSubmodule (b + a) → LittlePeriodicCAlphaFunction a N k α)
    (hsource : ∀ᶠ p : collarEuclideanRealSubmodule (b + a) in
      𝓝 (collarEuclideanRealEquiv (b + a)
        (toLp 2 (Fin.append p₀ (fun _ : Fin a ↦ (0 : ℝ))))),
      ∀ y : EuclideanSpace ℝ (Fin a), (F p).val.toFun y =
        toLp 2 (fun l ↦ f
          (Fin.append (fun i : Fin b ↦ (p.val (Fin.castAdd a i)).re)
            (fun j : Fin a ↦ y j + (p.val (Fin.natAdd b j)).re)) l)) :
    ∀ᶠ z : EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a) in 𝓝 (toLp 2 p₀, 0),
      F (collarRealJointParameter b a z) =
        littlePeriodicCAlphaTranslateIsometry z.2
          (F (collarRealJointParameter b a (z.1, 0))) := by
  have hbase : Continuous (fun z : EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a) ↦
      collarRealJointParameter b a (z.1, 0)) :=
    (collarRealJointParameter b a).continuous.comp (continuous_fst.prodMk continuous_const)
  have h₁ := (collarRealJointParameter b a).continuous.tendsto (toLp 2 p₀, 0)
  have h₂ := hbase.tendsto (toLp 2 p₀, 0)
  rw [collar_real_joint_parameter_basepoint] at h₁ h₂
  filter_upwards [h₁.eventually hsource, h₂.eventually hsource] with z hz hz₀
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext y
  change (F (collarRealJointParameter b a z)).val.toFun y =
    (F (collarRealJointParameter b a (z.1, 0))).val.toFun (y + z.2)
  rw [hz, hz₀]
  simp only [collar_real_joint_parameter_base, collar_real_joint_parameter_shift,
    PiLp.add_apply, PiLp.zero_apply, add_zero]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarRealJointParameter
#print axioms GlobalEmbedding.Paper.collar_source_holder_translation_identity
