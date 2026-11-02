import GlobalEmbedding.Paper.PlanarHopfGenerator
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# The actual normalized positive-integer power map on the whole Hopf sphere

Source: `main.tex`, `cor:selector`, lines575–582.
DAG: `selector-power-map`; exclusive proof owner W2.
The sphere, norm, atlas, period-one flow and generator are the original actual objects.
-/

noncomputable section
open scoped Manifold ContDiff
open NormedSpace

namespace GlobalEmbedding.Paper

/-- The literal coordinatewise power vector in the original complex Euclidean space.
Source: the numerator of P_K in main.tex576–578. -/
def selectorPowerRaw {C : ℕ} (K : ℕ) (z : PlanarHopfAmbient C) : PlanarHopfAmbient C :=
  WithLp.toLp 2 (fun j ↦ z j ^ K)

/-- The raw power vector at a genuine unit sphere point never vanishes, even if
some individual coordinates vanish. A unit vector has a nonzero coordinate, and
its positive integer power remains nonzero. Source: main.tex576–578. -/
theorem selectorPowerRaw_ne_zero {C : ℕ} (K : ℕ) (_hK : 1 ≤ K)
    (z : PlanarHopfSphere C) : selectorPowerRaw K (z : PlanarHopfAmbient C) ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, (z : PlanarHopfAmbient C) j ≠ 0 := by
    by_contra! hz
    apply ne_zero_of_mem_unit_sphere z
    ext j
    exact hz j
  intro hz
  have hp := congrArg (fun v : PlanarHopfAmbient C ↦ v j) hz
  exact pow_ne_zero K hj (by simpa [selectorPowerRaw] using hp)

/-- The true Euclidean norm of the raw vector is exactly the denominator printed
in the source. No supremum norm or chosen positive denominator is used.
Source: main.tex576–578. -/
theorem selectorPowerRaw_norm {C : ℕ} (K : ℕ) (z : PlanarHopfAmbient C) :
    ‖selectorPowerRaw K z‖ = Real.sqrt (∑ j, ‖z j‖ ^ (2 * K)) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [selectorPowerRaw, norm_pow, ← pow_mul, Nat.mul_comm K 2]

/-- The actual source denominator is strictly positive everywhere on the whole sphere.
Source: main.tex576–578. -/
theorem selectorPowerRaw_norm_pos {C : ℕ} (K : ℕ) (hK : 1 ≤ K)
    (z : PlanarHopfSphere C) : 0 < ‖selectorPowerRaw K (z : PlanarHopfAmbient C)‖ :=
  norm_pos_iff.mpr (selectorPowerRaw_ne_zero K hK z)

/-- The numerator is genuinely real smooth on the entire actual complex ambient
space. Real continuous-linear coordinate projections, polynomial powers and the
actual finite PiLp coordinate equivalence give the result, including zero coordinates.
Source: the smooth whole-sphere formula in main.tex576–580. -/
theorem selectorPowerRaw_contDiff (C K : ℕ) :
    ContDiff ℝ ∞ (selectorPowerRaw (C := C) K) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin C ↦ ℂ)).symm
  apply e.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  exact ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).contDiff.pow K

/-- The source's actual positive-integer power map, normalized by its true norm.
The proof of the sphere-valued condition uses the proved raw-vector nonvanishing;
no norm, denominator or smoothness data is assumed. Source: main.tex576–578. -/
def selectorPowerMap {C : ℕ} (K : ℕ) (hK : 1 ≤ K) :
    PlanarHopfSphere C → PlanarHopfSphere C := fun z ↦
  ⟨normalize (selectorPowerRaw K (z : PlanarHopfAmbient C)),
    mem_sphere_zero_iff_norm.mpr (norm_normalize (selectorPowerRaw_ne_zero K hK z))⟩

/-- The actual ambient value is normalization of precisely the original numerator.
Source: main.tex576–578. -/
@[simp] theorem selectorPowerMap_coe {C : ℕ} (K : ℕ) (hK : 1 ≤ K)
    (z : PlanarHopfSphere C) :
    (selectorPowerMap K hK z : PlanarHopfAmbient C) =
      normalize (selectorPowerRaw K (z : PlanarHopfAmbient C)) := rfl

/-- The genuine normalized power map is native smooth on the whole sphere.
The numerator is a real polynomial; its norm and norm inverse are smooth at every
actual nonzero raw vector. Restrict this true ambient smooth germ to the original
native sphere, then apply the genuine sphere codomain criterion.
Source: the whole smooth power map in main.tex575–580. -/
theorem selectorPowerMap_contMDiff (C : ℕ) [Fact (0 < C)] (K : ℕ) (hK : 1 ≤ K) :
    ContMDiff (planarHopfModel C) (planarHopfModel C) ∞ (selectorPowerMap (C := C) K hK) := by
  apply ContMDiff.codRestrict_sphere
  intro z
  have hv := (selectorPowerRaw_contDiff C K).contDiffAt (x := (z : PlanarHopfAmbient C))
  have hn := hv.norm ℂ (selectorPowerRaw_ne_zero K hK z)
  have hi := hn.inv (norm_ne_zero_iff.mpr (selectorPowerRaw_ne_zero K hK z))
  exact (hi.smul hv).contMDiffAt.comp z (planarHopfSphere_contMDiff_coe C z)

/-- Every coordinate agrees literally with the printed normalized power formula.
The denominator is proved positive above rather than assumed.
Source: main.tex576–578. -/
theorem selectorPowerMap_apply {C : ℕ} (K : ℕ) (hK : 1 ≤ K)
    (z : PlanarHopfSphere C) (j : Fin C) :
    (selectorPowerMap K hK z : PlanarHopfAmbient C) j =
      ((z : PlanarHopfAmbient C) j ^ K) /
        (Real.sqrt (∑ i, ‖(z : PlanarHopfAmbient C) i‖ ^ (2 * K)) : ℂ) := by
  change (‖selectorPowerRaw K (z : PlanarHopfAmbient C)‖⁻¹ : ℝ) •
    ((z : PlanarHopfAmbient C) j ^ K) = _
  rw [selectorPowerRaw_norm, RCLike.real_smul_eq_coe_mul]
  push_cast
  rw [div_eq_mul_inv, mul_comm]
  rfl

/-- At the original allowed exponent K=1 the same whole-sphere map is identity.
Source: the positive-integer range of main.tex576–580. -/
theorem selectorPowerMap_one {C : ℕ} (z : PlanarHopfSphere C) :
    selectorPowerMap 1 (by decide) z = z := by
  apply Subtype.ext
  change normalize (selectorPowerRaw 1 (z : PlanarHopfAmbient C)) = _
  have hr : selectorPowerRaw 1 (z : PlanarHopfAmbient C) = (z : PlanarHopfAmbient C) := by
    ext j
    simp [selectorPowerRaw]
  rw [hr]
  exact normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp z.property)

/-- The actual polynomial numerator transports scalar multiplication by the
literal integer power of the same scalar. Source: main.tex576–580. -/
theorem selectorPowerRaw_smul {C : ℕ} (K : ℕ) (c : ℂ) (z : PlanarHopfAmbient C) :
    selectorPowerRaw K (c • z) = c ^ K • selectorPowerRaw K z := by
  ext j
  simp [selectorPowerRaw, mul_pow]

/-- Raising the original period-one Hopf multiplier to K gives precisely its
multiplier at time K*t, retaining the source's exact 2pi normalization.
Source: main.tex579–580. -/
theorem selectorPowerHopfMultiplier_pow (K : ℕ) (t : ℝ) :
    (Circle.exp (2 * Real.pi * t) : ℂ) ^ K =
      (Circle.exp (2 * Real.pi * ((K : ℝ) * t)) : ℂ) := by
  change Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) ^ K =
    Complex.exp ((2 * Real.pi * ((K : ℝ) * t) : ℝ) * Complex.I)
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The actual normalized whole-sphere map intertwines the original Hopf flow
with time K*t. The same true denominator is invariant under the unit Hopf
multiplier, so no denominator or equivariance hypothesis is supplied.
Source: main.tex579–580. -/
theorem selectorPowerMap_flow {C : ℕ} (K : ℕ) (hK : 1 ≤ K)
    (t : ℝ) (z : PlanarHopfSphere C) :
    selectorPowerMap K hK (planarHopfFlow t z) =
      planarHopfFlow ((K : ℝ) * t) (selectorPowerMap K hK z) := by
  apply Subtype.ext
  change normalize (selectorPowerRaw K ((Circle.exp (2 * Real.pi * t) : ℂ) •
    (z : PlanarHopfAmbient C))) =
    (Circle.exp (2 * Real.pi * ((K : ℝ) * t)) : ℂ) •
      normalize (selectorPowerRaw K (z : PlanarHopfAmbient C))
  simp only [selectorPowerRaw_smul, NormedSpace.normalize, norm_smul, norm_pow,
    Circle.norm_coe, one_pow, one_mul]
  rw [selectorPowerHopfMultiplier_pow]
  exact smul_comm _ _ _

/-- The actual native differential sends the original period-one Hopf generator
to K times that same target generator. Differentiate the genuine flow identity
in the actual ambient space, apply the native tangent chain rule, and use the
injective differential of the true sphere inclusion. No desired pushforward or
formal derivative is assumed. Source: (P_K)_*X=KX in main.tex579–580. -/
theorem selectorPowerMap_generator (C : ℕ) [Fact (0 < C)] (K : ℕ) (hK : 1 ≤ K)
    (z : PlanarHopfSphere C) :
    mfderiv (planarHopfModel C) (planarHopfModel C) (selectorPowerMap K hK) z
      (planarHopfGenerator z) = (K : ℝ) • planarHopfGenerator (selectorPowerMap K hK z) := by
  let P := selectorPowerMap (C := C) K hK
  have hP := selectorPowerMap_contMDiff C K hK
  have hobs := (planarHopfSphere_contMDiff_coe C).comp hP
  have hchain := mvfderiv_comp_apply (I := planarHopfModel C) (I' := planarHopfModel C)
    (f := P) (g := fun w : PlanarHopfSphere C ↦ (w : PlanarHopfAmbient C)) z
    ((planarHopfSphere_contMDiff_coe C).mdifferentiableAt (by norm_num))
    (hP.mdifferentiableAt (by norm_num)) (planarHopfGenerator z)
  have hvel := planarHopfOrbit_hasDerivAt (P z)
  have htime := (hasDerivAt_id (0 : ℝ)).const_mul (K : ℝ)
  have hvel' : HasDerivAt (fun t : ℝ ↦ (planarHopfFlow t (P z) : PlanarHopfAmbient C))
      ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (P z : PlanarHopfAmbient C))
      ((K : ℝ) * 0) := by simpa only [mul_zero] using hvel
  have hd := hvel'.scomp 0 htime
  have he : (fun t : ℝ ↦ (P (planarHopfFlow t z) : PlanarHopfAmbient C)) =
      fun t ↦ (planarHopfFlow ((K : ℝ) * t) (P z) : PlanarHopfAmbient C) := by
    funext t
    exact congrArg (fun w : PlanarHopfSphere C ↦ (w : PlanarHopfAmbient C))
      (selectorPowerMap_flow K hK t z)
  apply injective_mvfderiv_subtypeVal_sphere (n := 2 * C - 1) (P z)
  rw [map_smul, planarHopfGenerator_ambient]
  rw [← hchain]
  rw [planarHopfGenerator_mvfderiv _ hobs z]
  change deriv (fun t : ℝ ↦ (P (planarHopfFlow t z) : PlanarHopfAmbient C)) 0 = _
  rw [he]
  simpa only [Function.comp_def, mul_one] using hd.deriv

end GlobalEmbedding.Paper
