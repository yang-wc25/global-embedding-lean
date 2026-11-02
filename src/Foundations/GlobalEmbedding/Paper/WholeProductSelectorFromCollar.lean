import GlobalEmbedding.Paper.HopfCollarProperties
import GlobalEmbedding.Paper.HopfCollarTimeDifferentiation
import GlobalEmbedding.Paper.HopfCollarRadialOrthogonality
import GlobalEmbedding.Paper.FreeHopfDerivativeCommute
import GlobalEmbedding.Paper.FreeHopfProductSuccessor
import GlobalEmbedding.Paper.SelectorPowerMap
import GlobalEmbedding.Paper.SelectorCompactInjectiveBound
import GlobalEmbedding.Paper.TrueSecondFormEvaluation
import GlobalEmbedding.Paper.SymmetricSquareLinearMap
import GlobalEmbedding.Paper.SymmetricSquareNorms
import GlobalEmbedding.Paper.TargetDimension
import GlobalEmbedding.Targets.PlanarSelectors
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The original whole-product selector from an actual native collar

Source: `literature/parallelizable-stable-plus-one/main.tex`, cor:selector, lines565–584.
DAG: selector-from-actual-collar; parent cor-selector. Exclusive owner W3.
The full original target remains open until the original collar is supplied internally;
no collar premise is added to that target.
The geometric lemmas below use the same native Hopf flows and actual derivatives.
-/

noncomputable section

open Manifold
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Paper

/-- Constant actual partial Gram and genuine Hopf commutation make every actual
second column normal to every partial tangent, including the last tangent.

Differentiate the constant pairings along three actual factor orbits. The native
inner-product rule gives the three cyclic equations; actual mixed-derivative
commutation and symmetry of the real inner product make their only solution zero.
Source: cor:selector, the second-form normality argument, lines580–582. -/
theorem selector_second_inner_first_eq_zero {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hGram : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S x) = 1)
    (x : FreeHopfProduct C) (i j k : Fin a) :
    inner ℝ (freeHopfDeriv C i (freeHopfDeriv C j S) x)
      (freeHopfDeriv C k S x) = 0 := by
  have hs (l : Fin a) : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freeHopfDeriv C l S) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C l)
      (freeHopfProductFlow_contMDiff C l) S hS
  have hd (l p q : Fin a) :
      inner ℝ (freeHopfDeriv C p S x)
          (freeHopfDeriv C l (freeHopfDeriv C q S) x) +
        inner ℝ (freeHopfDeriv C l (freeHopfDeriv C p S) x)
          (freeHopfDeriv C q S x) = 0 := by
    have hp := hasDerivAt_orbit (freeHopfProductFlow C l)
      (freeHopfProductFlow_contMDiff C l) (freeHopfProductFlow_add C l)
      (freeHopfDeriv C p S) (hs p) 0 x
    have hq := hasDerivAt_orbit (freeHopfProductFlow C l)
      (freeHopfProductFlow_contMDiff C l) (freeHopfProductFlow_add C l)
      (freeHopfDeriv C q S) (hs q) 0 x
    have h := (hp.inner ℝ hq).deriv
    have he : (fun t : ℝ ↦
        inner ℝ (freeHopfDeriv C p S (freeHopfProductFlow C l t x))
          (freeHopfDeriv C q S (freeHopfProductFlow C l t x))) =
        fun _ ↦ (1 : Matrix (Fin a) (Fin a) ℝ) p q := by
      funext t
      exact congrArg (fun A : Matrix (Fin a) (Fin a) ℝ ↦ A p q)
        (hGram (freeHopfProductFlow C l t x))
    rw [he, deriv_const] at h
    simpa only [freeHopfDeriv, freeHopfProductFlow_zero] using h.symm
  have h₁ := hd i j k
  have h₂ := hd j k i
  have h₃ := hd k i j
  rw [freeHopfDeriv_commute_euclidean C S hS j i] at h₂
  rw [freeHopfDeriv_commute_euclidean C S hS k j,
    freeHopfDeriv_commute_euclidean C S hS k i] at h₃
  simp only [real_inner_comm] at h₁ h₂ h₃ ⊢
  linarith

/-- The normal space of the actual multi-orbit leaf is precisely the paper's
partial normal space. This is an equality of actual submodules, not a replacement
of the full Hopf product's total normal space by its partial normal space.
The accepted first-jet lift formula and the native coordinate basis identify the
derivative range with the span of all original Hopf partial tangents.
Source: setup:partial, lines216–220, used in cor:selector. -/
theorem selector_orbitLeaf_normalSpace {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (x : FreeHopfProduct C) :
    normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
      (S ∘ freeHopfOrbitLift C x) 0 =
      (Submodule.span ℝ (Set.range (fun i ↦ freeHopfDeriv C i S x)))ᗮ := by
  simp only [normalSpace, mfderiv_eq_fderiv]
  change (LinearMap.range (fderiv ℝ (S ∘ freeHopfOrbitLift C x) 0).toLinearMap)ᗮ = _
  have he : (fderiv ℝ (S ∘ freeHopfOrbitLift C x) 0).toLinearMap =
      (EuclideanSpace.basisFun (Fin a) ℝ).toBasis.constr ℝ
        (fun i ↦ freeHopfDeriv C i S x) := by
    apply (EuclideanSpace.basisFun (Fin a) ℝ).toBasis.ext
    intro i
    rw [Module.Basis.constr_basis]
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    have hi := freeHopf_first_orbitLift C S hS x 0 i
    rw [freeHopfOrbitLift_zero] at hi
    exact hi.symm.trans (freeHopfGenerator_mvfderiv C i S hS x)
  rw [he, Module.Basis.constr_range]

/-- With constant actual partial Gram, each actual second column belongs to the
true normal space of the same multi-orbit leaf. This includes every diagonal and
every ordered pair, and projects away all partial tangent directions.
Source: the true partial normal projection in cor:selector, lines580–582. -/
theorem selector_second_mem_orbitLeaf_normalSpace {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hGram : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S x) = 1)
    (x : FreeHopfProduct C) (i j : Fin a) :
    freeHopfDeriv C i (freeHopfDeriv C j S) x ∈
      normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
        (S ∘ freeHopfOrbitLift C x) 0 := by
  rw [selector_orbitLeaf_normalSpace C S hS x, Submodule.mem_orthogonal']
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨k, rfl⟩ := hv
    exact selector_second_inner_first_eq_zero C S hS hGram x i j k
  | zero => simp
  | add v w _ _ hv hw => simp only [inner_add_right, hv, hw, add_zero]
  | smul r v _ hv => simp only [inner_smul_right, hv, mul_zero]

/-- On the same genuine multi-orbit leaf, the canonical true second form on
each exact symmetric-square product is the true partial normal projection of
the literal ordered Hopf second derivative. There is no factor one half.
Use the accepted actual second-jet lift formula and native CLM evaluation
differentiation, then evaluate the existing true second form in the identity chart.
Source: setup:partial and cor:selector, lines216–220 and580–582. -/
theorem selector_orbitLeaf_secondForm_product {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (x : FreeHopfProduct C) (i j : Fin a) :
    (trueSecondForm (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) (S ∘ freeHopfOrbitLift C x)
        (hS.comp (freeHopfOrbitLift_contMDiff C x)) 0
        (symmetricSquareProduct (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin a))
            (0 : EuclideanSpace ℝ (Fin a)))
          ((NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin a))).symm
            (EuclideanSpace.single i 1))
          ((NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin a))).symm
            (EuclideanSpace.single j 1))) : EuclideanSpace ℝ (Fin N)) =
      (normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
        (S ∘ freeHopfOrbitLift C x) 0).starProjection
          (freeHopfDeriv C i (freeHopfDeriv C j S) x) := by
  have hs (k : Fin a) : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freeHopfDeriv C k S) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C k)
      (freeHopfProductFlow_contMDiff C k) S hS
  have he (k : Fin a) : balancedDirectionalDerivative S (freeHopfGenerator C k) =
      freeHopfDeriv C k S :=
    funext (fun z ↦ freeHopfGenerator_mvfderiv C k S hS z)
  have hsecond := freeHopf_second_orbitLift C S hS x 0 i j
  rw [freeHopfOrbitLift_zero, he j] at hsecond
  change mvfderiv (freeHopfModel C) (freeHopfDeriv C j S) x
      (freeHopfGenerator C i x) = _ at hsecond
  rw [freeHopfGenerator_mvfderiv C i _ (hs j)] at hsecond
  have hL : ContDiff ℝ ∞ (S ∘ freeHopfOrbitLift C x) :=
    (hS.comp (freeHopfOrbitLift_contMDiff C x)).contDiff
  have hdf : DifferentiableAt ℝ (fderiv ℝ (S ∘ freeHopfOrbitLift C x)) 0 :=
    (hL.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have heval : fderiv ℝ (fun y ↦ fderiv ℝ (S ∘ freeHopfOrbitLift C x) y
      (EuclideanSpace.single j 1)) 0 =
      (fderiv ℝ (fderiv ℝ (S ∘ freeHopfOrbitLift C x)) 0).flip
        (EuclideanSpace.single j 1) := by
    have h := hdf.hasFDerivAt.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single j 1) (0 : EuclideanSpace ℝ (Fin a)))
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using h.fderiv
  rw [heval] at hsecond
  rw [trueSecondForm_product]
  change (normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
      (S ∘ freeHopfOrbitLift C x) 0).starProjection
        (fderiv ℝ (fderiv ℝ ((S ∘ freeHopfOrbitLift C x) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) 0).symm))
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) 0 0)
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = _
  rw [extChartAt_model_space_eq_id]
  change (normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
      (S ∘ freeHopfOrbitLift C x) 0).starProjection
        (fderiv ℝ (fderiv ℝ (S ∘ freeHopfOrbitLift C x)) 0
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = _
  exact congrArg (fun v : EuclideanSpace ℝ (Fin N) ↦
    (normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
      (S ∘ freeHopfOrbitLift C x) 0).starProjection v) hsecond.symm

/-- For constant partial Gram, the actual partial second form equals the raw
second column because that very column is proved to be in the true partial normal
space. This is an equality of the canonical true form, not a rank proxy.
Source: cor:selector, lines580–582. -/
theorem selector_orbitLeaf_secondForm_product_of_gram {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hGram : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S x) = 1)
    (x : FreeHopfProduct C) (i j : Fin a) :
    (trueSecondForm (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) (S ∘ freeHopfOrbitLift C x)
        (hS.comp (freeHopfOrbitLift_contMDiff C x)) 0
        (symmetricSquareProduct (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin a))
            (0 : EuclideanSpace ℝ (Fin a)))
          ((NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin a))).symm
            (EuclideanSpace.single i 1))
          ((NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin a))).symm
            (EuclideanSpace.single j 1))) : EuclideanSpace ℝ (Fin N)) =
      freeHopfDeriv C i (freeHopfDeriv C j S) x := by
  rw [selector_orbitLeaf_secondForm_product C S hS x i j]
  exact Submodule.starProjection_eq_self_iff.mpr
    (selector_second_mem_orbitLeaf_normalSpace C S hS hGram x i j)

/-- The literal shrunken planar map from the paper, using the already proved
normalized whole-sphere power map. No second power map or source carrier is defined.
Source: p_K=K⁻¹p∘P_K in cor:selector, lines575–580. -/
def selectorSmallPlanar {C : ℕ} (p : PlanarHopfSphere C → Planar)
    (K : ℕ) (hK : 1 ≤ K) (z : PlanarHopfSphere C) : Planar :=
  (K : ℝ)⁻¹ • p (selectorPowerMap K hK z)

/-- The same literal shrunken planar map is native smooth on the whole sphere.
Source: the global construction in cor:selector, lines575–580. -/
theorem selectorSmallPlanar_contMDiff {C : ℕ} [Fact (0 < C)]
    (p : PlanarHopfSphere C → Planar)
    (hp : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ p) (K : ℕ) (hK : 1 ≤ K) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ (selectorSmallPlanar p K hK) := by
  let L : Planar →L[ℝ] Planar := (K : ℝ)⁻¹ • ContinuousLinearMap.id ℝ Planar
  exact L.contDiff.contMDiff.comp (hp.comp (selectorPowerMap_contMDiff C K hK))

/-- Its actual original-period Hopf derivative is exactly Xp∘P_K. The accepted
power-flow identity and native one-variable chain rule cancel the two K factors.
Source: the unit-speed identity in cor:selector, lines579–580. -/
theorem selectorSmallPlanar_orbitDeriv {C : ℕ} [Fact (0 < C)]
    (p : PlanarHopfSphere C → Planar)
    (hp : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ p) (K : ℕ) (hK : 1 ≤ K)
    (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (selectorSmallPlanar p K hK) z =
      orbitDeriv planarHopfFlow p (selectorPowerMap K hK z) := by
  have hKn : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have htime := (hasDerivAt_id (0 : ℝ)).const_mul (K : ℝ)
  have hcurve := (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add p hp ((K : ℝ) * 0) (selectorPowerMap K hK z)).scomp 0 htime
  have hd := (HasDerivAt.fun_const_smul (c := (K : ℝ)⁻¹) hcurve).deriv
  have he : (fun t : ℝ ↦ selectorSmallPlanar p K hK (planarHopfFlow t z)) =
      fun t ↦ (K : ℝ)⁻¹ •
        p (planarHopfFlow ((K : ℝ) * t) (selectorPowerMap K hK z)) := by
    funext t
    rw [selectorSmallPlanar, selectorPowerMap_flow]
  unfold orbitDeriv
  rw [he]
  simpa only [Function.comp_def, Pi.smul_apply, mul_zero, mul_one, planarHopfFlow_zero,
    smul_smul, inv_mul_cancel₀ hKn, one_smul, orbitDeriv] using hd

/-- One positive integer makes the values of the same unit-speed planar selector
uniformly small on the whole sphere. Compactness bounds the original actual map;
the Archimedean property chooses one K and the accepted power map preserves speed.
No new selector is chosen separately on any coordinate subsphere.
Source: the single K choice in cor:selector, lines579–580. -/
theorem selector_small_planar_exists {C : ℕ} [Fact (0 < C)]
    (p : PlanarHopfSphere C → Planar)
    (hp : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ p)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow p z‖ = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : PlanarHopfSphere C → Planar,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ q ∧
      (∀ z, ‖orbitDeriv planarHopfFlow q z‖ = 1) ∧ (∀ z, ‖q z‖ < δ) := by
  obtain ⟨B, hB, hbound⟩ := (isCompact_univ.image hp.continuous).isBounded.exists_pos_norm_le
  obtain ⟨K, hK⟩ := exists_nat_gt (max (1 : ℝ) (B / δ))
  have hKr : 1 < (K : ℝ) := lt_of_le_of_lt (le_max_left _ _) hK
  have hKpos : (0 : ℝ) < K := lt_trans zero_lt_one hKr
  have hKn : 1 ≤ K := by exact_mod_cast (le_of_lt hKr)
  refine ⟨selectorSmallPlanar p K hKn, selectorSmallPlanar_contMDiff p hp K hKn, ?_, ?_⟩
  · intro z
    rw [selectorSmallPlanar_orbitDeriv p hp]
    exact hunit _
  · intro z
    have hb : ‖p (selectorPowerMap K hKn z)‖ ≤ B :=
      hbound _ (Set.mem_image_of_mem p (Set.mem_univ _))
    have hlarge : B / δ < (K : ℝ) := lt_of_le_of_lt (le_max_right _ _) hK
    have hsmall : B / (K : ℝ) < δ :=
      (div_lt_iff₀ hKpos).mpr (by
        have h := (div_lt_iff₀ hδ).mp hlarge
        nlinarith)
    calc
      ‖selectorSmallPlanar p K hKn z‖ = (K : ℝ)⁻¹ * ‖p (selectorPowerMap K hKn z)‖ := by
        rw [selectorSmallPlanar, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hKpos)]
      _ ≤ (K : ℝ)⁻¹ * B := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hKpos.le)
      _ < δ := by simpa only [div_eq_mul_inv, mul_comm] using hsmall

/-- Append one literal real coordinate in the original Euclidean l2 target.
Source: S=(G(a_K,y),b_K) in cor:selector, line580. -/
def selectorSnoc {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) (b : ℝ) :
    EuclideanSpace ℝ (Fin (N + 1)) := WithLp.toLp 2 (Fin.snoc (fun i ↦ v i) b)

/-- The literal appended target coordinate preserves the actual orthogonal
Euclidean block pairing, with no max-norm product substituted for l2.
Source: the partial Gram computation in cor:selector, lines580–582. -/
theorem selectorSnoc_inner {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (b c : ℝ) :
    inner ℝ (selectorSnoc v b) (selectorSnoc w c) = inner ℝ v w + b * c := by
  simp only [PiLp.inner_apply, selectorSnoc]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, RCLike.inner_apply, conj_trivial]
  rw [mul_comm c b]

/-- Appending the one actual coordinate preserves native smoothness on every
native source. This is the finite Pi smoothness criterion in the l2 coordinate model.
Source: the global smooth map in cor:selector, line580. -/
theorem selectorSnoc_contMDiff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}
    (v : M → EuclideanSpace ℝ (Fin N)) (b : M → ℝ)
    (hv : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ v)
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (N + 1))) ∞
      (fun x ↦ selectorSnoc (v x) (b x)) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (N + 1) ↦ ℝ)).symm
  apply e.contDiff.contMDiff.comp
  apply contMDiff_pi_module_iff.mpr
  intro j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simpa only [Fin.snoc_last] using hb
  · simpa only [Fin.snoc_castSucc, Function.comp_def, EuclideanSpace.proj,
      PiLp.proj_apply] using (EuclideanSpace.proj i).contMDiff.comp hv

/-- Actual derivatives append the actual component derivatives. The native
finite Pi derivative rule and the fixed PiLp linear equivalence prove this.
Source: the real derivative columns of cor:selector, lines580–582. -/
theorem selectorSnoc_hasDerivAt {N : ℕ} (v : ℝ → EuclideanSpace ℝ (Fin N))
    (b : ℝ → ℝ) (v' : EuclideanSpace ℝ (Fin N)) (b' t : ℝ)
    (hv : HasDerivAt v v' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s ↦ selectorSnoc (v s) (b s)) (selectorSnoc v' b') t := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (N + 1) ↦ ℝ)).symm
  apply e.hasFDerivAt.comp_hasDerivAt t
  apply hasDerivAt_pi.mpr
  intro j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simpa only [Fin.snoc_last] using hb
  · simpa only [Fin.snoc_castSucc, EuclideanSpace.proj, PiLp.proj_apply,
      Function.comp_def] using
      (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t hv

/-- The one globally defined selector composed from the actual collar and the
same small planar selector, on the existing actual successor Hopf product.
Source: the literal formula in cor:selector, line580. -/
def selectorFromCollar {m N : ℕ} (C : Fin (m + 1) → ℕ)
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin N))
    (q : PlanarHopfSphere (C (Fin.last m)) → Planar) (x : FreeHopfProduct C) :
    EuclideanSpace ℝ (Fin (N + 1)) :=
  selectorSnoc (G (q (freeHopfProductSplit C x).2 0, (freeHopfProductSplit C x).1))
    (q (freeHopfProductSplit C x).2 1)

/-- The same constructed selector is native smooth everywhere. The actual planar
first coordinate lies in the common open collar; joint omega regularity on that
collar therefore composes to native infinity regularity on the whole product.
Source: cor:selector, lines579–580. -/
theorem selectorFromCollar_contMDiff {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin N))
    (r0 : ℝ) (hG : AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G)
    (q : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hq : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ q)
    (hrange : ∀ z, q z 0 ∈ Set.Ioo (-r0) r0) :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (N + 1))) ∞
      (selectorFromCollar C G q) := by
  have hsplit := freeHopfProductSplit_contMDiff C
  have hlast := hq.comp (contMDiff_snd.comp hsplit)
  have ha := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contMDiff.comp hlast
  have hb := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contMDiff.comp hlast
  have hold := contMDiff_fst.comp hsplit
  have hpair := ha.prodMk hold
  have hcomp := (hG.1.of_le (show (∞ : ℕ∞ω) ≤ ω by simp)).comp_contMDiff hpair
    (fun x ↦ ⟨hrange _, Set.mem_univ _⟩)
  exact selectorSnoc_contMDiff _ _ hcomp hb

/-- Every actual slice inside the native analytic collar is native smooth on
the whole old Hopf product, by composition with the actual constant-r inclusion.
Source: prop:collar, used in cor:selector, lines574–580. -/
theorem selector_collar_slice_contMDiff {m N : ℕ} (C : Fin m → ℕ)
    [∀ i, Fact (0 < C i)]
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r0 : ℝ) (hG : AnalyticHopfCollarProperties C r0 G) (r : ℝ)
    (hr : r ∈ Set.Ioo (-r0) r0) :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun y ↦ G (r, y)) :=
  (hG.1.of_le (show (∞ : ℕ∞ω) ≤ ω by simp)).comp_contMDiff
    (contMDiff_const.prodMk contMDiff_id) (fun _ ↦ ⟨hr, Set.mem_univ _⟩)

/-- The old first columns of the same selector are precisely the old collar
columns with zero last coordinate. The exact successor flow identity makes
the planar input constant, and native orbit differentiation computes the result.
Source: Y_i S=(Y_i G,0) in cor:selector, lines580–581. -/
theorem selectorFromCollar_deriv_old {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin N))
    (r0 : ℝ) (hG : AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G)
    (q : PlanarHopfSphere (C (Fin.last m)) → Planar) (x : FreeHopfProduct C)
    (hr : q (freeHopfProductSplit C x).2 0 ∈ Set.Ioo (-r0) r0) (i : Fin m) :
    freeHopfDeriv C i.castSucc (selectorFromCollar C G q) x =
      selectorSnoc (freeHopfDeriv (freeHopfOldDimensions C) i
        (fun y ↦ G (q (freeHopfProductSplit C x).2 0, y))
        (freeHopfProductSplit C x).1) 0 := by
  have hs := selector_collar_slice_contMDiff (freeHopfOldDimensions C) G r0 hG _ hr
  have hd := hasDerivAt_orbit (freeHopfProductFlow (freeHopfOldDimensions C) i)
    (freeHopfProductFlow_contMDiff (freeHopfOldDimensions C) i)
    (freeHopfProductFlow_add (freeHopfOldDimensions C) i) _ hs 0
    (freeHopfProductSplit C x).1
  have hb := hasDerivAt_const (0 : ℝ) (q (freeHopfProductSplit C x).2 1)
  have h := selectorSnoc_hasDerivAt _ _ _ _ _ hd hb
  have he : (fun t : ℝ ↦ selectorFromCollar C G q
      (freeHopfProductFlow C i.castSucc t x)) =
      fun t ↦ selectorSnoc
        (G (q (freeHopfProductSplit C x).2 0,
          freeHopfProductFlow (freeHopfOldDimensions C) i t
            (freeHopfProductSplit C x).1))
        (q (freeHopfProductSplit C x).2 1) := by
    funext t
    simp only [selectorFromCollar, freeHopfProductSplit_flow_old]
  change deriv (fun t ↦ selectorFromCollar C G q
    (freeHopfProductFlow C i.castSucc t x)) 0 = _
  rw [he]
  simpa only [freeHopfProductFlow_zero, freeHopfDeriv] using h.deriv

/-- The last actual first column of the same selector is the literal chain-rule
column ((Xa)G_r,Xb). Only native first curve calculus is used here; the independent
time/Y mixed-derivative and metric-propagation obligations remain owned by W2.
Source: Y_n S=((Xa_K)G_r,Xb_K) in cor:selector, lines580–581. -/
theorem selectorFromCollar_deriv_last {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin N))
    (r0 : ℝ) (hG : AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G)
    (q : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hq : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ q)
    (x : FreeHopfProduct C) (hr : q (freeHopfProductSplit C x).2 0 ∈ Set.Ioo (-r0) r0) :
    freeHopfDeriv C (Fin.last m) (selectorFromCollar C G q) x =
      selectorSnoc
        ((orbitDeriv planarHopfFlow q (freeHopfProductSplit C x).2 0) •
          hopfCollarRDeriv G (q (freeHopfProductSplit C x).2 0)
            (freeHopfProductSplit C x).1)
        (orbitDeriv planarHopfFlow q (freeHopfProductSplit C x).2 1) := by
  let z := (freeHopfProductSplit C x).2
  let y := (freeHopfProductSplit C x).1
  have hq' := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff (C (Fin.last m)))
    planarHopfFlow_add q hq 0 z
  have hproj (i : Fin 2) : HasDerivAt (fun t : ℝ ↦ q (planarHopfFlow t z) i)
      (orbitDeriv planarHopfFlow q z i) 0 := by
    simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply,
      planarHopfFlow_zero] using (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt 0 hq'
  have hcurve := hopfCollar_time_hasDerivAt_of_orbit (freeHopfOldDimensions C) G (q z 0) y
    (hopfCollar_orbit_analyticAt (freeHopfOldDimensions C) r0 G hG.1 (q z 0) hr y 0)
  have hcomp := hcurve.scomp_of_eq 0 (hproj 0) (by rw [planarHopfFlow_zero])
  have h := selectorSnoc_hasDerivAt _ _ _ _ _ hcomp (hproj 1)
  have he : (fun t : ℝ ↦ selectorFromCollar C G q
      (freeHopfProductFlow C (Fin.last m) t x)) =
      fun t ↦ selectorSnoc (G (q (planarHopfFlow t z) 0, y))
        (q (planarHopfFlow t z) 1) := by
    funext t
    simp only [selectorFromCollar, freeHopfProductSplit_flow_last, z, y]
  change deriv (fun t ↦ selectorFromCollar C G q
    (freeHopfProductFlow C (Fin.last m) t x)) 0 = _
  rw [he]
  exact h.deriv

/-- The same globally constructed selector has the full original partial Gram
I, including the mixed and last diagonal entries. Native collar old Gram,
old/r orthogonality and unit r-speed combine with the actual planar unit speed.
No metric conclusion is supplied as an additional hypothesis.
Source: cor:selector, lines580–581. -/
theorem selectorFromCollar_gram {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin N))
    (r0 : ℝ) (hG : AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G)
    (q : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hq : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ q)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow q z‖ = 1)
    (hrange : ∀ z, q z 0 ∈ Set.Ioo (-r0) r0) (x : FreeHopfProduct C) :
    Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i (selectorFromCollar C G q) x) = 1 := by
  let z := (freeHopfProductSplit C x).2
  let y := (freeHopfProductSplit C x).1
  have hprops := hG.2 (q z 0) (hrange z) y
  have hold (i : Fin m) := selectorFromCollar_deriv_old C G r0 hG q x (hrange z) i
  have hlast := selectorFromCollar_deriv_last C G r0 hG q hq x (hrange z)
  have hspeed : (orbitDeriv planarHopfFlow q z 0) ^ 2 +
      (orbitDeriv planarHopfFlow q z 1) ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ ↦ t ^ 2) (hunit z)
    rw [EuclideanSpace.real_norm_sq_eq] at h
    simpa only [Fin.sum_univ_two, one_pow] using h
  ext i j
  change inner ℝ (freeHopfDeriv C i (selectorFromCollar C G q) x)
    (freeHopfDeriv C j (selectorFromCollar C G q) x) =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i j
  refine Fin.lastCases ?_ (fun p ↦ ?_) i
  · refine Fin.lastCases ?_ (fun p ↦ ?_) j
    · rw [hlast, selectorSnoc_inner, inner_smul_left, inner_smul_right,
        real_inner_self_eq_norm_sq, hprops.2.2.1]
      simpa only [Matrix.one_apply, ite_true, mul_one, pow_two, conj_trivial] using hspeed
    · rw [hlast, hold p, selectorSnoc_inner, inner_smul_left,
        real_inner_comm _ (hopfCollarRDeriv G (q z 0) y), hprops.2.1 p]
      simp [eq_comm]
  · refine Fin.lastCases ?_ (fun q' ↦ ?_) j
    · rw [hold p, hlast, selectorSnoc_inner, inner_smul_right, hprops.2.1 p]
      simp
    · rw [hold p, hold q', selectorSnoc_inner]
      have h := congrArg (fun A : Matrix (Fin m) (Fin m) ℝ ↦ A p q') hprops.1
      simpa only [Matrix.gram_apply, Matrix.one_apply, Fin.castSucc_inj,
        mul_zero, add_zero] using h

/-- Every old second column of the same selector is precisely the corresponding
actual old collar second column with zero appended coordinate. The proof
differentiates the already proved first-column identity along an actual old flow.
Source: the true partial second-form columns in cor:selector, lines581–582. -/
theorem selectorFromCollar_second_old {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin N))
    (r0 : ℝ) (hG : AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G)
    (q : PlanarHopfSphere (C (Fin.last m)) → Planar) (x : FreeHopfProduct C)
    (hr : q (freeHopfProductSplit C x).2 0 ∈ Set.Ioo (-r0) r0) (i j : Fin m) :
    freeHopfDeriv C i.castSucc (freeHopfDeriv C j.castSucc (selectorFromCollar C G q)) x =
      selectorSnoc (freeHopfDeriv (freeHopfOldDimensions C) i
        (freeHopfDeriv (freeHopfOldDimensions C) j
          (fun y ↦ G (q (freeHopfProductSplit C x).2 0, y)))
        (freeHopfProductSplit C x).1) 0 := by
  have hs := selector_collar_slice_contMDiff (freeHopfOldDimensions C) G r0 hG _ hr
  have hj := contMDiff_orbitDeriv (freeHopfProductFlow (freeHopfOldDimensions C) j)
    (freeHopfProductFlow_contMDiff (freeHopfOldDimensions C) j) _ hs
  change ContMDiff (freeHopfModel (freeHopfOldDimensions C))
    𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freeHopfDeriv (freeHopfOldDimensions C) j
      (fun y ↦ G (q (freeHopfProductSplit C x).2 0, y))) at hj
  have hd := hasDerivAt_orbit (freeHopfProductFlow (freeHopfOldDimensions C) i)
    (freeHopfProductFlow_contMDiff (freeHopfOldDimensions C) i)
    (freeHopfProductFlow_add (freeHopfOldDimensions C) i) _ hj 0
    (freeHopfProductSplit C x).1
  have h := selectorSnoc_hasDerivAt _ (fun _ : ℝ ↦ (0 : ℝ)) _ 0 0 hd
    (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have he : (fun t : ℝ ↦ freeHopfDeriv C j.castSucc (selectorFromCollar C G q)
      (freeHopfProductFlow C i.castSucc t x)) =
      fun t ↦ selectorSnoc
        (freeHopfDeriv (freeHopfOldDimensions C) j
          (fun y ↦ G (q (freeHopfProductSplit C x).2 0, y))
          (freeHopfProductFlow (freeHopfOldDimensions C) i t
            (freeHopfProductSplit C x).1)) 0 := by
    funext t
    have hr' : q (freeHopfProductSplit C (freeHopfProductFlow C i.castSucc t x)).2 0 ∈
        Set.Ioo (-r0) r0 := by
      simpa only [freeHopfProductSplit_flow_old] using hr
    simpa only [freeHopfProductSplit_flow_old] using
      selectorFromCollar_deriv_old C G r0 hG q
        (freeHopfProductFlow C i.castSucc t x) hr' j
  change deriv (fun t ↦ freeHopfDeriv C j.castSucc (selectorFromCollar C G q)
    (freeHopfProductFlow C i.castSucc t x)) 0 = _
  rw [he]
  simpa only [freeHopfProductFlow_zero, freeHopfDeriv] using h.deriv

/-- The actual old sorted second columns of this same selector are independent.
Project away only the appended target coordinate and reuse the original collar's
joint square-column independence on its actual second-column subfamily.
This lemma is an intermediate; the true Sym² injectivity still requires the
proved canonical second-form identification above and quotient algebra.
Source: cor:selector, lines581–582. -/
theorem selectorFromCollar_old_second_independent {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin N))
    (r0 : ℝ) (hG : AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G)
    (q : PlanarHopfSphere (C (Fin.last m)) → Planar) (x : FreeHopfProduct C)
    (hr : q (freeHopfProductSplit C x).2 0 ∈ Set.Ioo (-r0) r0) :
    LinearIndependent ℝ (fun ij : {p : Fin m × Fin m // p.1 ≤ p.2} ↦
      freeHopfDeriv C ij.val.1.castSucc
        (freeHopfDeriv C ij.val.2.castSucc (selectorFromCollar C G q)) x) := by
  let L : EuclideanSpace ℝ (Fin (N + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) :=
    { toFun := fun v ↦ WithLp.toLp 2 (fun i ↦ v i.castSucc)
      map_add' := by intro v w; ext i; rfl
      map_smul' := by intro r v; ext i; rfl }
  have hL (v : EuclideanSpace ℝ (Fin N)) : L (selectorSnoc v 0) = v := by
    ext i
    exact Fin.snoc_castSucc (α := fun _ : Fin (N + 1) ↦ ℝ) 0 (fun i ↦ v i) i
  apply LinearIndependent.of_comp L
  have hli := (hG.2 _ hr (freeHopfProductSplit C x).1).2.2.2
  have hsub := hli.comp
    (fun ij : {p : Fin m × Fin m // p.1 ≤ p.2} ↦ Sum.inr (Sum.inr ij))
    (by intro i j hij; simpa only [Sum.inr.injEq] using hij)
  have he : (L ∘ fun ij : {p : Fin m × Fin m // p.1 ≤ p.2} ↦
      freeHopfDeriv C ij.val.1.castSucc
        (freeHopfDeriv C ij.val.2.castSucc (selectorFromCollar C G q)) x) =
      (hopfCollarSquareColumns (freeHopfOldDimensions C) G
        (q (freeHopfProductSplit C x).2 0) (freeHopfProductSplit C x).1 ∘
        fun ij : {p : Fin m × Fin m // p.1 ≤ p.2} ↦ Sum.inr (Sum.inr ij)) := by
    funext ij
    change L (freeHopfDeriv C ij.val.1.castSucc
      (freeHopfDeriv C ij.val.2.castSucc (selectorFromCollar C G q)) x) = _
    rw [selectorFromCollar_second_old C G r0 hG q x hr, hL]
    rfl
  rw [he]
  exact hsub

/-- Every old second column of the actual same collar selector is in its true
partial normal space. Old tangent pairings use the cyclic identity; the last
tangent pairing directly consumes W2's accepted same-collar radial orthogonality.
No time/Y mixed derivative is reproved here.
Source: cor:selector, lines581–582. -/
theorem selectorFromCollar_old_second_normal {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin N))
    (r0 : ℝ) (hG : AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G)
    (q : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hq : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ q)
    (hrange : ∀ z, q z 0 ∈ Set.Ioo (-r0) r0) (x : FreeHopfProduct C) (i j : Fin m) :
    freeHopfDeriv C i.castSucc (freeHopfDeriv C j.castSucc (selectorFromCollar C G q)) x ∈
      normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))))
        (selectorFromCollar C G q ∘ freeHopfOrbitLift C x) 0 := by
  let r := q (freeHopfProductSplit C x).2 0
  let y := (freeHopfProductSplit C x).1
  have hr : r ∈ Set.Ioo (-r0) r0 := hrange _
  have hS := selectorFromCollar_contMDiff C G r0 hG q hq hrange
  have hs := selector_collar_slice_contMDiff (freeHopfOldDimensions C) G r0 hG r hr
  have hpair (k : Fin (m + 1)) :
      inner ℝ (freeHopfDeriv C i.castSucc
          (freeHopfDeriv C j.castSucc (selectorFromCollar C G q)) x)
        (freeHopfDeriv C k (selectorFromCollar C G q) x) = 0 := by
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · rw [selectorFromCollar_second_old C G r0 hG q x hr,
        selectorFromCollar_deriv_last C G r0 hG q hq x hr, selectorSnoc_inner,
        inner_smul_right]
      have hn := hopfCollar_r_second_inner_eq_zero (freeHopfOldDimensions C) r0 G hG r hr y i j
      simpa only [real_inner_comm, mul_zero, zero_mul, add_zero] using
        congrArg (fun t : ℝ ↦ orbitDeriv planarHopfFlow q (freeHopfProductSplit C x).2 0 * t) hn
    · rw [selectorFromCollar_second_old C G r0 hG q x hr,
        selectorFromCollar_deriv_old C G r0 hG q x hr k, selectorSnoc_inner]
      simpa only [mul_zero, add_zero] using
        selector_second_inner_first_eq_zero (freeHopfOldDimensions C) (fun z ↦ G (r, z)) hs
          (fun z ↦ (hG.2 r hr z).1) y i j k
  rw [selector_orbitLeaf_normalSpace C _ hS x, Submodule.mem_orthogonal']
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨k, rfl⟩ := hv; exact hpair k
  | zero => simp
  | add v w _ _ hv hw => simp only [inner_add_right, hv, hw, add_zero]
  | smul r v _ hv => simp only [inner_smul_right, hv, mul_zero]

theorem selector_symSquare_ext_basis {m : ℕ}
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q R : SymmetricSquare (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] W)
    (h : ∀ i j, Q (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      R (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) : Q = R := by
  have hbil : (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))).compr₂ Q =
      (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))).compr₂ R := by
    apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
    intro i
    apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
    intro j
    simpa only [LinearMap.compr₂_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply] using h i j
  apply (symmetricSquareRelations (EuclideanSpace ℝ (Fin m))).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  exact congrArg (fun β : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] W ↦ β v w) hbil

private theorem selector_symSquare_injective_of_basis_columns {m : ℕ}
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q : SymmetricSquare (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] W)
    (hQ : LinearIndependent ℝ (fun ij : {p : Fin m × Fin m // p.1 ≤ p.2} ↦
      Q (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single ij.val.1 1) (EuclideanSpace.single ij.val.2 1)))) :
    Function.Injective Q := by
  let v := fun ij : {p : Fin m × Fin m // p.1 ≤ p.2} ↦
    symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace.single ij.val.1 1) (EuclideanSpace.single ij.val.2 1)
  let L₀ := (Module.Basis.span hQ).constr ℝ v
  obtain ⟨L, hL⟩ := L₀.exists_extend
  have hsorted (ij : {p : Fin m × Fin m // p.1 ≤ p.2}) : L (Q (v ij)) = v ij := by
    have h := LinearMap.congr_fun hL (Module.Basis.span hQ ij)
    have hc : (Submodule.span ℝ (Set.range (fun ij ↦ Q (v ij)))).subtype
        (Module.Basis.span hQ ij) = Q (v ij) := Module.Basis.coe_span_apply hQ ij
    change L ((Submodule.span ℝ (Set.range (fun ij ↦ Q (v ij)))).subtype
      (Module.Basis.span hQ ij)) = L₀ (Module.Basis.span hQ ij) at h
    rw [hc] at h
    simpa only [L₀, Module.Basis.constr_basis] using h
  have hbasis (i j : Fin m) :
      L (Q (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) =
      symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    by_cases hij : i ≤ j
    · exact hsorted ⟨(i, j), hij⟩
    · rw [symmetricSquareProduct_comm (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]
      exact hsorted ⟨(j, i), le_of_not_ge hij⟩
  have hcomp : L.comp Q = LinearMap.id :=
    selector_symSquare_ext_basis _ _ hbasis
  have hleft : Function.LeftInverse L Q := fun v ↦ LinearMap.congr_fun hcomp v
  exact hleft.injective

/-- The actual old-coordinate inclusion into the tangent of the genuine
(m+1)-dimensional orbit leaf at zero. It appends the literal zero coordinate and
uses the canonical normed-space tangent identification, with no new carrier.
Source: Sym² span(Y_1,...,Y_m) in cor:selector, lines570–572. -/
def selectorOldTangentInclusion (m : ℕ) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
      (0 : EuclideanSpace ℝ (Fin (m + 1))) where
  toFun v := (NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin (m + 1)))).symm
    (selectorSnoc v 0)
  map_add' v w := by
    change selectorSnoc (v + w) 0 = selectorSnoc v 0 + selectorSnoc w 0
    ext j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j <;> simp [selectorSnoc]
  map_smul' r v := by
    change selectorSnoc (r • v) 0 = r • selectorSnoc v 0
    ext j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j <;> simp [selectorSnoc]

/-- Each old coordinate vector is included as its actual original coordinate
vector in the same orbit leaf, with zero final coordinate.
Source: the old generator inclusion in cor:selector, lines570–572. -/
theorem selectorOldTangentInclusion_single (m : ℕ) (i : Fin m) :
    selectorOldTangentInclusion m (EuclideanSpace.single i 1) =
      (NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin (m + 1)))).symm
        (EuclideanSpace.single i.castSucc 1) := by
  change selectorSnoc (EuclideanSpace.single i 1) 0 = EuclideanSpace.single i.castSucc 1
  ext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j <;> simp [selectorSnoc, EuclideanSpace.single]

/-- The true partial second form restricted to the old coordinates, followed
only by the actual normal-space inclusion into the original Euclidean target.
Its data are the existing trueSecondForm on the same genuine multi-orbit leaf
and the existing exact symmetric-square functor of the old inclusion.
Source: the restricted true partial form in cor:selector, lines570–572. -/
def selectorOldSecondForm {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (x : FreeHopfProduct C) : SymmetricSquare (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin N) :=
  (normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))))
    (S ∘ freeHopfOrbitLift C x) 0).subtype.comp
      ((trueSecondForm (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))))
        (S ∘ freeHopfOrbitLift C x) (hS.comp (freeHopfOrbitLift_contMDiff C x)) 0).comp
          (symmetricSquareLinearMap (selectorOldTangentInclusion m)))

private theorem selectorOldSecondForm_basis_product_projected {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (x : FreeHopfProduct C) (i j : Fin m) :
    selectorOldSecondForm C S hS x
        (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      (normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))))
        (S ∘ freeHopfOrbitLift C x) 0).starProjection
          (freeHopfDeriv C i.castSucc (freeHopfDeriv C j.castSucc S) x) := by
  have hmap : symmetricSquareLinearMap (selectorOldTangentInclusion m)
      (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      symmetricSquareProduct (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
        (0 : EuclideanSpace ℝ (Fin (m + 1))))
        (selectorOldTangentInclusion m (EuclideanSpace.single i 1))
        (selectorOldTangentInclusion m (EuclideanSpace.single j 1)) :=
    symmetricBilinearDescend_product _ _ _ _
  simp only [selectorOldSecondForm, LinearMap.comp_apply]
  rw [hmap, selectorOldTangentInclusion_single, selectorOldTangentInclusion_single]
  exact selector_orbitLeaf_secondForm_product C S hS x i.castSucc j.castSucc

/-- With actual Gram I, the actual restricted true partial second form takes
each canonical old symmetric product to its literal old second column.
Source: the true second-form identification in cor:selector, lines581–582. -/
theorem selectorOldSecondForm_basis_product {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hGram : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S x) = 1)
    (x : FreeHopfProduct C) (i j : Fin m) :
    selectorOldSecondForm C S hS x
        (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      freeHopfDeriv C i.castSucc (freeHopfDeriv C j.castSucc S) x := by
  rw [selectorOldSecondForm_basis_product_projected C S hS x i j]
  exact Submodule.starProjection_eq_self_iff.mpr
    (selector_second_mem_orbitLeaf_normalSpace C S hS hGram x i.castSucc j.castSucc)

/-- The actual restricted true partial second form of the same collar selector
is injective on the entire exact old symmetric square, including all diagonal
products. The preceding true-form identification and actual column independence
are combined by native linear extension and quotient extensionality.
Source: cor:selector, lines570–572 and581–582. -/
theorem selectorFromCollar_oldSecondForm_injective {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin N))
    (r0 : ℝ) (hG : AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G)
    (q : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hq : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ q)
    (_hunit : ∀ z, ‖orbitDeriv planarHopfFlow q z‖ = 1)
    (hrange : ∀ z, q z 0 ∈ Set.Ioo (-r0) r0) (x : FreeHopfProduct C) :
    Function.Injective (selectorOldSecondForm C (selectorFromCollar C G q)
      (selectorFromCollar_contMDiff C G r0 hG q hq hrange) x) := by
  apply selector_symSquare_injective_of_basis_columns
  have he : (fun ij : {p : Fin m × Fin m // p.1 ≤ p.2} ↦
      selectorOldSecondForm C (selectorFromCollar C G q)
        (selectorFromCollar_contMDiff C G r0 hG q hq hrange) x
          (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
            (EuclideanSpace.single ij.val.1 1) (EuclideanSpace.single ij.val.2 1))) =
      fun ij : {p : Fin m × Fin m // p.1 ≤ p.2} ↦
        freeHopfDeriv C ij.val.1.castSucc
          (freeHopfDeriv C ij.val.2.castSucc (selectorFromCollar C G q)) x := by
    funext ij
    rw [selectorOldSecondForm_basis_product_projected C _ _ x ij.val.1 ij.val.2]
    exact Submodule.starProjection_eq_self_iff.mpr
      (selectorFromCollar_old_second_normal C G r0 hG q hq hrange x ij.val.1 ij.val.2)
  rw [he]
  exact selectorFromCollar_old_second_independent C G r0 hG q x (hrange _)

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance selectorSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance selectorSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The same actual restricted partial second form is an operator field with
the canonical Hilbert tensor quotient norm on the old symmetric square. Its
continuity follows from actual smooth Hopf second columns and finite quotient
generation; no moving normal-space norm or arbitrary norm is substituted.
Source: the compact uniform-bound step in cor:selector, lines582–584. -/
theorem selectorOldSecondForm_continuous {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hGram : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S x) = 1) :
    Continuous (fun x ↦ (selectorOldSecondForm C S hS x).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  have hs (i : Fin (m + 1)) : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freeHopfDeriv C i S) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C i) (freeHopfProductFlow_contMDiff C i) S hS
  have hcol (i j : Fin m) : Continuous (fun x ↦ selectorOldSecondForm C S hS x
      (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) := by
    have he : (fun x ↦ selectorOldSecondForm C S hS x
        (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) =
        fun x ↦ freeHopfDeriv C i.castSucc (freeHopfDeriv C j.castSucc S) x :=
      funext (fun x ↦ selectorOldSecondForm_basis_product C S hS hGram x i j)
    rw [he]
    exact (contMDiff_orbitDeriv (freeHopfProductFlow C i.castSucc)
      (freeHopfProductFlow_contMDiff C i.castSucc) _ (hs j.castSucc)).continuous
  intro u
  refine Submodule.Quotient.induction_on _ u (fun z ↦ ?_)
  change Continuous (fun x ↦ selectorOldSecondForm C S hS x
    (symmetricSquareQuotient (EuclideanSpace ℝ (Fin m)) z))
  induction z using TensorProduct.inductionOn with
  | tmul v w =>
    change Continuous (fun x ↦ selectorOldSecondForm C S hS x
      (symmetricSquareProduct (EuclideanSpace ℝ (Fin m)) v w))
    let b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    rw [← b.sum_repr v, ← b.sum_repr w]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    apply continuous_finsetSum
    intro i _
    apply Continuous.fun_const_smul
    apply continuous_finsetSum
    intro j _
    apply Continuous.fun_const_smul
    simpa only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hcol j i
  | add z w hz hw =>
    simpa only [map_add] using hz.fun_add hw

/-- One positive uniform lower bound holds for the same actual restricted true
partial second form in the original canonical symmetric-square quotient norm.
Apply the accepted compact injective bound in actual finite Euclidean coordinates,
then use the actual coordinate inverse's operator norm to return to the original
quotient norm. No auxiliary Euclidean norm is asserted equal to the quotient norm.
Source: the uniform minimum singular value in cor:selector, lines570–572 and582–584. -/
theorem selectorFromCollar_oldSecondForm_uniform_bound {m N : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)]
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin N))
    (r0 : ℝ) (hG : AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G)
    (q : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hq : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ q)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow q z‖ = 1)
    (hrange : ∀ z, q z 0 ∈ Set.Ioo (-r0) r0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x v, ε * ‖v‖ ≤
      ‖selectorOldSecondForm C (selectorFromCollar C G q)
        (selectorFromCollar_contMDiff C G r0 hG q hq hrange) x v‖ := by
  let V := SymmetricSquare (EuclideanSpace ℝ (Fin m))
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let e : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E])
  let hS := selectorFromCollar_contMDiff C G r0 hG q hq hrange
  let A : FreeHopfProduct C → E →L[ℝ] EuclideanSpace ℝ (Fin (N + 1)) := fun x ↦
    (selectorOldSecondForm C (selectorFromCollar C G q) hS x).toContinuousLinearMap.comp
      e.symm.toContinuousLinearMap
  have hA : Continuous A := by
    apply continuous_clm_apply.mpr
    intro v
    exact (selectorOldSecondForm_continuous C (selectorFromCollar C G q) hS
      (selectorFromCollar_gram C G r0 hG q hq hunit hrange)).clm_apply continuous_const
  have hinj (x : FreeHopfProduct C) : Function.Injective (A x) :=
    (selectorFromCollar_oldSecondForm_injective C G r0 hG q hq hunit hrange x).comp
      e.symm.injective
  obtain ⟨ε, hε, hbound⟩ := selector_compact_injective_bound A hA hinj
  let B := max 1 ‖e.symm.toContinuousLinearMap‖
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨ε / B, div_pos hε hB, ?_⟩
  intro x v
  have hcoords : ‖v‖ ≤ B * ‖e v‖ := by
    calc
      ‖v‖ = ‖e.symm (e v)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e v‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B * ‖e v‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have hb : ε * ‖e v‖ ≤ ‖selectorOldSecondForm C (selectorFromCollar C G q) hS x v‖ := by
    simpa only [A, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using hbound x (e v)
  calc
    ε / B * ‖v‖ ≤ ε / B * (B * ‖e v‖) :=
      mul_le_mul_of_nonneg_left hcoords (div_nonneg hε.le hB.le)
    _ = ε * ‖e v‖ := by field_simp
    _ ≤ ‖selectorOldSecondForm C (selectorFromCollar C G q) hS x v‖ := hb

/-- The source-faithful selector construction from an actual native collar.
All original dimensions satisfy C_i≥2 and n=m+1≥2. The planar selector is supplied
internally by the accepted original planar theorem, and a single power K puts
its first coordinate in the common collar. The same single map has full Gram I,
true old symmetric-square injectivity and one positive original-norm bound.

This is a genuine intermediate, not the original cor:selector: the original
target must still internally construct its actual collar from prop:collar.
Source: the complete construction in cor:selector, lines565–584. -/
theorem whole_product_selector_from_actual_collar (m : ℕ) (_hm : 1 ≤ m)
    (C : Fin (m + 1) → ℕ) (hC : ∀ i, 2 ≤ C i) (r0 : ℝ) (hr0 : 0 < r0)
    (G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) →
      EuclideanSpace ℝ (Fin (symmetricTensorDimension m + m + 1))) :
    letI : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have h := hC i; omega⟩
    AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G →
      ∃ S : FreeHopfProduct C → EuclideanSpace ℝ (Fin (closedAmbientDimension (m + 1))),
      ∃ hS : ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (closedAmbientDimension (m + 1)))) ∞ S,
        (∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S x) = 1) ∧
        (∀ x, Function.Injective (selectorOldSecondForm C S hS x)) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ x v, ε * ‖v‖ ≤ ‖selectorOldSecondForm C S hS x v‖ := by
  let : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have h := hC i; omega⟩
  intro hG
  obtain ⟨p, κ, hp, hunit, _⟩ := planar_hopf_selector (C (Fin.last m)) (hC (Fin.last m))
  obtain ⟨q, hq, hqunit, hsmall⟩ := selector_small_planar_exists p hp hunit (r0 / 2)
    (by positivity)
  have hrange (z : PlanarHopfSphere (C (Fin.last m))) : q z 0 ∈ Set.Ioo (-r0) r0 := by
    have hc : |q z 0| ≤ ‖q z‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (q z) 0
    have hr : |q z 0| < r0 := lt_trans (lt_of_le_of_lt hc (hsmall z)) (by linarith)
    exact abs_lt.mp hr
  have hdim : closedAmbientDimension (m + 1) =
      (symmetricTensorDimension m + m + 1) + 1 := by
    simp only [closedAmbientDimension, symmetricTensorDimension]
    have hprod : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * m + 2 := by ring
    omega
  rw [hdim]
  exact ⟨selectorFromCollar C G q, selectorFromCollar_contMDiff C G r0 hG q hq hrange,
    selectorFromCollar_gram C G r0 hG q hq hqunit hrange,
    selectorFromCollar_oldSecondForm_injective C G r0 hG q hq hqunit hrange,
    selectorFromCollar_oldSecondForm_uniform_bound C G r0 hG q hq hqunit hrange⟩

/-- The literal coordinate-subsphere inclusion for any injection of the complex
coordinates. Native PiLp extension by zero supplies the actual complex Euclidean
isometry; the existing native sphere is retained verbatim.
Source: literal coordinate-subsphere restrictions in cor:selector, line572. -/
def selectorHopfCoordinateInclusion {smallDim C : ℕ} (e : Fin smallDim ↪ Fin C)
    (z : PlanarHopfSphere smallDim) : PlanarHopfSphere C :=
  ⟨LinearIsometry.piLpExtendByZero 2 ℂ ℂ e (z : PlanarHopfAmbient smallDim),
    mem_sphere_zero_iff_norm.mpr ((LinearIsometry.piLpExtendByZero 2 ℂ ℂ e).norm_map _ |>.trans
      (mem_sphere_zero_iff_norm.mp z.property))⟩

/-- Every literal coordinate-subsphere inclusion is native smooth for the
existing sphere atlases, by the native sphere codomain criterion and the actual
real restriction of the complex linear isometry.
Source: coordinate-subsphere restrictions in cor:selector, line572. -/
theorem selectorHopfCoordinateInclusion_contMDiff {smallDim C : ℕ}
    [Fact (0 < smallDim)] [Fact (0 < C)] (e : Fin smallDim ↪ Fin C) :
    ContMDiff (planarHopfModel smallDim) (planarHopfModel C) ∞
      (selectorHopfCoordinateInclusion e) := by
  apply ContMDiff.codRestrict_sphere
  intro z
  exact ((LinearIsometry.piLpExtendByZero 2 ℂ ℂ e).toContinuousLinearMap.restrictScalars ℝ
    |>.contDiff.contMDiff.contMDiffAt).comp z (planarHopfSphere_contMDiff_coe smallDim z)

/-- The same literal coordinate inclusion intertwines the original period-one
Hopf actions exactly, since complex coordinate extension is complex linear.
Source: coordinate-subsphere invariance in cor:selector, line572. -/
theorem selectorHopfCoordinateInclusion_flow {smallDim C : ℕ} (e : Fin smallDim ↪ Fin C)
    (t : ℝ) (z : PlanarHopfSphere smallDim) :
    selectorHopfCoordinateInclusion e (planarHopfFlow t z) =
      planarHopfFlow t (selectorHopfCoordinateInclusion e z) := by
  apply Subtype.ext
  change LinearIsometry.piLpExtendByZero 2 ℂ ℂ e
      ((Circle.exp (2 * Real.pi * t) : ℂ) • (z : PlanarHopfAmbient smallDim)) =
    (Circle.exp (2 * Real.pi * t) : ℂ) •
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ e (z : PlanarHopfAmbient smallDim)
  exact (LinearIsometry.piLpExtendByZero 2 ℂ ℂ e).map_smul _ _

/-- The literal product of actual coordinate-subsphere inclusions, with the same
number and ordering of factors as the original whole Hopf product.
Source: all literal coordinate-subsphere restrictions in cor:selector, line572. -/
def selectorProductCoordinateInclusion {a : ℕ} (smallC C : Fin a → ℕ)
    (e : ∀ i, Fin (smallC i) ↪ Fin (C i)) (x : FreeHopfProduct smallC) :
    FreeHopfProduct C := fun i ↦ selectorHopfCoordinateInclusion (e i) (x i)

/-- The actual product coordinate inclusion is native smooth, by the existing
finite-product model and the proved native factor inclusions.
Source: coordinate-subsphere restrictions in cor:selector, line572. -/
theorem selectorProductCoordinateInclusion_contMDiff {a : ℕ} (smallC C : Fin a → ℕ)
    [∀ i, Fact (0 < smallC i)] [∀ i, Fact (0 < C i)]
    (e : ∀ i, Fin (smallC i) ↪ Fin (C i)) :
    ContMDiff (freeHopfModel smallC) (freeHopfModel C) ∞
      (selectorProductCoordinateInclusion smallC C e) := by
  rw [show freeHopfModel C = ModelWithCorners.pi (fun i ↦ planarHopfModel (C i)) from
    (free_finite_product_model_eq _).symm]
  exact contMDiff_pi_iff.mpr (fun i ↦ (selectorHopfCoordinateInclusion_contMDiff (e i)).comp
    (freeHopfProduct_contMDiff_apply smallC i))

/-- Each original period-one factor flow intertwines with the literal product
coordinate inclusion, without changing the flow time or choosing a new selector.
Source: coordinate-subsphere restrictions in cor:selector, line572. -/
theorem selectorProductCoordinateInclusion_flow {a : ℕ} (smallC C : Fin a → ℕ)
    (e : ∀ i, Fin (smallC i) ↪ Fin (C i)) (i : Fin a) (t : ℝ)
    (x : FreeHopfProduct smallC) :
    selectorProductCoordinateInclusion smallC C e (freeHopfProductFlow smallC i t x) =
      freeHopfProductFlow C i t (selectorProductCoordinateInclusion smallC C e x) := by
  funext j
  by_cases hji : j = i
  · subst j
    change selectorHopfCoordinateInclusion (e i) ((freeHopfProductFlow smallC i t x) i) = _
    rw [freeHopfProductFlow_apply, freeHopfProductFlow_apply]
    exact selectorHopfCoordinateInclusion_flow (e i) t (x i)
  · change selectorHopfCoordinateInclusion (e j) ((freeHopfProductFlow smallC i t x) j) = _
    rw [freeHopfProductFlow_apply_ne smallC i j hji, freeHopfProductFlow_apply_ne C i j hji]
    rfl

/-- Differentiating a literal restriction gives the literal restriction of the
original Hopf derivative. The real orbit curves are equal by the proved flow
intertwining, so this holds even without an additional smoothness hypothesis.
Source: literal coordinate restrictions in cor:selector, line572. -/
theorem selectorProductCoordinateInclusion_deriv {a N : ℕ} (smallC C : Fin a → ℕ)
    (e : ∀ i, Fin (smallC i) ↪ Fin (C i))
    (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N)) (i : Fin a)
    (x : FreeHopfProduct smallC) :
    freeHopfDeriv smallC i (S ∘ selectorProductCoordinateInclusion smallC C e) x =
      freeHopfDeriv C i S (selectorProductCoordinateInclusion smallC C e x) := by
  unfold freeHopfDeriv orbitDeriv
  congr 1
  funext t
  rw [Function.comp_apply, selectorProductCoordinateInclusion_flow]

/-- The same exact restriction identity holds for all ordered second columns,
including the diagonal columns, by applying the first identity twice.
Source: true partial second forms of literal restrictions in cor:selector, line572. -/
theorem selectorProductCoordinateInclusion_second {a N : ℕ} (smallC C : Fin a → ℕ)
    (e : ∀ i, Fin (smallC i) ↪ Fin (C i))
    (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N)) (i j : Fin a)
    (x : FreeHopfProduct smallC) :
    freeHopfDeriv smallC i
        (freeHopfDeriv smallC j (S ∘ selectorProductCoordinateInclusion smallC C e)) x =
      freeHopfDeriv C i (freeHopfDeriv C j S)
        (selectorProductCoordinateInclusion smallC C e x) := by
  have he : freeHopfDeriv smallC j (S ∘ selectorProductCoordinateInclusion smallC C e) =
      freeHopfDeriv C j S ∘ selectorProductCoordinateInclusion smallC C e :=
    funext (selectorProductCoordinateInclusion_deriv smallC C e S j)
  rw [he]
  exact selectorProductCoordinateInclusion_deriv smallC C e (freeHopfDeriv C j S) i x

/-- The partial Gram of every literal coordinate restriction is exactly the
restriction of the same original partial Gram, so full Gram I is retained.
Source: literal coordinate-subsphere restrictions in cor:selector, line572. -/
theorem selectorProductCoordinateInclusion_gram {a N : ℕ} (smallC C : Fin a → ℕ)
    (e : ∀ i, Fin (smallC i) ↪ Fin (C i))
    (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hGram : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S x) = 1)
    (x : FreeHopfProduct smallC) :
    Matrix.gram ℝ (fun i ↦ freeHopfDeriv smallC i
      (S ∘ selectorProductCoordinateInclusion smallC C e) x) = 1 := by
  ext i j
  simp only [Matrix.gram_apply, selectorProductCoordinateInclusion_deriv]
  exact congrArg (fun A : Matrix (Fin a) (Fin a) ℝ ↦ A i j)
    (hGram (selectorProductCoordinateInclusion smallC C e x))

/-- The entire true old partial second-form operator of a literal coordinate
restriction equals the restriction of the same original operator. Equality is
on the exact binary Sym² quotient, not merely on its listed raw columns.
Source: literal coordinate-subsphere restrictions in cor:selector, line572. -/
theorem selectorProductCoordinateInclusion_oldSecondForm {m N : ℕ}
    (smallC C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < smallC i)] [∀ i, Fact (0 < C i)]
    (e : ∀ i, Fin (smallC i) ↪ Fin (C i))
    (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hGram : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S x) = 1)
    (x : FreeHopfProduct smallC) :
    selectorOldSecondForm smallC (S ∘ selectorProductCoordinateInclusion smallC C e)
        (hS.comp (selectorProductCoordinateInclusion_contMDiff smallC C e)) x =
      selectorOldSecondForm C S hS (selectorProductCoordinateInclusion smallC C e x) := by
  apply selector_symSquare_ext_basis
  intro i j
  rw [selectorOldSecondForm_basis_product smallC _ _
      (selectorProductCoordinateInclusion_gram smallC C e S hGram) x i j,
    selectorOldSecondForm_basis_product C S hS hGram _ i j]
  exact selectorProductCoordinateInclusion_second smallC C e S i.castSucc j.castSucc x

/-- All literal coordinate restrictions retain the same global positive bound
and true old Sym² injectivity, by equality with the same original operator.
No selector or positive margin is selected again on a smaller product.
Source: all coordinate-subsphere restrictions in cor:selector, line572. -/
theorem selectorProductCoordinateInclusion_properties {m N : ℕ}
    (smallC C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < smallC i)] [∀ i, Fact (0 < C i)]
    (e : ∀ i, Fin (smallC i) ↪ Fin (C i))
    (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hGram : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S x) = 1)
    (hinj : ∀ x, Function.Injective (selectorOldSecondForm C S hS x))
    (ε : ℝ) (hbound : ∀ x v, ε * ‖v‖ ≤ ‖selectorOldSecondForm C S hS x v‖) :
    (∀ x, Function.Injective
      (selectorOldSecondForm smallC (S ∘ selectorProductCoordinateInclusion smallC C e)
        (hS.comp (selectorProductCoordinateInclusion_contMDiff smallC C e)) x)) ∧
    ∀ x v, ε * ‖v‖ ≤ ‖selectorOldSecondForm smallC
      (S ∘ selectorProductCoordinateInclusion smallC C e)
        (hS.comp (selectorProductCoordinateInclusion_contMDiff smallC C e)) x v‖ := by
  constructor
  · intro x
    rw [selectorProductCoordinateInclusion_oldSecondForm smallC C e S hS hGram x]
    exact hinj _
  · intro x v
    rw [selectorProductCoordinateInclusion_oldSecondForm smallC C e S hS hGram x]
    exact hbound _ v

end GlobalEmbedding.Paper
