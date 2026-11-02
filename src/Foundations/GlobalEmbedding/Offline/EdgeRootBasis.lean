import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

open Finset LinearMap
open scoped BigOperators

/-!
# The normalized edge-root rank-one basis

This is the explicit algebraic construction in the positive-dictionary paragraph of
`literature/parallelizable-stable-plus-one/main.tex`.  All forms below are native real
bilinear forms on the actual zero-sum subspace of `Fin m → ℝ`.  The coordinate dot form
is used algebraically; no ambient analytic norm or metric is replaced.

Off-diagonal entries recover every edge coefficient, so both independence and spanning
are proved rather than supplied.  Normalization by `sqrt m` makes the identity coefficients
exactly one.  The cardinality and the dimension of the zero-sum space are also proved.
-/

namespace GlobalEmbedding.Offline

abbrev EdgePair (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}

noncomputable def edgeCovector (m : ℕ) (e : EdgePair m) : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj e.val.1 : (Fin m → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj e.val.2

@[simp] theorem edgeCovector_apply (m : ℕ) (e : EdgePair m) (x : Fin m → ℝ) :
    edgeCovector m e x = x e.val.1 - x e.val.2 := rfl

noncomputable def edgeBilinForm (m : ℕ) (e : EdgePair m) :
    LinearMap.BilinForm ℝ (Fin m → ℝ) :=
  LinearMap.BilinForm.linMulLin (edgeCovector m e) (edgeCovector m e)

@[simp] theorem edgeBilinForm_apply (m : ℕ) (e : EdgePair m) (x y : Fin m → ℝ) :
    edgeBilinForm m e x y = (x e.val.1 - x e.val.2) * (y e.val.1 - y e.val.2) := rfl

noncomputable def weightedEdgeBilinForm (m : ℕ) (a : EdgePair m → ℝ) :
    LinearMap.BilinForm ℝ (Fin m → ℝ) := ∑ e, a e • edgeBilinForm m e

@[simp] theorem weightedEdgeBilinForm_apply (m : ℕ) (a : EdgePair m → ℝ)
    (x y : Fin m → ℝ) :
    weightedEdgeBilinForm m a x y =
      ∑ e, a e * (x e.val.1 - x e.val.2) * (y e.val.1 - y e.val.2) := by
  simp [weightedEdgeBilinForm, smul_eq_mul, mul_assoc]

theorem weightedEdgeBilinForm_offdiag (m : ℕ) (a : EdgePair m → ℝ)
    (i j : Fin m) (hij : i < j) :
    weightedEdgeBilinForm m a (Pi.single i 1) (Pi.single j 1) = -a ⟨(i,j), hij⟩ := by
  classical
  rw [weightedEdgeBilinForm_apply]
  rw [Finset.sum_eq_single ⟨(i,j), hij⟩]
  · simp [ne_of_lt hij, (ne_of_lt hij).symm]
  · rintro ⟨⟨l,r⟩, hlr⟩ _ hne
    dsimp only
    by_cases hli : l = i <;> by_cases hri : r = i <;>
      by_cases hlj : l = j <;> by_cases hrj : r = j
    all_goals simp [Pi.single_apply, hli, hri, hlj, hrj, eq_comm]
    all_goals try omega
    all_goals subst_vars
    all_goals first | exact (hne rfl).elim | exact (lt_asymm hlr hij).elim
  · simp

noncomputable def coordinateSum (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, LinearMap.proj i

@[simp] theorem coordinateSum_apply (m : ℕ) (x : Fin m → ℝ) :
    coordinateSum m x = ∑ i, x i := by simp [coordinateSum]

noncomputable def zeroSumSpace (m : ℕ) : Submodule ℝ (Fin m → ℝ) := (coordinateSum m).ker

@[simp] theorem mem_zeroSumSpace (m : ℕ) (x : Fin m → ℝ) :
    x ∈ zeroSumSpace m ↔ ∑ i, x i = 0 := by simp [zeroSumSpace]

noncomputable def centerToZeroSum (m : ℕ) (hm : m ≠ 0) :
    (Fin m → ℝ) →ₗ[ℝ] zeroSumSpace m where
  toFun x := ⟨fun i ↦ x i - (∑ j, x j) / m, by
    rw [mem_zeroSumSpace]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp
    ring⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    dsimp
    ring
  map_smul' c x := by
    apply Subtype.ext
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    dsimp
    ring

@[simp] theorem centerToZeroSum_apply (m : ℕ) (hm : m ≠ 0) (x : Fin m → ℝ) (i : Fin m) :
    (centerToZeroSum m hm x).val i = x i - (∑ j, x j) / m := rfl

theorem edgeCovector_center (m : ℕ) (hm : m ≠ 0) (e : EdgePair m) (x : Fin m → ℝ) :
    edgeCovector m e (centerToZeroSum m hm x) = edgeCovector m e x := by
  simp only [edgeCovector_apply, centerToZeroSum_apply]
  ring

theorem weightedEdgeBilinForm_center (m : ℕ) (hm : m ≠ 0) (a : EdgePair m → ℝ)
    (x y : Fin m → ℝ) :
    weightedEdgeBilinForm m a (centerToZeroSum m hm x) (centerToZeroSum m hm y) =
      weightedEdgeBilinForm m a x y := by
  simp only [weightedEdgeBilinForm, LinearMap.sum_apply, LinearMap.smul_apply,
    edgeBilinForm, LinearMap.BilinForm.linMulLin_apply, edgeCovector_center]

noncomputable def restrictedEdgeBilinForm (m : ℕ) (e : EdgePair m) :
    LinearMap.BilinForm ℝ (zeroSumSpace m) := (edgeBilinForm m e).restrict (zeroSumSpace m)

theorem edgeBilinForm_restrict_linearIndependent (m : ℕ) (hm : m ≠ 0) :
    LinearIndependent ℝ (restrictedEdgeBilinForm m) := by
  classical
  let : AddCommGroup (zeroSumSpace m) := inferInstance
  let : Module ℝ (zeroSumSpace m) := inferInstance
  let : AddCommGroup (LinearMap.BilinForm ℝ (zeroSumSpace m)) := inferInstance
  let : Module ℝ (LinearMap.BilinForm ℝ (zeroSumSpace m)) := inferInstance
  apply (Fintype.linearIndependent_iff (R := ℝ) (v := restrictedEdgeBilinForm m)).mpr
  intro a ha e
  have h := congrArg (fun B : LinearMap.BilinForm ℝ (zeroSumSpace m) ↦
    B (centerToZeroSum m hm (Pi.single e.val.1 1))
      (centerToZeroSum m hm (Pi.single e.val.2 1))) ha
  have hzero : weightedEdgeBilinForm m a
      (centerToZeroSum m hm (Pi.single e.val.1 1))
      (centerToZeroSum m hm (Pi.single e.val.2 1)) = 0 := by
    simpa only [weightedEdgeBilinForm, restrictedEdgeBilinForm, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] using h
  rw [weightedEdgeBilinForm_center, weightedEdgeBilinForm_offdiag m a _ _ e.property] at hzero
  exact neg_eq_zero.mp hzero

theorem weightedEdgeBilinForm_isSymm (m : ℕ) (a : EdgePair m → ℝ) :
    (weightedEdgeBilinForm m a).IsSymm := by
  constructor
  intro x y
  simp only [weightedEdgeBilinForm_apply]
  apply Finset.sum_congr rfl
  intro e _
  ring

@[simp] theorem weightedEdgeBilinForm_const_right (m : ℕ) (a : EdgePair m → ℝ)
    (x : Fin m → ℝ) (c : ℝ) : weightedEdgeBilinForm m a x (fun _ ↦ c) = 0 := by
  simp only [weightedEdgeBilinForm_apply, sub_self, mul_zero, Finset.sum_const_zero]

noncomputable def coordinateDotBilinForm (m : ℕ) : LinearMap.BilinForm ℝ (Fin m → ℝ) :=
  ∑ i : Fin m, LinearMap.BilinForm.linMulLin
    (LinearMap.proj i : (Fin m → ℝ) →ₗ[ℝ] ℝ) (LinearMap.proj i)

@[simp] theorem coordinateDotBilinForm_apply (m : ℕ) (x y : Fin m → ℝ) :
    coordinateDotBilinForm m x y = ∑ i, x i * y i := by
  simp [coordinateDotBilinForm]

noncomputable def completeGraphBilinForm (m : ℕ) : LinearMap.BilinForm ℝ (Fin m → ℝ) :=
  (m : ℝ) • coordinateDotBilinForm m -
    LinearMap.BilinForm.linMulLin (coordinateSum m) (coordinateSum m)

@[simp] theorem completeGraphBilinForm_apply (m : ℕ) (x y : Fin m → ℝ) :
    completeGraphBilinForm m x y = (m : ℝ) * (∑ i, x i * y i) - (∑ i, x i) * (∑ i, y i) := by
  simp [completeGraphBilinForm, smul_eq_mul]

theorem completeGraphBilinForm_isSymm (m : ℕ) : (completeGraphBilinForm m).IsSymm := by
  constructor
  intro x y
  simp [mul_comm]

@[simp] theorem completeGraphBilinForm_const_right (m : ℕ) (x : Fin m → ℝ) :
    completeGraphBilinForm m x (fun _ ↦ 1) = 0 := by
  simp [completeGraphBilinForm_apply, mul_comm]

theorem completeGraphBilinForm_offdiag (m : ℕ) (i j : Fin m) (hij : i < j) :
    completeGraphBilinForm m (Pi.single i 1) (Pi.single j 1) = -1 := by
  have hdot : (∑ l : Fin m, (Pi.single i 1 : Fin m → ℝ) l *
      (Pi.single j 1 : Fin m → ℝ) l) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    by_cases hil : i = l
    · subst l
      simp [(ne_of_lt hij).symm]
    · simp [Pi.single_apply, hil]
  simp [completeGraphBilinForm_apply, hdot]

theorem bilinear_eq_of_offdiag_of_const
    (m : ℕ) (B C : LinearMap.BilinForm ℝ (Fin m → ℝ))
    (hB : B.IsSymm) (hC : C.IsSymm)
    (hBconst : ∀ x, B x (fun _ ↦ 1) = 0) (hCconst : ∀ x, C x (fun _ ↦ 1) = 0)
    (hoff : ∀ i j : Fin m, i < j → B (Pi.single i 1) (Pi.single j 1) =
      C (Pi.single i 1) (Pi.single j 1)) : B = C := by
  classical
  have hne (i j : Fin m) (hij : i ≠ j) : B (Pi.single i 1) (Pi.single j 1) =
      C (Pi.single i 1) (Pi.single j 1) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hoff i j h
    · rw [hB.eq, hC.eq]
      exact hoff j i h
  apply LinearMap.BilinForm.ext_basis (Pi.basisFun ℝ (Fin m))
  intro i j
  simp only [Pi.basisFun_apply]
  by_cases hij : i = j
  · subst j
    have hsumB : (∑ l : Fin m, B (Pi.single i 1) (Pi.single l 1)) = 0 := by
      rw [← map_sum, Finset.univ_sum_single]
      exact hBconst _
    have hsumC : (∑ l : Fin m, C (Pi.single i 1) (Pi.single l 1)) = 0 := by
      rw [← map_sum, Finset.univ_sum_single]
      exact hCconst _
    have hrest : (∑ l ∈ Finset.univ.erase i, B (Pi.single i 1) (Pi.single l 1)) =
        ∑ l ∈ Finset.univ.erase i, C (Pi.single i 1) (Pi.single l 1) := by
      apply Finset.sum_congr rfl
      intro l hl
      exact hne i l (Finset.ne_of_mem_erase hl).symm
    have hb := Finset.sum_erase_add Finset.univ
      (fun l : Fin m ↦ B (Pi.single i 1) (Pi.single l 1)) (Finset.mem_univ i)
    have hc := Finset.sum_erase_add Finset.univ
      (fun l : Fin m ↦ C (Pi.single i 1) (Pi.single l 1)) (Finset.mem_univ i)
    rw [hsumB] at hb
    rw [hsumC] at hc
    linarith
  · exact hne i j hij

theorem sum_edge_forms_complete_graph (m : ℕ) :
    weightedEdgeBilinForm m (fun _ ↦ 1) = completeGraphBilinForm m := by
  apply bilinear_eq_of_offdiag_of_const m _ _
    (weightedEdgeBilinForm_isSymm m _) (completeGraphBilinForm_isSymm m)
    (fun x ↦ weightedEdgeBilinForm_const_right m _ x 1)
    (completeGraphBilinForm_const_right m)
  intro i j hij
  rw [weightedEdgeBilinForm_offdiag m _ i j hij, completeGraphBilinForm_offdiag m i j hij]

theorem sum_edge_forms_on_zeroSum (m : ℕ) (x y : zeroSumSpace m) :
    (∑ e : EdgePair m, edgeBilinForm m e x y) =
      (m : ℝ) * (∑ i, x.val i * y.val i) := by
  have hx : ∑ i, x.val i = 0 := (mem_zeroSumSpace m _).mp x.property
  have hy : ∑ i, y.val i = 0 := (mem_zeroSumSpace m _).mp y.property
  have h := congrArg (fun B : LinearMap.BilinForm ℝ (Fin m → ℝ) ↦ B x y)
    (sum_edge_forms_complete_graph m)
  simpa [weightedEdgeBilinForm, completeGraphBilinForm_apply, hx, hy] using h

@[simp] theorem centerToZeroSum_coe (m : ℕ) (hm : m ≠ 0) (x : zeroSumSpace m) :
    centerToZeroSum m hm x = x := by
  apply Subtype.ext
  funext i
  have hx : ∑ j, x.val j = 0 := (mem_zeroSumSpace m _).mp x.property
  simp only [centerToZeroSum_apply, hx, zero_div, sub_zero]

@[simp] theorem centerToZeroSum_const_one (m : ℕ) (hm : m ≠ 0) :
    centerToZeroSum m hm (fun _ ↦ 1) = 0 := by
  apply Subtype.ext
  funext i
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  simp [centerToZeroSum_apply, hm']

noncomputable def centeredBilinExtension (m : ℕ) (hm : m ≠ 0)
    (B : LinearMap.BilinForm ℝ (zeroSumSpace m)) :
    LinearMap.BilinForm ℝ (Fin m → ℝ) :=
  B.comp (centerToZeroSum m hm) (centerToZeroSum m hm)

@[simp] theorem centeredBilinExtension_apply (m : ℕ) (hm : m ≠ 0)
    (B : LinearMap.BilinForm ℝ (zeroSumSpace m)) (x y : Fin m → ℝ) :
    centeredBilinExtension m hm B x y = B (centerToZeroSum m hm x) (centerToZeroSum m hm y) := rfl

theorem centeredBilinExtension_isSymm (m : ℕ) (hm : m ≠ 0)
    (B : LinearMap.BilinForm ℝ (zeroSumSpace m)) (hB : B.IsSymm) :
    (centeredBilinExtension m hm B).IsSymm :=
  ⟨fun _ _ ↦ hB.eq _ _⟩

@[simp] theorem centeredBilinExtension_const_right (m : ℕ) (hm : m ≠ 0)
    (B : LinearMap.BilinForm ℝ (zeroSumSpace m)) (x : Fin m → ℝ) :
    centeredBilinExtension m hm B x (fun _ ↦ 1) = 0 := by simp

noncomputable def edgeCoefficientLinear (m : ℕ) (hm : m ≠ 0) :
    LinearMap.BilinForm ℝ (zeroSumSpace m) →ₗ[ℝ] (EdgePair m → ℝ) where
  toFun B e := -B (centerToZeroSum m hm (Pi.single e.val.1 1))
    (centerToZeroSum m hm (Pi.single e.val.2 1))
  map_add' B C := by
    funext e
    simp only [LinearMap.add_apply, Pi.add_apply]
    ring
  map_smul' c B := by
    funext e
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem edgeCoefficientLinear_apply (m : ℕ) (hm : m ≠ 0)
    (B : LinearMap.BilinForm ℝ (zeroSumSpace m)) (e : EdgePair m) :
    edgeCoefficientLinear m hm B e = -B (centerToZeroSum m hm (Pi.single e.val.1 1))
      (centerToZeroSum m hm (Pi.single e.val.2 1)) := rfl

theorem weightedEdgeBilinForm_coefficients (m : ℕ) (hm : m ≠ 0)
    (B : LinearMap.BilinForm ℝ (zeroSumSpace m)) (hB : B.IsSymm) :
    weightedEdgeBilinForm m (edgeCoefficientLinear m hm B) = centeredBilinExtension m hm B := by
  apply bilinear_eq_of_offdiag_of_const m _ _ (weightedEdgeBilinForm_isSymm m _)
    (centeredBilinExtension_isSymm m hm B hB)
    (fun x ↦ weightedEdgeBilinForm_const_right m _ x 1)
    (centeredBilinExtension_const_right m hm B)
  intro i j hij
  rw [weightedEdgeBilinForm_offdiag m _ i j hij]
  simp

noncomputable def reconstructEdgeForm (m : ℕ) :
    (EdgePair m → ℝ) →ₗ[ℝ] LinearMap.BilinForm ℝ (zeroSumSpace m) where
  toFun a := ∑ e, a e • restrictedEdgeBilinForm m e
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem reconstructEdgeForm_apply (m : ℕ) (a : EdgePair m → ℝ)
    (x y : zeroSumSpace m) :
    reconstructEdgeForm m a x y = weightedEdgeBilinForm m a x y := by
  simp only [reconstructEdgeForm, weightedEdgeBilinForm, restrictedEdgeBilinForm,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]

theorem edgeCoefficientLinear_reconstruct (m : ℕ) (hm : m ≠ 0) (a : EdgePair m → ℝ) :
    edgeCoefficientLinear m hm (reconstructEdgeForm m a) = a := by
  funext e
  rw [edgeCoefficientLinear_apply, reconstructEdgeForm_apply, weightedEdgeBilinForm_center,
    weightedEdgeBilinForm_offdiag m a _ _ e.property, neg_neg]

theorem reconstructEdgeForm_coefficients (m : ℕ) (hm : m ≠ 0)
    (B : LinearMap.BilinForm ℝ (zeroSumSpace m)) (hB : B.IsSymm) :
    reconstructEdgeForm m (edgeCoefficientLinear m hm B) = B := by
  ext x y
  rw [reconstructEdgeForm_apply, weightedEdgeBilinForm_coefficients m hm B hB]
  simp

theorem edge_form_decomposition_unique (m : ℕ) (hm : m ≠ 0)
    (B : LinearMap.BilinForm ℝ (zeroSumSpace m)) (hB : B.IsSymm) :
    ∃! a : EdgePair m → ℝ, reconstructEdgeForm m a = B := by
  refine ⟨edgeCoefficientLinear m hm B, reconstructEdgeForm_coefficients m hm B hB, ?_⟩
  intro a ha
  have h := congrArg (edgeCoefficientLinear m hm) ha
  simpa only [edgeCoefficientLinear_reconstruct] using h

noncomputable def normalizedEdgeCovector (m : ℕ) (e : EdgePair m) :
    zeroSumSpace m →ₗ[ℝ] ℝ :=
  (Real.sqrt (m : ℝ))⁻¹ • (edgeCovector m e).domRestrict (zeroSumSpace m)

noncomputable def normalizedEdgeForm (m : ℕ) (e : EdgePair m) :
    LinearMap.BilinForm ℝ (zeroSumSpace m) :=
  LinearMap.BilinForm.linMulLin (normalizedEdgeCovector m e) (normalizedEdgeCovector m e)

theorem normalizedEdgeForm_eq_smul (m : ℕ) (e : EdgePair m) :
    normalizedEdgeForm m e = (m : ℝ)⁻¹ • restrictedEdgeBilinForm m e := by
  ext x y
  have hs : (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ = (m : ℝ)⁻¹ := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by positivity)]
  simp only [normalizedEdgeForm, normalizedEdgeCovector, LinearMap.BilinForm.linMulLin_apply,
    LinearMap.smul_apply, LinearMap.domRestrict_apply, smul_eq_mul,
    restrictedEdgeBilinForm, LinearMap.BilinForm.restrict_apply, edgeBilinForm_apply,
    edgeCovector_apply]
  calc
    _ = ((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹) *
        ((x.val e.val.1 - x.val e.val.2) * (y.val e.val.1 - y.val e.val.2)) := by ring
    _ = _ := by rw [hs]

noncomputable def normalizedEdgeReconstruct (m : ℕ) :
    (EdgePair m → ℝ) →ₗ[ℝ] LinearMap.BilinForm ℝ (zeroSumSpace m) :=
  (m : ℝ)⁻¹ • reconstructEdgeForm m

theorem normalizedEdgeReconstruct_eq_sum (m : ℕ) (a : EdgePair m → ℝ) :
    normalizedEdgeReconstruct m a = ∑ e, a e • normalizedEdgeForm m e := by
  simp only [normalizedEdgeReconstruct, LinearMap.smul_apply, reconstructEdgeForm,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum, normalizedEdgeForm_eq_smul]
  apply Finset.sum_congr rfl
  intro e _
  exact smul_comm _ _ _

noncomputable def normalizedEdgeCoefficientLinear (m : ℕ) (hm : m ≠ 0) :
    LinearMap.BilinForm ℝ (zeroSumSpace m) →ₗ[ℝ] (EdgePair m → ℝ) :=
  (m : ℝ) • edgeCoefficientLinear m hm

theorem normalizedEdgeCoefficient_reconstruct (m : ℕ) (hm : m ≠ 0) (a : EdgePair m → ℝ) :
    normalizedEdgeCoefficientLinear m hm (normalizedEdgeReconstruct m a) = a := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  simp only [normalizedEdgeCoefficientLinear, normalizedEdgeReconstruct,
    LinearMap.smul_apply, map_smul, edgeCoefficientLinear_reconstruct,
    smul_smul, inv_mul_cancel₀ hm', one_smul]

theorem normalizedEdgeReconstruct_coefficients (m : ℕ) (hm : m ≠ 0)
    (B : LinearMap.BilinForm ℝ (zeroSumSpace m)) (hB : B.IsSymm) :
    normalizedEdgeReconstruct m (normalizedEdgeCoefficientLinear m hm B) = B := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  simp only [normalizedEdgeCoefficientLinear, normalizedEdgeReconstruct,
    LinearMap.smul_apply, map_smul, reconstructEdgeForm_coefficients m hm B hB,
    smul_smul, mul_inv_cancel₀ hm', one_smul]

theorem normalizedEdgeForm_linearIndependent (m : ℕ) (hm : m ≠ 0) :
    LinearIndependent ℝ (normalizedEdgeForm m) := by
  classical
  let : AddCommGroup (zeroSumSpace m) := inferInstance
  let : Module ℝ (zeroSumSpace m) := inferInstance
  let : AddCommGroup (LinearMap.BilinForm ℝ (zeroSumSpace m)) := inferInstance
  let : Module ℝ (LinearMap.BilinForm ℝ (zeroSumSpace m)) := inferInstance
  apply (Fintype.linearIndependent_iff (R := ℝ) (v := normalizedEdgeForm m)).mpr
  intro a ha e
  rw [← normalizedEdgeReconstruct_eq_sum] at ha
  have h := congrArg (normalizedEdgeCoefficientLinear m hm) ha
  rw [normalizedEdgeCoefficient_reconstruct, map_zero] at h
  exact congrFun h e

noncomputable def zeroSumDotForm (m : ℕ) : LinearMap.BilinForm ℝ (zeroSumSpace m) :=
  (coordinateDotBilinForm m).restrict (zeroSumSpace m)

@[simp] theorem zeroSumDotForm_apply (m : ℕ) (x y : zeroSumSpace m) :
    zeroSumDotForm m x y = ∑ i, x.val i * y.val i := by
  simp [zeroSumDotForm, LinearMap.BilinForm.restrict_apply]

theorem normalizedEdgeReconstruct_one (m : ℕ) (hm : m ≠ 0) :
    normalizedEdgeReconstruct m (fun _ ↦ 1) = zeroSumDotForm m := by
  ext x y
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  simp only [normalizedEdgeReconstruct, LinearMap.smul_apply, smul_eq_mul,
    reconstructEdgeForm_apply, weightedEdgeBilinForm_apply, one_mul, zeroSumDotForm_apply]
  have hsum := sum_edge_forms_on_zeroSum m x y
  simp only [edgeBilinForm_apply] at hsum
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hm', one_mul]

theorem normalizedEdgeCoefficient_dot (m : ℕ) (hm : m ≠ 0) :
    normalizedEdgeCoefficientLinear m hm (zeroSumDotForm m) = fun _ ↦ 1 := by
  rw [← normalizedEdgeReconstruct_one m hm, normalizedEdgeCoefficient_reconstruct]

theorem zeroSumDotForm_isSymm (m : ℕ) : (zeroSumDotForm m).IsSymm := by
  constructor
  intro x y
  simp only [zeroSumDotForm_apply, mul_comm]

theorem zeroSumDotForm_posDef (m : ℕ) : ∀ x : zeroSumSpace m, x ≠ 0 →
    0 < zeroSumDotForm m x x := by
  intro x hx
  rw [zeroSumDotForm_apply]
  have hnonzero : ∃ i : Fin m, x.val i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hx
    apply Subtype.ext
    funext i
    exact hn i
  obtain ⟨i, hi⟩ := hnonzero
  exact Finset.sum_pos' (fun j _ ↦ mul_self_nonneg (x.val j))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

theorem normalizedEdgeCovector_ne_zero (m : ℕ) (hm : m ≠ 0) (e : EdgePair m) :
    normalizedEdgeCovector m e ≠ 0 := by
  intro he
  have hform : normalizedEdgeForm m e = 0 := by
    ext x y
    simp [normalizedEdgeForm, he]
  exact (normalizedEdgeForm_linearIndependent m hm).ne_zero e hform

def edgePairSigmaEquiv (m : ℕ) : EdgePair m ≃ (Σ j : Fin m, Fin j.val) where
  toFun e := ⟨e.val.2, ⟨e.val.1.val, e.property⟩⟩
  invFun e := ⟨(⟨e.2.val, lt_trans e.2.isLt e.1.isLt⟩, e.1), e.2.isLt⟩
  left_inv e := by rcases e with ⟨⟨i,j⟩, h⟩; rfl
  right_inv e := by rcases e with ⟨j,i⟩; rfl

theorem card_edgePair (m : ℕ) : Fintype.card (EdgePair m) = m * (m - 1) / 2 := by
  rw [Fintype.card_congr (edgePairSigmaEquiv m), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h : (∑ i : Fin m, (fun j : ℕ ↦ j) i.val) = ∑ i ∈ Finset.range m, i :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ j) m
  exact h.trans (Finset.sum_range_id m)

theorem finrank_zeroSumSpace (m : ℕ) (hm : m ≠ 0) :
    Module.finrank ℝ (zeroSumSpace m) = m - 1 := by
  have hsurj : Function.Surjective (coordinateSum m) := by
    intro r
    refine ⟨Pi.single ⟨0, Nat.pos_of_ne_zero hm⟩ r, ?_⟩
    simp
  have h := LinearMap.finrank_range_add_finrank_ker (coordinateSum m)
  rw [LinearMap.range_eq_top.mpr hsurj] at h
  simp only [finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at h
  change Module.finrank ℝ (LinearMap.ker (coordinateSum m)) = m - 1
  omega

#print axioms weightedEdgeBilinForm_offdiag
#print axioms weightedEdgeBilinForm_center
#print axioms edgeBilinForm_restrict_linearIndependent
#print axioms sum_edge_forms_complete_graph
#print axioms sum_edge_forms_on_zeroSum
#print axioms edgeCoefficientLinear_reconstruct
#print axioms reconstructEdgeForm_coefficients
#print axioms edge_form_decomposition_unique
#print axioms normalizedEdgeForm_eq_smul
#print axioms normalizedEdgeReconstruct_coefficients
#print axioms normalizedEdgeForm_linearIndependent
#print axioms normalizedEdgeReconstruct_one
#print axioms normalizedEdgeCoefficient_dot
#print axioms zeroSumDotForm_posDef
#print axioms normalizedEdgeCovector_ne_zero
#print axioms card_edgePair
#print axioms finrank_zeroSumSpace

end GlobalEmbedding.Offline
