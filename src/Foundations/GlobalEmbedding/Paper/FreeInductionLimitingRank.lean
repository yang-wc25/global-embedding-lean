import GlobalEmbedding.Paper.FreeUniformPivotEstimates
import GlobalEmbedding.Paper.FreeInductionDisplacement
import GlobalEmbedding.Paper.FreeInductionNearProjection
import GlobalEmbedding.Paper.FreeNormalizedPolynomialColumns
import GlobalEmbedding.Paper.FreeInductionBaseNormalization
import GlobalEmbedding.Paper.FreeInductionMixedColumns
import GlobalEmbedding.Paper.FreeInductionColumnGrouping

/-!
# Actual limiting normalized-column rank in both induction patches

Source: `main.tex`, thm:free, lines477–489.
DAG: free-induction-limiting-rank. Exclusive W3 ownership recorded before edits.
W2 owns physical columns, W4 owns grouping and the common epsilon inverse.
-/
noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
namespace GlobalEmbedding.Paper

/-- The genuine complement quotient kills every old block perpendicular to nu. -/
theorem freeComplementFrameCLM_adjoint_old {K m : ℕ}
    (ν h : EuclideanSpace ℝ (Fin K)) (hperp : ⟪ν, h⟫ = 0) :
    (freeComplementFrameCLM (m := m) ν).adjoint (freeInductionBlock K m h 0 0) = 0 := by
  apply ext_inner_left ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right,
    freeComplementFrameCLM_apply, freeInductionBlock_inner]
  simp only [real_inner_smul_left, hperp, mul_zero, inner_zero_right, zero_add]

/-- The genuine complement quotient kills every planar block. -/
theorem freeComplementFrameCLM_adjoint_planar {K m : ℕ}
    (ν : EuclideanSpace ℝ (Fin K)) (v : Planar) :
    (freeComplementFrameCLM (m := m) ν).adjoint (freeInductionBlock K m 0 v 0) = 0 := by
  apply ext_inner_left ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right,
    freeComplementFrameCLM_apply, freeInductionBlock_inner]
  simp

/-- Unit nu makes the genuine complement quotient recover every actual complement vector. -/
theorem freeComplementFrameCLM_adjoint_self {K m : ℕ}
    (ν : EuclideanSpace ℝ (Fin K)) (hν : ‖ν‖ = 1)
    (w : EuclideanSpace ℝ (Fin (m + 1))) :
    (freeComplementFrameCLM ν).adjoint (freeComplementFrameCLM ν w) = w := by
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, freeComplementFrameCLM_inner ν hν]

/-- Projecting off the actual planar Jv does not change the genuine complement quotient. -/
theorem freeComplementFrameCLM_adjoint_near {K m : ℕ}
    (ν : EuclideanSpace ℝ (Fin K)) (v : Planar) (hv : ‖v‖ = 1)
    (y : EuclideanSpace ℝ (Fin (K + (2 + m)))) :
    (freeComplementFrameCLM (m := m) ν).adjoint
        (freeInductionNearProjection K m v y) =
      (freeComplementFrameCLM (m := m) ν).adjoint y := by
  rw [freeInductionNearProjection_apply K m v hv, map_sub, map_smul,
    freeComplementFrameCLM_adjoint_planar, smul_zero, sub_zero]

/-- The actual old free columns remain independent in the common augmented target.
The fixed block wrapper is injective by its genuine old coordinates. -/
theorem freeInductionOldBlock_independent {m K : ℕ}
    (Cs : Fin m → ℕ)
    (H : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin K))
    (hH : ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow Cs) H x))
    (x : FreeHopfProduct Cs) :
    LinearIndependent ℝ (fun j ↦ freeInductionBlock K m
      (freeFlowColumns (freeHopfProductFlow Cs) H x j) 0 0) := by
  let L : EuclideanSpace ℝ (Fin K) →L[ℝ]
      EuclideanSpace ℝ (Fin (K + (2 + m))) :=
    (freeAugmentCLM K m).comp ((ContinuousLinearMap.id ℝ _).prod 0)
  have hinj : Function.Injective L := by
    intro a b hab
    ext i
    have hi := congrArg (fun u : EuclideanSpace ℝ (Fin (K + (2 + m))) ↦
      u (freeInductionIndexEquiv K m (Sum.inl i))) hab
    simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply, freeAugmentCLM_eq_block,
      freeInductionBlock_coordinate, Sum.elim_inl] using hi
  exact (hH x).map' L.toLinearMap (LinearMap.ker_eq_bot.mpr hinj)

/-- The actual old free columns and the same unit planar velocity are independent
in the genuine common target. Pairing with that planar velocity removes its
coefficient; the accepted old block independence removes all remaining ones. -/
theorem freeInductionOldAndVelocity_independent {m K : ℕ}
    (Cs : Fin m → ℕ) (H : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin K))
    (hH : ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow Cs) H x))
    (x : FreeHopfProduct Cs) (v : Planar) (hv : ‖v‖ = 1) :
    LinearIndependent ℝ (Sum.elim
      (fun j ↦ freeInductionBlock K m
        (freeFlowColumns (freeHopfProductFlow Cs) H x j) 0 0)
      (fun _ : Unit ↦ freeInductionBlock K m 0 v 0)) := by
  let a := fun j ↦ freeInductionBlock K m
    (freeFlowColumns (freeHopfProductFlow Cs) H x j) 0 0
  let b := freeInductionBlock K m 0 v 0
  have ha : LinearIndependent ℝ a := freeInductionOldBlock_independent Cs H hH x
  have hba (i) : ⟪b, a i⟫ = 0 := by
    dsimp only [a, b]
    rw [freeInductionBlock_inner]
    simp
  have hbb : ⟪b, b⟫ = 1 := by
    dsimp only [b]
    rw [freeInductionBlock_inner]
    simp [hv]
  apply Fintype.linearIndependent_iff.mpr
  intro g hg j
  have hz : (∑ i, g (Sum.inl i) • a i) + g (Sum.inr ()) • b = 0 := by
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_unique] using hg
  have hi := congrArg (fun y ↦ ⟪b, y⟫) hz
  simp only [inner_add_right, inner_sum, real_inner_smul_right, hba, hbb,
    mul_zero, Finset.sum_const_zero, mul_one, zero_add, inner_zero_right] at hi
  have ho := Fintype.linearIndependent_iff.mp ha (fun i ↦ g (Sum.inl i))
    (by simpa only [hi, zero_smul, add_zero] using hz)
  cases j with
  | inl i => exact ho i
  | inr u => cases u; exact hi

/-- The actual far quotient separates the genuine mixed directions from the
nonzero planar curvature direction. Its product is only a linear quotient. -/
theorem freePivot_far_quotient_independent {m C : ℕ}
    (Cs : Fin m → ℕ)
    (Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere C → ℝ)
    (A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1))) (δ lam κ : ℝ)
    (p : FreeHopfProduct Cs × PlanarHopfSphere C) (hlam : 0 < lam)
    (hbound : ∀ v, lam * ‖v‖ ^ 2 ≤ ‖freePivotMixedFrame Cs Q η A n δ p v‖ ^ 2)
    (hκ : κ ≠ 0) :
    LinearIndependent ℝ (Fin.snoc (fun i ↦
      (freeDisplacementMixedVector Q η δ (freeHopfDeriv Cs i A p.1)
        (freeHopfDeriv Cs i n p.1) p.2, (0 : ℝ))) (0, κ)) := by
  have hinj : Function.Injective (freePivotMixedFrame Cs Q η A n δ p) := by
    apply (injective_iff_map_eq_zero (freePivotMixedFrame Cs Q η A n δ p)).mpr
    intro v hv
    have hh := hbound v
    rw [hv, norm_zero, zero_pow (by omega)] at hh
    have hs : ‖v‖ ^ 2 ≤ 0 := (mul_le_mul_iff_of_pos_left hlam).mp (by simpa using hh)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  have hMi := (freeColumnOperator_injective_iff _).mp hinj
  let J : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin (m + 1)) × ℝ) := LinearMap.id.prod 0
  have hJi : Function.Injective J := by
    intro a b hab
    exact congrArg Prod.fst hab
  have hprod := hMi.map' J (LinearMap.ker_eq_bot.mpr hJi)
  apply linearIndependent_finSnoc.mpr
  refine ⟨hprod, ?_⟩
  intro hspan
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  have hh := congrArg (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin (m + 1))) ℝ) hg
  simp only [map_sum, map_smul, LinearMap.snd_apply, smul_zero,
    Finset.sum_const_zero] at hh
  exact hκ hh.symm

/-- The actual planar normal functional kills every old or complement variation,
including the full outside derivative of nu in the genuine mixed column. -/
theorem freeInductionPlanarNormal_inner_variation {K m : ℕ}
    (ν μ : EuclideanSpace ℝ (Fin K)) (v : Planar)
    (a b : EuclideanSpace ℝ (Fin (m + 1))) :
    ⟪freeInductionBlock K m 0 (planarQuarterTurn v) 0,
      freeComplementVariation ν μ a b⟫ = 0 := by
  rw [freeComplementVariation, freeAugmentCLM_eq_block, freeInductionBlock_inner]
  simp

/-- The same actual unit velocity is perpendicular to the actual embedded Jv.
Use the accepted genuine near projection's fixed-velocity identity. -/
theorem freeInductionPlanarNormal_inner_velocity (K m : ℕ) (v : Planar) (hv : ‖v‖ = 1) :
    ⟪freeInductionBlock K m 0 (planarQuarterTurn v) 0,
      freeInductionBlock K m 0 v 0⟫ = 0 := by
  let q := freeInductionBlock K m 0 (planarQuarterTurn v) 0
  have hm := Submodule.starProjection_apply_mem (ℝ ∙ q)ᗮ (freeInductionBlock K m 0 v 0)
  change freeInductionNearProjection K m v (freeInductionBlock K m 0 v 0) ∈ (ℝ ∙ q)ᗮ at hm
  rw [freeInductionNearProjection_fix_velocity K m v hv] at hm
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (by simp [q])) hm

/-- The actual planar acceleration has quotient coefficient exactly its genuine
curvature, since the actual embedded Jv is unit. -/
theorem freeInductionPlanarNormal_inner_acceleration (K m : ℕ)
    (v : Planar) (hv : ‖v‖ = 1) (κ : ℝ) :
    ⟪freeInductionBlock K m 0 (planarQuarterTurn v) 0,
      freeInductionBlock K m 0 (κ • planarQuarterTurn v) 0⟫ = κ := by
  rw [freeInductionBlock_planar_smul, real_inner_smul_right,
    real_inner_self_eq_norm_sq, freeInductionNearProjection_unit_direction K m v hv,
    one_pow, mul_one]

section ActualColumns
variable {m K : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]
local instance freeLimitingOldPositive (i : Fin m) :
    Fact (0 < freeHopfOldDimensions C i) := inferInstanceAs (Fact (0 < C i.castSucc))
local instance freeLimitingMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  let n := (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ))
  n.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

variable
    (ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hν : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ ν) (hunit : ∀ y, ‖ν y‖ = 1)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η) (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)

include hν hunit hP hQ hPQ hη hA hn in
/-- The genuine complement quotient of the actual physical mixed column is the
same literal M_i. This consumes W2's physical inner-product identity. -/
theorem freeHopfInductionZ_adjoint_mixed (i : Fin m) (x : FreeHopfProduct C) :
    (freeComplementFrameCLM (ν (freeHopfProductSplit C x).1)).adjoint
      (freeHopfDeriv C i.castSucc
        (freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n)) x) =
    freeDisplacementMixedVector Q η δ
      (freeHopfDeriv (freeHopfOldDimensions C) i A (freeHopfProductSplit C x).1)
      (freeHopfDeriv (freeHopfOldDimensions C) i n (freeHopfProductSplit C x).1)
      (freeHopfProductSplit C x).2 := by
  apply ext_inner_left ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact freeHopfInductionZ_mixed_frame_inner C ν hν hunit P Q hP hQ hPQ η hη δ A n hA hn i x w

include hunit hP hQ hPQ hη in
/-- The same complement quotient of the actual active second column is the
same actual XXV used in the accepted uniform pivot theorem. -/
theorem freeHopfInductionZ_adjoint_active (x : FreeHopfProduct C) :
    (freeComplementFrameCLM (ν (freeHopfProductSplit C x).1)).adjoint
      (freeHopfDeriv C (Fin.last m)
        (freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n)) x) =
    freePivotActiveSecond (freeHopfOldDimensions C) P Q η A n δ (freeHopfProductSplit C x) := by
  rw [freeHopfInductionZ_active_second C ν P Q hP hQ hPQ η hη δ A n x,
    freeComplementFrameCLM_adjoint_self _ (hunit _)]

include hν hP hQ hPQ hη hA hn in
/-- The additional far quotient functional kills the actual physical mixed
column. W2's true moving-frame formula retains the full derivative of nu. -/
theorem freeHopfInductionZ_mixed_planar_normal (v : Planar)
    (i : Fin m) (x : FreeHopfProduct C) :
    ⟪freeInductionBlock K m 0 (planarQuarterTurn v) 0,
      freeHopfDeriv C i.castSucc
        (freeHopfDeriv C (Fin.last m) (freeHopfInductionZ C ν P Q η δ A n)) x⟫ = 0 := by
  rw [freeHopfInductionZ_mixed_second C ν hν P Q hP hQ hPQ η hη δ A n hA hn i x]
  exact freeInductionPlanarNormal_inner_variation _ _ _ _ _

variable
    (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hH : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
    (hOldLI : ∀ y, LinearIndependent ℝ (freeFlowColumns
      (freeHopfProductFlow (freeHopfOldDimensions C)) H y))
    (hOldPerp : ∀ y j, ⟪ν y,
      freeFlowColumns (freeHopfProductFlow (freeHopfOldDimensions C)) H y j⟫ = 0)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar) (hf : MatrixPlanarSelectorProperties f)

include hH in
/-- Grouping the actual original old base columns gives exactly the same old
free columns in the sole target block. Both physical derivative providers are reused. -/
theorem freeInductionBase_grouped_old (x : FreeHopfProduct C) (j : BalancedPairingIndex m) :
    freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionBase C H f) x
      (freeOldColumnIndex m j) = freeInductionBlock K m
      (freeFlowColumns (freeHopfProductFlow (freeHopfOldDimensions C)) H
        (freeHopfProductSplit C x).1 j) 0 0 := by
  cases j with
  | inl i => exact freeHopfInductionBase_deriv_old C H hH f i x
  | inr ij => exact freeInductionBase_whole_old_second C H hH f x ij

include hν hunit hP hQ hPQ hη hA hn hH hOldLI hOldPerp hf in
/-- On the actual near patch, the genuine projected selected-linear/unselected-base
columns are independent. The actual complement quotient gives the accepted same
mixed/active pivot family, and actual old columns plus velocity give the remaining rank. -/
theorem free_induction_near_zero_columns_independent
    (lam : ℝ) (x : FreeHopfProduct C) (hlam : 0 < lam)
    (hcoercive : ∀ w, lam * ‖w‖ ^ 2 ≤
      ‖freePivotMixedFrame (freeHopfOldDimensions C) Q η A n δ (freeHopfProductSplit C x) w‖ ^ 2)
    (hpivot : 0 < ⟪freePivotNormal (freeHopfOldDimensions C) Q η A n δ
        (freeHopfProductSplit C x),
      freePivotActiveSecond (freeHopfOldDimensions C) P Q η A n δ (freeHopfProductSplit C x)⟫) :
    LinearIndependent ℝ (fun j ↦
      if freeNearColumnMask m j then
        freeInductionNearProjection K m
          (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2)
          (freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionZ C ν P Q η δ A n) x j)
      else freeInductionNearProjection K m
          (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2)
          (freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionBase C H f) x j)) := by
  let y := freeHopfProductSplit C x
  let v := orbitDeriv planarHopfFlow f y.2
  have hv : ‖v‖ = 1 := hf.unit_speed _
  let prj := freeInductionNearProjection K m v
  let c := fun j ↦ if freeNearColumnMask m j then
    prj (freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionZ C ν P Q η δ A n) x j)
    else prj (freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionBase C H f) x j)
  let a := Sum.elim
    (fun j ↦ freeInductionBlock K m
      (freeFlowColumns (freeHopfProductFlow (freeHopfOldDimensions C)) H y.1 j) 0 0)
    (fun _ : Unit ↦ freeInductionBlock K m 0 v 0)
  let b := fun i : Fin (m + 1) ↦ c (Sum.inr ⟨(i, Fin.last m), Fin.le_last i⟩)
  let T := (freeComplementFrameCLM (m := m) (ν y.1)).adjoint
  have ha : LinearIndependent ℝ a :=
    freeInductionOldAndVelocity_independent (freeHopfOldDimensions C) H hOldLI y.1 v hv
  have hTa (j) : T (a j) = 0 := by
    cases j with
    | inl j => exact freeComplementFrameCLM_adjoint_old _ _ (hOldPerp y.1 j)
    | inr u => exact freeComplementFrameCLM_adjoint_planar _ _
  have hnew (i : Fin (m + 1)) : T (b i) =
      Fin.snoc (α := fun _ ↦ EuclideanSpace ℝ (Fin (m + 1)))
        (fun j : Fin m ↦ freeDisplacementMixedVector Q η δ
        (freeHopfDeriv (freeHopfOldDimensions C) j A y.1)
        (freeHopfDeriv (freeHopfOldDimensions C) j n y.1) y.2)
        (freePivotActiveSecond (freeHopfOldDimensions C) P Q η A n δ y) i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [b, c, freeNearColumnMask, decide_eq_true_eq, ite_true, Fin.snoc_last]
      change T (prj (freeHopfDeriv C (Fin.last m) (freeHopfDeriv C (Fin.last m)
        (freeHopfInductionZ C ν P Q η δ A n)) x)) = _
      rw [freeComplementFrameCLM_adjoint_near _ v hv]
      exact freeHopfInductionZ_adjoint_active C ν hunit P Q hP hQ hPQ η hη δ A n x
    · simp only [b, c, freeNearColumnMask, decide_eq_true_eq, ite_true, Fin.snoc_castSucc]
      change T (prj (freeHopfDeriv C j.castSucc (freeHopfDeriv C (Fin.last m)
        (freeHopfInductionZ C ν P Q η δ A n)) x)) = _
      rw [freeComplementFrameCLM_adjoint_near _ v hv]
      exact freeHopfInductionZ_adjoint_mixed C ν hν hunit P Q hP hQ hPQ η hη δ A n hA hn j x
  have hb : LinearIndependent ℝ (fun i ↦ T (b i)) := by
    simp_rw [hnew]
    exact (freePivot_rank_of_bounds (freeHopfOldDimensions C) P Q η A n δ lam y
      hlam hcoercive hpivot).2
  have hfull := free_triangular_column_independence a b T.toLinearMap ha hb hTa
  apply freeInductionColumns_independent_of_grouping m
  change LinearIndependent ℝ (c ∘ freeInductionColumnIndex m)
  have hold (j : BalancedPairingIndex m) : c (freeOldColumnIndex m j) = a (Sum.inl j) := by
    have hm : freeNearColumnMask m (freeOldColumnIndex m j) = false := by
      cases j <;> simp [freeNearColumnMask, freeOldColumnIndex]
    simp only [c, hm, Bool.false_eq_true, ite_false]
    rw [freeInductionBase_grouped_old C H hH f x j]
    exact freeInductionNearProjection_fix_complement K m v hv _ _
  have hactive : c (Sum.inl (Fin.last m)) = a (Sum.inr ()) := by
    change prj (freeHopfDeriv C (Fin.last m) (freeHopfInductionBase C H f) x) = _
    rw [freeHopfInductionBase_deriv_last C H f hf.smooth x]
    exact freeInductionNearProjection_fix_velocity K m v hv
  have heq : c ∘ freeInductionColumnIndex m = Sum.elim a b := by
    funext j
    rcases j with (j | u) | i
    · exact hold j
    · cases u; exact hactive
    · rfl
  rw [heq]
  exact hfull

include hν hunit hP hQ hPQ hη hA hn hH hOldLI hOldPerp hf in
/-- Away from genuine curvature zero, the unprojected selected mixed columns
and all actual unselected base columns are independent in the original index.
The far quotient records the actual complement and planar-normal components. -/
theorem free_induction_far_zero_columns_independent
    (lam : ℝ) (x : FreeHopfProduct C) (hlam : 0 < lam)
    (hcoercive : ∀ w, lam * ‖w‖ ^ 2 ≤
      ‖freePivotMixedFrame (freeHopfOldDimensions C) Q η A n δ (freeHopfProductSplit C x) w‖ ^ 2)
    (hκ : planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2 ≠ 0) :
    LinearIndependent ℝ (fun j ↦
      if freeFarColumnMask m j then
        freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionZ C ν P Q η δ A n) x j
      else freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionBase C H f) x j) := by
  let y := freeHopfProductSplit C x
  let v := orbitDeriv planarHopfFlow f y.2
  let κ := planarOrbitCurvature planarHopfFlow f y.2
  have hv : ‖v‖ = 1 := hf.unit_speed _
  let c := fun j ↦ if freeFarColumnMask m j then
    freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionZ C ν P Q η δ A n) x j
    else freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionBase C H f) x j
  let a := Sum.elim
    (fun j ↦ freeInductionBlock K m
      (freeFlowColumns (freeHopfProductFlow (freeHopfOldDimensions C)) H y.1 j) 0 0)
    (fun _ : Unit ↦ freeInductionBlock K m 0 v 0)
  let b := fun i : Fin (m + 1) ↦ c (Sum.inr ⟨(i, Fin.last m), Fin.le_last i⟩)
  let TT := (freeComplementFrameCLM (m := m) (ν y.1)).adjoint
  let q := innerSL ℝ (freeInductionBlock K m 0 (planarQuarterTurn v) 0)
  let T := TT.prod q
  have ha : LinearIndependent ℝ a :=
    freeInductionOldAndVelocity_independent (freeHopfOldDimensions C) H hOldLI y.1 v hv
  have hTa (j) : T (a j) = 0 := by
    cases j with
    | inl j =>
      apply Prod.ext
      · exact freeComplementFrameCLM_adjoint_old _ _ (hOldPerp y.1 j)
      · change ⟪freeInductionBlock K m 0 (planarQuarterTurn v) 0,
          freeInductionBlock K m _ 0 0⟫ = 0
        rw [freeInductionBlock_inner]
        simp
    | inr u =>
      apply Prod.ext
      · exact freeComplementFrameCLM_adjoint_planar _ _
      · exact freeInductionPlanarNormal_inner_velocity K m v hv
  have hnew (i : Fin (m + 1)) : T (b i) =
      Fin.snoc (α := fun _ ↦ EuclideanSpace ℝ (Fin (m + 1)) × ℝ)
        (fun j : Fin m ↦ (freeDisplacementMixedVector Q η δ
          (freeHopfDeriv (freeHopfOldDimensions C) j A y.1)
          (freeHopfDeriv (freeHopfOldDimensions C) j n y.1) y.2, (0 : ℝ))) (0, κ) i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [b, c, freeFarColumnMask, ne_eq, not_true_eq_false, and_false,
        decide_false, Bool.false_eq_true, ite_false, Fin.snoc_last]
      change T (freeFlowColumns (freeHopfProductFlow C)
        (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C) x
        (Sum.inr ⟨(Fin.last m, Fin.last m), le_rfl⟩)) = (0, κ)
      rw [freeInductionBase_whole_active_second C H f hf x]
      apply Prod.ext
      · exact freeComplementFrameCLM_adjoint_planar _ _
      · exact freeInductionPlanarNormal_inner_acceleration K m v hv κ
    · have hm : freeFarColumnMask m
          (Sum.inr ⟨(j.castSucc, Fin.last m), Fin.le_last _⟩) = true := by
        simp [freeFarColumnMask]
      simp only [b, c, hm, ite_true, Fin.snoc_castSucc]
      apply Prod.ext
      · exact freeHopfInductionZ_adjoint_mixed C ν hν hunit P Q hP hQ hPQ η hη δ A n hA hn j x
      · exact freeHopfInductionZ_mixed_planar_normal C ν hν P Q hP hQ hPQ η hη δ A n hA hn v j x
  have hb : LinearIndependent ℝ (fun i ↦ T (b i)) := by
    simp_rw [hnew]
    exact freePivot_far_quotient_independent (freeHopfOldDimensions C) Q η A n δ lam κ y
      hlam hcoercive hκ
  have hfull := free_triangular_column_independence a b T.toLinearMap ha hb hTa
  apply freeInductionColumns_independent_of_grouping m
  change LinearIndependent ℝ (c ∘ freeInductionColumnIndex m)
  have hold (j : BalancedPairingIndex m) : c (freeOldColumnIndex m j) = a (Sum.inl j) := by
    have hm : freeFarColumnMask m (freeOldColumnIndex m j) = false := by
      cases j <;> simp [freeFarColumnMask, freeOldColumnIndex]
    simp only [c, hm, Bool.false_eq_true, ite_false]
    exact freeInductionBase_grouped_old C H hH f x j
  have hactive : c (Sum.inl (Fin.last m)) = a (Sum.inr ()) := by
    exact freeHopfInductionBase_deriv_last C H f hf.smooth x
  have heq : c ∘ freeInductionColumnIndex m = Sum.elim a b := by
    funext j
    rcases j with (j | u) | i
    · exact hold j
    · cases u; exact hactive
    · rfl
  rw [heq]
  exact hfull

include hν hunit hP hQ hPQ hη hA hn hH hOldLI hOldPerp hf in
/-- Genuine injectivity at zero of the original near normalized-column polynomial.
Both raw column operators are the original balancedPairingMap adjoints on the actual
Hopf product. The quadratic coefficient is unrestricted, since it drops out at zero. -/
theorem free_induction_near_zero_injective
    (A2 : EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (K + (2 + m))))
    (lam : ℝ) (x : FreeHopfProduct C) (hlam : 0 < lam)
    (hcoercive : ∀ w, lam * ‖w‖ ^ 2 ≤
      ‖freePivotMixedFrame (freeHopfOldDimensions C) Q η A n δ (freeHopfProductSplit C x) w‖ ^ 2)
    (hpivot : 0 < ⟪freePivotNormal (freeHopfOldDimensions C) Q η A n δ
        (freeHopfProductSplit C x),
      freePivotActiveSecond (freeHopfOldDimensions C) P Q η A n δ (freeHopfProductSplit C x)⟫) :
    Function.Injective (freeNormalizedColumnPolynomial
      (freeInductionNearProjection K m
        (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2))
      (freeCoordinateMask (freeNearColumnMask m))
      (balancedPairingMap (I := freeHopfModel C) (freeHopfInductionBase C H f)
        (freeHopfGenerator C) x).adjoint
      (balancedPairingMap (I := freeHopfModel C) (freeHopfInductionZ C ν P Q η δ A n)
        (freeHopfGenerator C) x).adjoint A2 0) := by
  simp only [free_balanced_pairing_adjoint_eq_columnOperator]
  rw [freeHopf_balanced_pairing_columns C _
      (freeHopfInductionBase_contMDiff C H hH f hf.smooth) x,
    freeHopf_balanced_pairing_columns C _
      (freeHopfInductionZ_contMDiff C ν hν P Q hP hQ η hη δ A n hA hn) x]
  rw [freeNormalizedColumnPolynomial_zero]
  have he := free_normalized_polynomial_zero_columns
    (freeInductionNearProjection K m
          (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2)) (freeNearColumnMask m)
    (freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionBase C H f) x)
    (freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionZ C ν P Q η δ A n) x)
    (fun _ ↦ 0)
  rw [freeNormalizedColumnPolynomial_zero] at he
  rw [he]
  apply (freeColumnOperator_injective_iff _).mpr
  exact free_induction_near_zero_columns_independent C ν hν hunit P Q hP hQ hPQ η hη δ
    A n hA hn H hH hOldLI hOldPerp f hf lam x hlam hcoercive hpivot


include hν hunit hP hQ hPQ hη hA hn hH hOldLI hOldPerp hf in
/-- Genuine injectivity at zero of the original far normalized-column polynomial.
Both raw column operators are the original balancedPairingMap adjoints on the actual
Hopf product. The quadratic coefficient is unrestricted, since it drops out at zero. -/
theorem free_induction_far_zero_injective
    (A2 : EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (K + (2 + m))))
    (lam : ℝ) (x : FreeHopfProduct C) (hlam : 0 < lam)
    (hcoercive : ∀ w, lam * ‖w‖ ^ 2 ≤
      ‖freePivotMixedFrame (freeHopfOldDimensions C) Q η A n δ (freeHopfProductSplit C x) w‖ ^ 2)
    (hκ : planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2 ≠ 0) :
    Function.Injective (freeNormalizedColumnPolynomial
      (ContinuousLinearMap.id ℝ _) (freeCoordinateMask (freeFarColumnMask m))
      (balancedPairingMap (I := freeHopfModel C) (freeHopfInductionBase C H f)
        (freeHopfGenerator C) x).adjoint
      (balancedPairingMap (I := freeHopfModel C) (freeHopfInductionZ C ν P Q η δ A n)
        (freeHopfGenerator C) x).adjoint A2 0) := by
  simp only [free_balanced_pairing_adjoint_eq_columnOperator]
  rw [freeHopf_balanced_pairing_columns C _
      (freeHopfInductionBase_contMDiff C H hH f hf.smooth) x,
    freeHopf_balanced_pairing_columns C _
      (freeHopfInductionZ_contMDiff C ν hν P Q hP hQ η hη δ A n hA hn) x]
  rw [freeNormalizedColumnPolynomial_zero]
  have he := free_normalized_polynomial_zero_columns
    (ContinuousLinearMap.id ℝ _) (freeFarColumnMask m)
    (freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionBase C H f) x)
    (freeFlowColumns (freeHopfProductFlow C) (freeHopfInductionZ C ν P Q η δ A n) x)
    (fun _ ↦ 0)
  rw [freeNormalizedColumnPolynomial_zero] at he
  rw [he]
  apply (freeColumnOperator_injective_iff _).mpr
  exact free_induction_far_zero_columns_independent C ν hν hunit P Q hP hQ hPQ η hη δ
    A n hA hn H hH hOldLI hOldPerp f hf lam x hlam hcoercive hκ

/-- Both original normalized-column operators are injective at zero for the SAME
actual induction data. Q is literally XP and kappa is the curvature of the same f.
The two quantitative inputs are the already proved uniform-pivot conclusions,
not desired limiting-rank assumptions. This theorem preserves the chosen A,n,
delta and buffer, so it consumes freeHopf_induction_data_exists without choosing
another displacement. The actual old induction hypothesis supplies every old
independence, normal, unit and native-smoothness property internally. -/
theorem free_induction_limiting_rank
    (H ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hIH : FreeSelectorProperties (freeHopfModel (freeHopfOldDimensions C))
      (freeHopfProductFlow (freeHopfOldDimensions C)) H ν)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar) (hf : MatrixPlanarSelectorProperties f)
    (P : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (δ d₀ lam : ℝ) (hδ : 0 < δ) (hlam : 0 < lam)
    (hcoercive : ∀ p : FreeHopfProduct (freeHopfOldDimensions C) ×
        PlanarHopfSphere (C (Fin.last m)), ∀ w,
      lam * ‖w‖ ^ 2 ≤ ‖freePivotMixedFrame (freeHopfOldDimensions C)
        (orbitDeriv planarHopfFlow P) η A n δ p w‖ ^ 2)
    (hbuffer : ∀ p : FreeHopfProduct (freeHopfOldDimensions C) ×
        PlanarHopfSphere (C (Fin.last m)),
      |planarOrbitCurvature planarHopfFlow f p.2| < d₀ → δ / 4 ≤
        ⟪freePivotNormal (freeHopfOldDimensions C) (orbitDeriv planarHopfFlow P) η A n δ p,
          freePivotActiveSecond (freeHopfOldDimensions C) P
            (orbitDeriv planarHopfFlow P) η A n δ p⟫) :
    let Q := orbitDeriv planarHopfFlow P
    ∀ (x : FreeHopfProduct C)
      (A2 : EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (K + (2 + m)))),
      (|planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2| < d₀ →
        Function.Injective (freeNormalizedColumnPolynomial
          (freeInductionNearProjection K m
            (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2))
          (freeCoordinateMask (freeNearColumnMask m))
          (balancedPairingMap (I := freeHopfModel C) (freeHopfInductionBase C H f)
            (freeHopfGenerator C) x).adjoint
          (balancedPairingMap (I := freeHopfModel C) (freeHopfInductionZ C ν P Q η δ A n)
            (freeHopfGenerator C) x).adjoint A2 0)) ∧
      (planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2 ≠ 0 →
        Function.Injective (freeNormalizedColumnPolynomial (ContinuousLinearMap.id ℝ _)
          (freeCoordinateMask (freeFarColumnMask m))
          (balancedPairingMap (I := freeHopfModel C) (freeHopfInductionBase C H f)
            (freeHopfGenerator C) x).adjoint
          (balancedPairingMap (I := freeHopfModel C) (freeHopfInductionZ C ν P Q η δ A n)
            (freeHopfGenerator C) x).adjoint A2 0)) := by
  dsimp only
  obtain ⟨hH, hν, _, hOldLI, hunit, hOldPerp⟩ := hIH
  let Q := orbitDeriv planarHopfFlow P
  have hQ := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff (C (Fin.last m))) P hP
  intro x A2
  constructor
  · intro hnear
    apply free_induction_near_zero_injective C ν hν hunit P Q hP hQ (fun _ ↦ rfl) η hη δ
      A n hA hn H hH hOldLI hOldPerp f hf A2 lam x hlam (hcoercive (freeHopfProductSplit C x))
    exact lt_of_lt_of_le (div_pos hδ (by norm_num)) (hbuffer (freeHopfProductSplit C x) hnear)
  · intro hκ
    exact free_induction_far_zero_injective C ν hν hunit P Q hP hQ (fun _ ↦ rfl) η hη δ
      A n hA hn H hH hOldLI hOldPerp f hf A2 lam x hlam (hcoercive (freeHopfProductSplit C x)) hκ

end ActualColumns
end GlobalEmbedding.Paper
