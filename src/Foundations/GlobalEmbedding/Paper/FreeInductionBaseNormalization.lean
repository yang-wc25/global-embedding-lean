import GlobalEmbedding.Paper.FreeInductionDisplacement
import GlobalEmbedding.Paper.FreeMixedPeriodIdentity
import GlobalEmbedding.Paper.FreeInductionNearProjection
import GlobalEmbedding.Paper.FreeHopfProductSuccessor
import GlobalEmbedding.Paper.FreeHopfUnitComplements
import GlobalEmbedding.Paper.FreeNormalizedColumnStabilityBridge

/-!
# Genuine base-column annihilation for both normalized inverse patches

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 477–489.
Every column is a literal derivative of the same F₀, transported through the actual successor split.
-/

noncomputable section
open scoped ContDiff Manifold

namespace GlobalEmbedding.Paper

variable {m K : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]

/-- Every pure-old sorted second base column is exactly the same old second column in its old
block. The accepted true old derivative is applied again to the smooth actual first derivative;
no interchange or dropped derivative of an auxiliary field is used. -/
theorem freeInductionBase_whole_old_second
    (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hH : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (x : FreeHopfProduct C) (ij : {p : Fin m × Fin m // p.1 ≤ p.2}) :
    freeFlowColumns (freeHopfProductFlow C)
      (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C) x
      (Sum.inr ⟨(ij.val.1.castSucc, ij.val.2.castSucc), ij.property⟩) =
      freeInductionBlock K m
        (freeFlowColumns (freeHopfProductFlow (freeHopfOldDimensions C)) H
          (freeHopfProductSplit C x).1 (Sum.inr ij)) 0 0 := by
  have hfirst : freeHopfDeriv C ij.val.2.castSucc
      (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C) =
      fun y ↦ freeInductionBlock K m
        (freeHopfDeriv (freeHopfOldDimensions C) ij.val.2 H (freeHopfProductSplit C y).1) 0 0 :=
    funext fun y ↦ freeHopfInductionBase_deriv_old C H hH f ij.val.2 y
  change freeHopfDeriv C ij.val.1.castSucc (freeHopfDeriv C ij.val.2.castSucc _) x = _
  rw [hfirst]
  exact freeHopfInductionBase_deriv_old C (freeHopfDeriv (freeHopfOldDimensions C) ij.val.2 H)
    (freeHopfDeriv_contMDiff (freeHopfOldDimensions C) H hH ij.val.2)
    (fun _ ↦ 0) ij.val.1 x

/-- Every mixed second base column is genuinely zero: its active first column is constant
along each actual old-factor flow. No assumption of a vanishing mixed column is used. -/
theorem freeInductionBase_whole_mixed
    (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ f)
    (x : FreeHopfProduct C) (i : Fin m) :
    freeFlowColumns (freeHopfProductFlow C)
      (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C) x
      (Sum.inr ⟨(i.castSucc, Fin.last m), Fin.le_last _⟩) = 0 := by
  have hactive : freeHopfDeriv C (Fin.last m)
      (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C) =
      fun y ↦ freeInductionBlock K m 0
        (orbitDeriv planarHopfFlow f (freeHopfProductSplit C y).2) 0 :=
    funext fun y ↦ freeHopfInductionBase_deriv_last C H f hf y
  change freeHopfDeriv C i.castSucc (freeHopfDeriv C (Fin.last m) _) x = 0
  rw [hactive]
  change deriv (fun t ↦ freeInductionBlock K m 0
    (orbitDeriv planarHopfFlow f
      (freeHopfProductSplit C (freeHopfProductFlow C i.castSucc t x)).2) 0) 0 = 0
  simp_rw [freeHopfProductSplit_flow_old]
  exact deriv_const _ _

/-- The active-active base column is the genuine planar acceleration in the common block. -/
theorem freeInductionBase_whole_active_second
    (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : MatrixPlanarSelectorProperties f) (x : FreeHopfProduct C) :
    freeFlowColumns (freeHopfProductFlow C)
      (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C) x
      (Sum.inr ⟨(Fin.last m, Fin.last m), le_rfl⟩) =
      freeInductionBlock K m 0
        (planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2 •
          planarQuarterTurn (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2)) 0 := by
  have hactive : freeHopfDeriv C (Fin.last m)
      (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C) =
      fun y ↦ freeInductionBlock K m 0
        (orbitDeriv planarHopfFlow f (freeHopfProductSplit C y).2) 0 :=
    funext fun y ↦ freeHopfInductionBase_deriv_last C H f hf.smooth y
  change freeHopfDeriv C (Fin.last m) (freeHopfDeriv C (Fin.last m) _) x = _
  rw [hactive]
  change deriv (fun t ↦ freeInductionBlock K m 0
    (orbitDeriv planarHopfFlow f
      (freeHopfProductSplit C (freeHopfProductFlow C (Fin.last m) t x)).2) 0) 0 = _
  simp_rw [freeHopfProductSplit_flow_last]
  have hv := contMDiff_orbitDeriv planarHopfFlow
    (planarHopfFlow_contMDiff (C (Fin.last m))) f hf.smooth
  have hd := freeInductionBase_active_orbitDeriv (m := m)
    (fun _ : FreeHopfProduct (freeHopfOldDimensions C) ↦ (0 : EuclideanSpace ℝ (Fin K)))
    (orbitDeriv planarHopfFlow f) hv (freeHopfProductSplit C x).1
    (freeHopfProductSplit C x).2
  rw [hf.acceleration] at hd
  simpa only [orbitDeriv, freeInductionBase, freeAugmentCLM_eq_block] using hd

/-- Scalar multiplication in the planar component is literal scalar multiplication of the
same common Euclidean block, not a new block map or target norm. -/
theorem freeInductionBlock_planar_smul (K m : ℕ) (c : ℝ) (v : Planar) :
    freeInductionBlock K m 0 (c • v) 0 = c • freeInductionBlock K m 0 v 0 := by
  unfold freeInductionBlock
  rw [← map_smul]
  congr 1
  ext j
  rcases j with j | (j | j) <;> simp [PiLp.smul_apply]

/-- All selected near-patch base columns of the literal same F₀ vanish after the actual projection.
The canonical near mask includes precisely the mixed and active-active second columns. -/
theorem freeInductionBase_near_masked
    (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : MatrixPlanarSelectorProperties f) (x : FreeHopfProduct C)
    (j : BalancedPairingIndex (m + 1)) (hj : freeNearColumnMask m j = true) :
    freeInductionNearProjection K m (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2)
      (freeFlowColumns (freeHopfProductFlow C)
        (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C) x j) = 0 := by
  have hlast (i : Fin (m + 1)) :
      freeInductionNearProjection K m
        (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2)
        (freeFlowColumns (freeHopfProductFlow C)
          (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C) x
          (Sum.inr ⟨(i, Fin.last m), Fin.le_last i⟩)) = 0 := by
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · rw [freeInductionBase_whole_active_second C H f hf x, freeInductionBlock_planar_smul]
      exact freeInductionNearProjection_active_base _ _ _ _
    · rw [freeInductionBase_whole_mixed C H f hf.smooth x i, map_zero]
  cases j with
  | inl i => simp [freeNearColumnMask] at hj
  | inr ij =>
    have hsecond : ij.val.2 = Fin.last m := of_decide_eq_true hj
    have heq : ij = ⟨(ij.val.1, Fin.last m), Fin.le_last _⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl hsecond
    rw [heq]
    exact hlast _

/-- The far mask selects only actual mixed base columns, so no target projection is required. -/
theorem freeInductionBase_far_masked
    (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ f)
    (x : FreeHopfProduct C) (j : BalancedPairingIndex (m + 1))
    (hj : freeFarColumnMask m j = true) :
    freeFlowColumns (freeHopfProductFlow C)
      (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C) x j = 0 := by
  cases j with
  | inl i => simp [freeFarColumnMask] at hj
  | inr ij =>
    have hs : ij.val.2 = Fin.last m ∧ ij.val.1 ≠ Fin.last m := of_decide_eq_true hj
    have hneq : ij.val.1.val ≠ m := fun h ↦ hs.2 (Fin.ext h)
    have hlt : ij.val.1.val < m := by have hb := ij.val.1.isLt; omega
    let i : Fin m := ⟨ij.val.1.val, hlt⟩
    have heq : ij = ⟨(i.castSucc, Fin.last m), Fin.le_last _⟩ := by
      apply Subtype.ext
      exact Prod.ext (Fin.ext rfl) hs.1
    rw [heq]
    exact freeInductionBase_whole_mixed C H f hf x i

/-- Vanishing of actual selected columns annihilates the entire masked data subspace,
by the accepted literal finite-synthesis formula. This is a full operator identity. -/
theorem free_masked_column_operator_zero
    {Idx E : Type*} [Fintype Idx] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (prj : E →L[ℝ] E) (masked : Idx → Bool) (v : Idx → E)
    (hv : ∀ j, masked j = true → prj (v j) = 0) :
    (prj.comp (freeColumnOperator v)).comp (freeCoordinateMask masked) = 0 := by
  ext u
  change prj (freeColumnOperator v (freeCoordinateMask masked u)) = 0
  rw [freeColumnOperator_apply, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_smul, freeCoordinateMask_apply]
  by_cases hj : masked j = true
  · simp [hj, hv j hj]
  · simp [hj]

/-- The actual near-patch base-annihilation hypothesis of the normalized polynomial is proved
for the original balanced pairing map of the same actual F₀. No zero-column data is supplied. -/
theorem freeInductionBase_near_operator_zero
    (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hH : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : MatrixPlanarSelectorProperties f) (x : FreeHopfProduct C) :
    ((freeInductionNearProjection K m
        (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2)).comp
      (balancedPairingMap (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C)
        (freeHopfGenerator C) x).adjoint).comp (freeCoordinateMask (freeNearColumnMask m)) = 0 := by
  have hF := (freeInductionBase_contMDiff (m := m) H hH f hf.smooth).comp
    (freeHopfProductSplit_contMDiff C)
  rw [free_balanced_pairing_adjoint_eq_columnOperator,
    freeHopf_balanced_pairing_columns C _ hF x]
  exact free_masked_column_operator_zero _ _ _ (freeInductionBase_near_masked C H f hf x)

/-- The actual unprojected far base similarly annihilates exactly the canonical mixed mask. -/
theorem freeInductionBase_far_operator_zero
    (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hH : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, Planar) ∞ f)
    (x : FreeHopfProduct C) :
    (balancedPairingMap (freeInductionBase (m := m) H f ∘ freeHopfProductSplit C)
      (freeHopfGenerator C) x).adjoint.comp (freeCoordinateMask (freeFarColumnMask m)) = 0 := by
  have hF := (freeInductionBase_contMDiff (m := m) H hH f hf).comp
    (freeHopfProductSplit_contMDiff C)
  rw [free_balanced_pairing_adjoint_eq_columnOperator,
    freeHopf_balanced_pairing_columns C _ hF x]
  have hz := free_masked_column_operator_zero (ContinuousLinearMap.id ℝ _)
    (freeFarColumnMask m) _ (fun j hj ↦ by
      simpa only [ContinuousLinearMap.id_apply] using freeInductionBase_far_masked C H f hf x j hj)
  simpa only [ContinuousLinearMap.id_comp] using hz

#print axioms freeInductionBase_whole_old_second
#print axioms freeInductionBase_whole_active_second
#print axioms freeInductionBase_near_masked
#print axioms freeInductionBase_far_masked
#print axioms freeInductionBase_near_operator_zero
#print axioms freeInductionBase_far_operator_zero

end GlobalEmbedding.Paper
