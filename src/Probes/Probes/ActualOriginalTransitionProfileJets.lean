import Probes.ActualOriginalPhaseProfileJets

/-! The SAME given source/parameter transition supplies its native positive
jets from its displayed original differential profile. Reverse chart pairs
are included in the same finite maximum. No adapted transition is an input
of this given-data profile, and no cardinality of the atlas enters the cost. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology BigOperators
namespace GlobalEmbedding.Continuation

def actualMatrixOperatorAssembly (a : ℕ) :
    (Fin (a*a) → ℝ) →L[ℝ] ((Fin a → ℝ) →L[ℝ] (Fin a → ℝ)) :=
  ∑ r : Fin a, ∑ s : Fin a,
    (ContinuousLinearMap.proj (finProdFinEquiv (r,s)) : (Fin (a*a) → ℝ) →L[ℝ] ℝ).smulRight
      ((ContinuousLinearMap.proj s : (Fin a → ℝ) →L[ℝ] ℝ).smulRight (Pi.single r 1))

theorem actualMatrixOperatorAssembly_exact (a : ℕ) (L : (Fin a → ℝ) →L[ℝ] (Fin a → ℝ)) :
    actualMatrixOperatorAssembly a
      (fun c => L (Pi.single (finProdFinEquiv.symm c).2 1) (finProdFinEquiv.symm c).1) = L := by
  ext v r
  have hv : (∑ s : Fin a, v s • (Pi.single s 1 : Fin a → ℝ)) = v := by
    ext t
    simp [Pi.single_apply]
  have hL : L v = ∑ s : Fin a, v s • L (Pi.single s 1) := by
    calc
      _ = L (∑ s : Fin a, v s • (Pi.single s 1 : Fin a → ℝ)) := congrArg L hv.symm
      _ = _ := by rw [map_sum]; simp only [map_smul]
  have hvalue := congrFun hL r
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hvalue
  have hrow (r s : Fin a) : (finProdFinEquiv (r,s)).divNat = r :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (r,s))
  have hcol (r s : Fin a) : (finProdFinEquiv (r,s)).modNat = s :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (r,s))
  simpa [actualMatrixOperatorAssembly,Pi.single_apply,mul_comm,hrow,hcol] using hvalue.symm

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "X" => Ep × Es

private local instance transitionProfileProductCharted : ChartedSpace X (P × M) :=
  prodChartedSpace Ep P Es M
private local instance transitionProfileProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

theorem actualOriginalGivenTransition_contDiffOn
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount)) :
    ContDiffOn ℝ ∞ (actualOriginalGivenTransition D ik.1 ik.2) (actualOriginalGivenTransitionDomain D ik) := by
  let a := parameterTensorModelEquiv n d
  let qi := (D.parameterChart ik.1.2).prod (D.atlas.chart ik.1.1)
  let qk := (D.parameterChart ik.2.2).prod (D.atlas.chart ik.2.1)
  have hqi : qi ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hd.parameter_charts_smooth ik.1.2)
      (hd.atlas_smooth.chart_mem ik.1.1)
  have hqk : qk ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hd.parameter_charts_smooth ik.2.2)
      (hd.atlas_smooth.chart_mem ik.2.1)
  let : ChartedSpace X X := chartedSpaceSelf X
  have ht : ContDiffOn ℝ ∞ (qk ∘ qi.symm) (qi.target ∩ qi.symm ⁻¹' qk.source) :=
    ((contMDiffOn_of_mem_maximalAtlas hqk).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hqi).mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  change ContDiffOn ℝ ∞ (a ∘ (qk ∘ qi.symm) ∘ a.symm) _
  apply a.contDiff.comp_contDiffOn (ht.comp a.symm.contDiff.contDiffOn ?_)
  intro y hy
  exact ⟨⟨hy.1.2,hy.1.1⟩,hy.2⟩

theorem actualOriginalGivenTransitionDifferential_contDiffOn
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount)) :
    ContDiffOn ℝ ∞ (actualOriginalGivenTransitionDifferentialCoordinates D ik)
      (actualOriginalGivenTransitionDomain D ik) := by
  apply contDiffOn_pi.mpr
  intro c
  exact (ContinuousLinearMap.proj (finProdFinEquiv.symm c).1 :
    (Fin (n+d) → ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (((actualOriginalGivenTransition_contDiffOn D hd ik).fderiv_of_isOpen
        (actualOriginalGivenTransitionDomain_open D ik) (m := ∞) (by simp)).clm_apply contDiffOn_const)

def actualOriginalGivenTransitionJetCost (n d j : ℕ) : ℝ :=
  ‖actualMatrixOperatorAssembly (n+d)‖*coordinateDimensionFactor (n+d) j

theorem actual_original_given_transition_positive_jets
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (j : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hfinite : actualOriginalGivenInputProfile D j ell ≠ ⊤)
    (hbudget : (actualOriginalGivenInputProfile D j ell).toReal ≤ budget)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount))
    (k : ℕ) (hk : k ≤ j) (z : Fin (n+d) → ℝ)
    (hz : z ∈ actualOriginalGivenTransitionSample D ik) :
    ell^k*‖iteratedFDeriv ℝ (k+1) (actualOriginalGivenTransition D ik.1 ik.2) z‖ ≤
      actualOriginalGivenTransitionJetCost n d j*budget := by
  let O := actualOriginalGivenTransitionDomain D
  let S := actualOriginalGivenTransitionSample D
  let f := actualOriginalGivenTransitionDifferentialCoordinates D
  have hO := actualOriginalGivenTransitionDomain_open D
  have hSO : ∀ i, S i ⊆ O i := fun _ => inter_subset_right
  have hf := actualOriginalGivenTransitionDifferential_contDiffOn D hd
  have hle := actualOriginalGivenInputProfile_transition_le D j ell
  have hfin : paperAtlasWeighted 0 j ell f O S ≠ ⊤ := ne_top_of_le_ne_top hfinite hle
  have hbound : (paperAtlasWeighted 0 j ell f O S).toReal ≤ budget :=
    (ENNReal.toReal_mono hfinite hle).trans hbudget
  have hj := paperAtlasWeighted_shifted_joint_jet_le 0 j ell hell f O S hO hSO hf hfin ik hk
    (le_refl 0) hz
  simp only [Nat.add_zero] at hj
  have hcoef : ell^k*‖iteratedFDeriv ℝ k (f ik) z‖ ≤ coordinateDimensionFactor (n+d) j*budget :=
    hj.trans (mul_le_mul_of_nonneg_left hbound (coordinateDimensionFactor_nonneg _ _))
  have hDf : fderiv ℝ (actualOriginalGivenTransition D ik.1 ik.2) =
      actualMatrixOperatorAssembly (n+d) ∘ f ik := by
    funext y
    exact (actualMatrixOperatorAssembly_exact (n+d)
      (fderiv ℝ (actualOriginalGivenTransition D ik.1 ik.2) y)).symm
  have hp := slow_linear_jet_bound (actualMatrixOperatorAssembly (n+d)) (O ik) (hO ik) (f ik) (hf ik)
    k ell (coordinateDimensionFactor (n+d) j*budget) hell.le z (hSO ik hz) hcoef
  rw [← hDf,norm_iteratedFDeriv_fderiv] at hp
  exact hp.trans_eq (by dsimp only [actualOriginalGivenTransitionJetCost]; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_given_transition_positive_jets
