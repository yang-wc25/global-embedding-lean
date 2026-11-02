import Probes.ActualIncrementOriginalTensorPairing
import Probes.ActualCoreWeightedJets
import Probes.ActualJointTensorChartTransfer
import Smoothing.ParameterRound2CompactNorms

/-! The original tensor/linear-coefficient norms supply the actual joint
profiles used by the primary wave and its mean. Differentiation stays on the
original parameter-open neighborhood; no global smooth extension or compact
parameter differentiation is imposed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology BigOperators
namespace GlobalEmbedding.Continuation

private theorem paperPartial_open_restrict {n : ℕ} (l : List (Fin n))
    (f : (Fin n → ℝ) → ℝ) (O U : Set (Fin n → ℝ))
    (hO : IsOpen O) (hU : IsOpen U) (hUO : U ⊆ O) :
    EqOn (paperCoordinatePartial l f O) (paperCoordinatePartial l f U) U := by
  induction l with
  | nil => intro x hx; rfl
  | cons a l ih =>
    intro x hx
    change lineDerivWithin ℝ (paperCoordinatePartial l f O) O x (Pi.single a 1) =
      lineDerivWithin ℝ (paperCoordinatePartial l f U) U x (Pi.single a 1)
    rw [lineDerivWithin_of_isOpen hO (hUO hx), lineDerivWithin_of_isOpen hU hx]
    have he : paperCoordinatePartial l f O =ᶠ[𝓝 x] paperCoordinatePartial l f U := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hy
    exact he.lineDeriv_eq

/-- Restricting the differentiation chart to a true open neighborhood of every
sample changes none of the original norm's scalar partials. -/
theorem actual_paperAtlasWeighted_open_restrict
    {ι : Type*} [Fintype ι] {n q : ℕ} (base j : ℕ) (ell : ℝ)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ) (O U S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hU : ∀ i, IsOpen (U i))
    (hUO : ∀ i, U i ⊆ O i) (hSU : ∀ i, S i ⊆ U i) :
    paperAtlasWeighted base j ell f O S = paperAtlasWeighted base j ell f U S := by
  unfold paperAtlasWeighted
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  unfold paperAtlasCj paperCoordinateCj
  apply iSup_congr
  intro i
  apply iSup_congr
  intro l
  apply iSup_congr
  intro x
  apply iSup_congr
  intro c
  rw [paperPartial_open_restrict l.val (fun y => f i y c) (O i) (U i)
    (hO i) (hU i) (hUO i) (hSU i x.property)]

/-- Fixed finite coordinate evaluation, on all ordered symmetric components.
Its norm depends only on the original spatial dimension. -/
def actualOriginalCoefficientFunctional (n : ℕ) :
    (Fin (n*n) → ℝ) →L[ℝ] ((Fin (n*n) → ℝ) →L[ℝ] ℝ) :=
  ∑ k, (ContinuousLinearMap.proj k : (Fin (n*n) → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj k : (Fin (n*n) → ℝ) →L[ℝ] ℝ)

@[simp] theorem actualOriginalCoefficientFunctional_apply (n : ℕ)
    (L A : Fin (n*n) → ℝ) :
    actualOriginalCoefficientFunctional n L A = ∑ k, L k*A k := by
  simp [actualOriginalCoefficientFunctional]

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace P]

theorem actual_original_jointPoint_continuousOn
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    ContinuousOn (incrementsOriginalJointPoint D.atlas D.parameterChart i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i) := by
  have hp : Continuous (incrementsOriginalParameterPoint (n := n) (d := d)) :=
    (parameterTensorModelEquiv n d).symm.continuous.fst
  have hx : Continuous (incrementsOriginalSourcePoint (n := n) (d := d)) :=
    (parameterTensorModelEquiv n d).symm.continuous.snd
  exact ((D.parameterChart i.2).symm.continuousOn.comp hp.continuousOn
    (fun y hy => hy.2)).prodMk
      ((D.atlas.chart i.1).symm.continuousOn.comp hx.continuousOn (fun y hy => hy.1))

theorem actual_original_primaryDifferentiation_open
    (D : IncrementsOriginalNativeData n d N M P)
    (hPrimary : ∀ ν, IsOpen (D.primaryDomain ν))
    (ν : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount) :
    IsOpen (incrementsOriginalPrimaryDifferentiation D ν i) :=
  (actual_original_jointPoint_continuousOn D i).isOpen_inter_preimage
    (parameterRound2_originalDifferentiation_open D.atlas D.parameterChart i) (hPrimary ν)

theorem actual_original_parameter_coordinate_region_open
    (D : IncrementsOriginalNativeData n d N M P) (hOpen : IsOpen D.parameterOpen)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    IsOpen (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
      (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
        incrementsOriginalParameterRegion D) :=
  (actual_original_jointPoint_continuousOn D i).isOpen_inter_preimage
    (parameterRound2_originalDifferentiation_open D.atlas D.parameterChart i)
    (hOpen.prod isOpen_univ)

/-- The literal original weighted norm, with its original differentiation
domain, controls every joint jet after the actual slow coordinate transition.
The parameter-open restriction is justified by the preceding exact equality. -/
theorem actual_original_weighted_coordinate_transfer
    {ι : Type*} [Fintype ι] {a q : ℕ}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (j : ℕ) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (ell : ℝ) (hell : 0 < ell)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O U S : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hU : ∀ i, IsOpen (U i))
    (hUO : ∀ i, U i ⊆ O i) (hSU : ∀ i, S i ⊆ U i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hfinite : paperAtlasWeighted 0 j ell f O S ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted 0 j ell f O S).toReal ≤ budget)
    (i : ι) (phi : X → Fin a → ℝ) (V R : Set X)
    (hV : IsOpen V) (hRV : R ⊆ V) (hphi : ContDiffOn ℝ ∞ phi V)
    (hmap : MapsTo phi V (U i)) (hsample : MapsTo phi R (S i))
    (hphijet : ∀ x ∈ R, ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1) * ‖iteratedFDeriv ℝ k phi x‖ ≤ T k) :
    ContDiffOn ℝ ∞ (f i ∘ phi) V ∧
      ∀ k ≤ j, ∀ x ∈ R, ell^k * ‖iteratedFDeriv ℝ k (f i ∘ phi) x‖ ≤
        actualFastChartTransferPrefix T j * coordinateDimensionFactor a j * budget := by
  have he := actual_paperAtlasWeighted_open_restrict 0 j ell f O U S hO hU hUO hSU
  have hfiniteU : paperAtlasWeighted 0 j ell f U S ≠ ⊤ := he ▸ hfinite
  have hbudgetU : (paperAtlasWeighted 0 j ell f U S).toReal ≤ budget := he ▸ hbudget
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  refine ⟨(hf i).comp hphi hmap, ?_⟩
  intro k hk x hx
  have hjet (r : ℕ) (hr : r ≤ k) :
      ell^r * ‖iteratedFDeriv ℝ r (f i) (phi x)‖ ≤ coordinateDimensionFactor a j * budget := by
    have h := paperAtlasWeighted_shifted_joint_jet_le 0 j ell hell f U S hU hSU hf
      hfiniteU i (hr.trans hk) (le_refl 0) (hsample hx)
    simp only [Nat.add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left hbudgetU (coordinateDimensionFactor_nonneg a j))
  have ht := actual_fast_joint_chart_transfer T hT k phi (f i) V (U i) hV (hU i)
    hphi (hf i) hmap x (hRV hx) ell ell (coordinateDimensionFactor a j * budget)
    hell le_rfl hjet (fun r hr hrk => hphijet x hx r hr (hrk.trans hk))
  exact ht.trans ((mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix T hT hk)
    (mul_nonneg (coordinateDimensionFactor_nonneg a j) hbudget0)).trans_eq (by ring))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_paperAtlasWeighted_open_restrict
#print axioms GlobalEmbedding.Continuation.actual_original_primaryDifferentiation_open
#print axioms GlobalEmbedding.Continuation.actual_original_weighted_coordinate_transfer
