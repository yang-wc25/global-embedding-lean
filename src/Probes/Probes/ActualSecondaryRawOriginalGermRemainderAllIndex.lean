import Probes.ActualSecondaryRawMetricDataAllIndex
import Probes.ActualSecondaryOriginalRemainderCoordinates
import Probes.ActualSecondaryNativeTensorGermNorm
import Smoothing.ParameterRound2SymmetricTensorSpace

/-! Raw original profiles, the fixed actual secondary choices and the true
inverse parameter charts produce the mean-removed native metric error in
the unchanged original weighted atlas norm on each true sample neighborhood. The constant precedes every
actual atlas, field, scale and cutoff choice. All observation charts see
one and the same global map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M Tr : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance rawNormTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance rawNormTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawNormTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

 theorem actual_original_raw_metric_germ_remainder_uniform_all_index
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ (Label SubPrimary SubSecondary : Type*)
      [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary], ∀ (pcount : ℕ), ∀
      (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph Ep Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
      (S : Fin A.count × Fin pcount → Set (Fin (m+1+d) → ℝ))
      (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
      (ell delta tau Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
      (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
      (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar nInput nSolve j q Rsub Lprimary
        reserve Bnd Mg Kcut T Tinv W primary ell delta tau Delta choice)
      (Obs : Fin A.count × Fin pcount → Set X)
      (obs : ∀ i : Fin A.count × Fin pcount, ActualOriginalSecondaryObservationData raw Tobs Rsecondary
        (A.chart i.1) (Obs i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)))
      (hParam : ∀ i : Fin A.count × Fin pcount, ∀ z : X,
        parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k → k ≤ j →
        ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k),
    let U := actualOriginalIncrementMap F hF g input (q+2) tau delta choice
    let Rest := incrementsOriginalMetricError (fun y => F y.1 y.2) U
      (incrementsGlobalPrimaryMean F hF g input (q+2) tau) delta
    Rest ∈ parameterRound2_originalTensorGermSpace A B S W ∧
    (∀ i, ∀ k ≤ j, ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ S i →
      tau^k*‖iteratedFDeriv ℝ k (actualOriginalNativeTargetTensor A B Rest i) z‖ ≤
        CR*(delta*(tau/ell)^q+delta^3/tau)) ∧
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B Rest)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B Rest)
        (incrementsOriginalDifferentiation A B) S).toReal ≤
        (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*CR*
          (delta*(tau/ell)^q+delta^3/tau)) := by
  obtain ⟨K,hK,hraw⟩ := actual_original_raw_metric_remainder_of_data_uniform_all_index
    (m := m) (N := N) («Ep» := Ep) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput reserve Bnd Mg Kcut hc hBnd hMg hKcut
    T Tinv Tobs hT hTinv hTobs
  let CP := actualFastChartTransferPrefix TP j
  have hCP : 0 ≤ CP := actualFastChartTransferPrefix_nonneg TP hTP j
  refine ⟨CP*K,mul_nonneg hCP hK,?_⟩
  intro Label SubPrimary SubSecondary _ _ _ _ pcount A B hA hB F hF g input inputbar W primary S hSO ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice raw Obs obs hParam U Rest
  let a := parameterTensorModelEquiv (m+1) d
  let phi := fun i : Fin A.count × Fin pcount => parameterRound2_meanParameterMap (m := m) (B i.2)
  let Ubase := fun i : Fin A.count × Fin pcount => (B i.2).target ×ˢ (A.chart i.1).target
  let V0 := Obs
  let O := fun i : Fin A.count × Fin pcount => Ubase i ∩ (phi i) ⁻¹' V0 i
  let S0 := fun i => a ⁻¹' S i
  let S1 := fun i => phi i '' S0 i
  let E0 := fun i : Fin A.count × Fin pcount => actualOriginalMeanRemovedMetric F hF g input (q+2) tau delta choice (A.chart i.1)
  let err := delta*(tau/ell)^q+delta^3/tau
  have hell : 0 < ell := htau.trans_le htaul
  have herr : 0 ≤ err := by dsimp only [err]; positivity
  have hUbase (i) : IsOpen (Ubase i) := (B i.2).open_target.prod (A.chart i.1).open_target
  have hV (i) : IsOpen (V0 i) := (obs i).profiles.hO
  have hphiBase (i) : ContDiffOn ℝ ∞ (phi i) (Ubase i) :=
    (((contMDiffOn_symm_of_mem_maximalAtlas (hB i.2)).contDiffOn).comp
      contDiffOn_fst (fun _ hz => hz.1)).prodMk contDiffOn_snd
  have hO (i) : IsOpen (O i) := (hphiBase i).continuousOn.isOpen_inter_preimage (hUbase i) (hV i)
  have hSO0 : ∀ i, S0 i ⊆ O i := by
    intro i z hz
    have hh := hSO i hz
    have he : (incrementsOriginalParameterPoint (a z),incrementsOriginalSourcePoint (a z)) = z := a.symm_apply_apply z
    refine ⟨?_,(obs i).profiles.hSO ⟨z,hz,rfl⟩⟩
    rw [← he]
    exact ⟨hh.2,hh.1⟩
  have hphi (i) : ContDiffOn ℝ ∞ (phi i) (O i) := (hphiBase i).mono inter_subset_left
  have hmap (i) : MapsTo (phi i) (O i) (V0 i) := fun _ hz => hz.2
  have hh (i) := hraw Label SubPrimary SubSecondary F hF g input inputbar W primary ell delta tau Delta hdelta hdeltatau choice raw
    (A.chart i.1) (V0 i) (S1 i) (obs i)
  have heq (i) : EqOn (actualOriginalNativeTargetTensor A B Rest i) (E0 i ∘ phi i) (O i) :=
    (actual_original_mean_removed_native_pullback A B hA F hF g input (q+2) tau delta choice i).mono inter_subset_left
  have hsm (i) : ContDiffOn ℝ ∞ (actualOriginalNativeTargetTensor A B Rest i) (O i) :=
    (((hh i).1.comp (hphi i) (hmap i)).congr (heq i))
  have hjets : ∀ i, ∀ k ≤ j, ∀ z ∈ S0 i,
      tau^k*‖iteratedFDeriv ℝ k (actualOriginalNativeTargetTensor A B Rest i) z‖ ≤ (CP*K)*err := by
    intro i k hk z hz
    rw [(((heq i).eventuallyEq_of_mem ((hO i).mem_nhds (hSO0 i hz))).iteratedFDeriv ℝ k).eq_of_nhds]
    have ht := actual_fast_joint_chart_transfer TP hTP k (phi i) (E0 i) (O i) (V0 i)
      (hO i) (hV i) (hphi i) (hh i).1 (hmap i) z (hSO0 i hz) tau ell (K*err) htau htaul
      (fun r hr => (hh i).2 r (hr.trans hk) (phi i z) ⟨z,hz,rfl⟩)
      (fun r hr hrk => hParam i z hz r hr (hrk.trans hk))
    exact (ht.trans (mul_le_mul_of_nonneg_right
      (actualFastChartTransferCost_le_prefix TP hTP hk) (mul_nonneg hK herr))).trans_eq (by ring)
  obtain ⟨hreg,hf,hb⟩ := actual_original_tensor_weighted_norm_from_native_germs A B S O hO
    (fun _ => inter_subset_left) hSO0 Rest j tau ((CP*K)*err)
    htau (htaul.trans hell1) (mul_nonneg (mul_nonneg hCP hK) herr) hsm hjets
  have hmember : Rest ∈ parameterRound2_originalTensorGermSpace A B S W := by
    constructor
    · intro i
      refine ⟨a.symm ⁻¹' O i,(hO i).preimage a.symm.continuous,?_,hreg i⟩
      intro y hy
      exact hSO0 i (by change a (a.symm y) ∈ S i; simpa only [a.apply_symm_apply] using hy)
    · intro z hz
      exact ((inducedMetric_isPosSemidef (I := 𝓙) (fun x => F z.1 x+U (z.1,x)) z.2).isSymm.sub
        (inducedMetric_isPosSemidef (I := 𝓙) (F z.1) z.2).isSymm).sub
        ((parameterRound2_actual_native_mean_symmetric F hF g input (q+2) tau z.1 z.2).smul (delta^2))
  exact ⟨hmember,hjets,hf,hb.trans_eq (by ring)⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_raw_metric_germ_remainder_uniform_all_index
