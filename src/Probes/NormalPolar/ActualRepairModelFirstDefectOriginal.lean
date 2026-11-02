import NormalPolar.ActualRepairModelFirstDefectCombinedJets
import NormalPolar.ActualRepairModelFirstDefectTotalCoordinates
import Probes.ActualSecondaryNativeTensorGermNorm

/-! The same actual combined primary and all signed secondary pieces give
the three-term remainder in the original weighted atlas norm. All inputs
below are actual piece/forcing/overlap data, smooth amplitude germs, or the
separate primary wave and primary linear-residual profiles. No estimate for
the remainder, the complete error, or the normalized defect is an input.
The true inverse parameter charts are retained before joint differentiation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N p r count : ℕ} {M Λ Β SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance firstTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance firstTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance firstTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

theorem actualRepairModelFirstDefect_combined_original_remainder
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (hAtlas : IsSmoothBufferedAtlas atlas)
    (hParamSmooth : ∀ i, param i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin atlas.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation atlas param i)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (t : Ep) → (x : D) → normalSpace (I := 𝓙) (F t) (c l t x))
    (phase : Fin r → Ep × M → ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (u : Fin p → ℝ)
    (n j q length : ℕ) (ell Mg CH delta tau : ℝ) (W : Set (Ep × M))
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n (j+1) ell Mg CH delta W)
    (hbudget : j+2+length ≤ n) (hql : q ≤ length)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) (hW : IsOpen W) :
    let b := fun i : Fin atlas.count × Fin count => (OpenPartialHomeomorph.refl Ep).prod (atlas.chart i.1)
    let phases := Sum.elim g.phase phase
    let R0 := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
    let Q0 := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
    let phi := fun i l t x => phases l ((b i).symm (t,x))
    let chi := fun (_ : Λ ⊕ Fin r) (_ : Ep) (_ : Unit) (_ : D) => (1 : ℝ)
    let P := fun i l t (_ : Unit) x => R0 l ((b i).symm (t,x))
    let Q := fun i l t (_ : Unit) x => Q0 l ((b i).symm (t,x))
    let primary := round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input u
    let U := fun z => primary z+actualConstructedSecondarySum F hF (fun rec a => (data rec a).base) tau length z
    let samples := fun i : Fin atlas.count × Fin count =>
      parameterRound2_meanParameterMap (m := m) (param i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)
    ∀ (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (hprimary : ∀ rec a, (data rec a).base.support ⊆ K rec.val.1.1 ∩ K rec.val.1.2)
    (Omega : Fin atlas.count × Fin count → Set X)
    (hOmega : ∀ i, IsOpen (Omega i)) (hSample : ∀ i, samples i ⊆ Omega i)
    (hTarget : ∀ i z, z ∈ Omega i → z.2 ∈ (atlas.chart i.1).target)
    (hmap : ∀ i, MapsTo (b i).symm (Omega i) W)
    (binding : ∀ i, ∀ rec : ActualSecondarySignedRecord (Λ ⊕ Fin r),
      let H := incrementsSecondaryQuadraticForcing (phi i) tau chi (P i) (Q i)
        (fun k _ => EuclideanSpace.single k 1) rec.1.1.1 rec.1.1.2 rec.1.2
      ActualSecondaryForcingBinding F hF (fun a => (data rec a).base) (b i)
        (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
        (incrementsSecondaryQuadraticPhase (phi i) rec.1.1.1 rec.1.1.2 rec.1.2))
    (O : (Fin atlas.count × Fin count) → ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → Set X)
    (hO : ∀ i rec a, IsOpen (O i rec a)) (hOOmega : ∀ i rec a, O i rec a ⊆ Omega i)
    (hActive : ∀ i rec a, samples i ∩ (b i).symm ⁻¹' (data rec a).base.support ⊆ O i rec a)
    (hSource : ∀ i rec a, MapsTo (b i).symm (O i rec a) (data rec a).base.chart.source)
    (hTransition : ∀ i rec a, ContDiffOn ℝ ∞ ((data rec a).base.chart ∘ (b i).symm) (O i rec a))
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hSecondarySample : ∀ i rec a z, z ∈ samples i ∩ (b i).symm ⁻¹' (data rec a).base.support →
      (data rec a).base.chart ((b i).symm z) ∈ (data rec a).base.sample)
    (hTransitionBound : ∀ i rec a z, z ∈ samples i ∩ (b i).symm ⁻¹' (data rec a).base.support →
      ∀ k, 1 ≤ k → k ≤ j+2 → ell^(k-1)*‖iteratedFDeriv ℝ k ((data rec a).base.chart ∘ (b i).symm) z‖ ≤ T k)
    (L R : ℕ)
    (hL : ∀ i z, z ∈ samples i → (Finset.univ.filter (fun nu => (b i).symm z ∈ K nu)).card ≤ L)
    (hR : ∀ i rec z, z ∈ samples i → (Finset.univ.filter (fun a => (b i).symm z ∈ (data rec a).base.support)).card ≤ R)
    (M1 CP : ℝ) (hM1 : 0 ≤ M1) (hCP : 0 ≤ CP)
    (hFobs : ∀ i, ContDiffOn ℝ ∞ (fun z : X => F ((b i).symm z).1 ((b i).symm z).2) (Omega i))
    (hU1 : ∀ i, ContDiffOn ℝ ∞ (primary ∘ (b i).symm) (Omega i))
    (hLin : ∀ i, ContDiffOn ℝ ∞ (actualJointMetricLinearization
      (fun z : X => F ((b i).symm z).1 ((b i).symm z).2) (primary ∘ (b i).symm)) (Omega i))
    (hMean : ∀ i, ContDiffOn ℝ ∞ (actualPrimaryOppositeMeanTensor (phi i) tau chi (P i) (Q i)) (Omega i))
    (hGrouped : ∀ i z, z ∈ Omega i → ∀ k,
      fderiv ℝ (fun x => primary ((b i).symm (z.1,x))) z.2 (EuclideanSpace.single k 1) =
      incrementsGroupedRealDerivative (fun nu => phi i nu z.1 z.2/tau)
        (incrementsSecondaryPhysicalCoefficient (phi i) tau chi (P i) (Q i)
          (fun k _ => EuclideanSpace.single k 1) z) k)
    (hU1jet : ∀ i k, k ≤ j+1 → ∀ z ∈ samples i,
      tau^k*‖iteratedFDeriv ℝ k (primary ∘ (b i).symm) z‖ ≤ M1*delta*tau)
    (hLinJet : ∀ i k, k ≤ j → ∀ z ∈ samples i,
      tau^k*‖iteratedFDeriv ℝ k (actualJointMetricLinearization
        (fun z : X => F ((b i).symm z).1 ((b i).symm z).2) (primary ∘ (b i).symm)) z‖ ≤
        CP*delta*tau*(tau/ell)^length)
    (TP : ℕ → ℝ) (hTP : ∀ k, 0 ≤ TP k)
    (hParam : ∀ i : Fin atlas.count × Fin count, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (param i.2)) z‖ ≤ TP k),
    let Rest := actualRepairModelFirstDefectArrayRest (fun z => F z.1 z.2) U phases tau R0 Q0
    let C := (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*
      actualFastChartTransferPrefix TP j*actualConstructedFiniteErrorCost m N n j length L R Mg CH M1 CP 0 T
    Rest ∈ parameterRound2_originalTensorGermSpace atlas param S W ∧
      paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates atlas param Rest)
        (incrementsOriginalDifferentiation atlas param) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates atlas param Rest)
        (incrementsOriginalDifferentiation atlas param) S).toReal ≤
        C*(delta*(tau/ell)^q+delta^3/tau) := by
  intro b phases R0 Q0 phi chi P Q primary U samples K hprimary Omega hOmega hSample hTarget hmap
    binding O hO hOOmega hActive hSource hTransition T hT hSecondarySample hTransitionBound L R hL hR
    M1 CP hM1 hCP hFobs hU1 hLin hMean hGrouped hU1jet hLinJet TP hTP hParam Rest C
  let CR := actualConstructedFiniteErrorCost m N n j length L R Mg CH M1 CP 0 T
  have hCR : 0 ≤ CR := by
    have hWave := actualSecondaryForcedWaveCost_nonneg m N n length (j+1) Mg CH hMg hCH
    have hPhysical := actualSecondaryPhysicalCost_nonneg m N n length (j+1) Mg CH hMg hCH
    have hV := actualFastChartTransferPrefix_nonneg T hT (j+1)
    have hT0 := actualFastTensorChartTransferPrefix_nonneg T hT (j+1)
    dsimp only [CR,actualConstructedFiniteErrorCost,actualConstructedSecondaryWaveBudget,
      actualConstructedSecondaryPhysicalBudget]
    positivity
  let E0 := fun i : Fin atlas.count × Fin count =>
    actualRepairModelFirstDefectObservedRest (fun z => F z.1 z.2) U phases tau R0 Q0 (atlas.chart i.1)
  have hlocal (i) : ContDiffOn ℝ ∞ (E0 i) (Omega i) ∧
      ∀ k ≤ j, ∀ z ∈ samples i, tau^k*‖iteratedFDeriv ℝ k (E0 i) z‖ ≤
        CR*(delta*(tau/ell)^q+delta^3/tau) := by
    have hb : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ (b i).symm (Omega i) := by
      have hf0 : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun z : X => z.1) (Omega i) := contDiffOn_fst.contMDiffOn
      have hs0 : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞ (fun z : X => z.2) (Omega i) := contDiffOn_snd.contMDiffOn
      exact hf0.prodMk ((contMDiffOn_symm_of_mem_maximalAtlas (hAtlas.chart_mem i.1)).comp
        hs0 (fun z hz => hTarget i z hz))
    have h := actualRepairModelFirstDefect_combined_remainder_jets
      F hF g label c vf phase backgroundLength probeLength a input u n j q length ell Mg CH delta tau W data
      hbudget hql hell hell1 htau htaul hdelta hdeltatau hMg hCH hW (b i)
      (binding i) (fun _ => 0) K hprimary (Omega i) (samples i) (hOmega i) (hSample i)
      (fun z hz => ⟨Set.mem_univ _,hTarget i z hz⟩) hb (hmap i) (fun _ _ => rfl)
      (O i) (hO i) (hOOmega i) (hActive i) (hSource i) (hTransition i) T hT
      (hSecondarySample i) (hTransitionBound i) L R (hL i) (hR i) M1 CP hM1 hCP
      (hFobs i) (hU1 i) contDiffOn_const (hLin i)
      (by simpa only [smul_zero,sub_zero] using hMean i) (hGrouped i) (hU1jet i) (hLinJet i)
    let Rloc := fun z : X => actualFiniteMetricError
      (fun w : X => F ((b i).symm w).1 ((b i).symm w).2)
      (fun w => primary ((b i).symm w)+
        actualConstructedSecondarySum F hF (fun rec a => (data rec a).base) tau length ((b i).symm w))
      (fun _ => 0) delta z-
      (actualPrimaryOppositeMeanTensor (phi i) tau chi (P i) (Q i) z-delta^2 • 0)
    have he : E0 i = Rloc := by
      funext z
      apply actual_bilinear_tensor_eq_of_basis
      intro k l
      simp only [E0,actualRepairModelFirstDefectObservedRest,Rloc,U,b,actualFiniteMetricError,
        sub_apply,smul_apply,zero_apply,smul_eq_mul,mul_zero,sub_zero]
      rfl
    change ContDiffOn ℝ ∞ Rloc (Omega i) ∧
      ∀ k ≤ j, ∀ z ∈ samples i, tau^k*‖iteratedFDeriv ℝ k Rloc z‖ ≤
        CR*(delta*(tau/ell)^q+delta^3/tau) at h
    rw [← he] at h
    exact h
  let ae := parameterTensorModelEquiv (m+1) d
  let psi := fun i : Fin atlas.count × Fin count => parameterRound2_meanParameterMap (m := m) (param i.2)
  let Ubase := fun i : Fin atlas.count × Fin count => (param i.2).target ×ˢ (atlas.chart i.1).target
  let O0 := fun i : Fin atlas.count × Fin count => Ubase i ∩ (psi i) ⁻¹' Omega i
  let S0 := fun i : Fin atlas.count × Fin count => ae ⁻¹' S i
  let CT := actualFastChartTransferPrefix TP j
  have hCT : 0 ≤ CT := actualFastChartTransferPrefix_nonneg TP hTP j
  let err := delta*(tau/ell)^q+delta^3/tau
  have herr : 0 ≤ err := by dsimp only [err]; positivity
  have hUbase (i) : IsOpen (Ubase i) := (param i.2).open_target.prod (atlas.chart i.1).open_target
  have hpsiBase (i) : ContDiffOn ℝ ∞ (psi i) (Ubase i) :=
    (((contMDiffOn_symm_of_mem_maximalAtlas (hParamSmooth i.2)).contDiffOn).comp
      contDiffOn_fst (fun _ hz => hz.1)).prodMk contDiffOn_snd
  have hO0 (i) : IsOpen (O0 i) := (hpsiBase i).continuousOn.isOpen_inter_preimage (hUbase i) (hOmega i)
  have hS0 : ∀ i, S0 i ⊆ O0 i := by
    intro i z hz
    have hh := hSO i hz
    have he : (incrementsOriginalParameterPoint (ae z),incrementsOriginalSourcePoint (ae z)) = z := ae.symm_apply_apply z
    refine ⟨?_,hSample i ⟨z,hz,rfl⟩⟩
    rw [← he]
    exact ⟨hh.2,hh.1⟩
  have heq (i) : EqOn (actualOriginalNativeTargetTensor atlas param Rest i) (E0 i ∘ psi i) (O0 i) := by
    intro z hz
    exact actualRepairModelFirstDefect_array_rest_pullback_total atlas param hAtlas
      (fun z => F z.1 z.2) U phases tau R0 Q0 i z hz.1
  have hsm (i) : ContDiffOn ℝ ∞ (actualOriginalNativeTargetTensor atlas param Rest i) (O0 i) :=
    (((hlocal i).1.comp ((hpsiBase i).mono inter_subset_left) (fun _ hz => hz.2)).congr (heq i))
  have hjets : ∀ i, ∀ k ≤ j, ∀ z ∈ S0 i,
      tau^k*‖iteratedFDeriv ℝ k (actualOriginalNativeTargetTensor atlas param Rest i) z‖ ≤ (CT*CR)*err := by
    intro i k hk z hz
    rw [(((heq i).eventuallyEq_of_mem ((hO0 i).mem_nhds (hS0 i hz))).iteratedFDeriv ℝ k).eq_of_nhds]
    have hh := actual_fast_joint_chart_transfer TP hTP k (psi i) (E0 i) (O0 i) (Omega i)
      (hO0 i) (hOmega i) ((hpsiBase i).mono inter_subset_left) (hlocal i).1 (fun _ hz => hz.2)
      z (hS0 i hz) tau ell (CR*err) htau htaul
      (fun k hkj => (hlocal i).2 k (hkj.trans hk) (psi i z) ⟨z,hz,rfl⟩)
      (fun k hk0 hkj => hParam i z hz k hk0 (hkj.trans hk))
    exact (hh.trans (mul_le_mul_of_nonneg_right
      (actualFastChartTransferCost_le_prefix TP hTP hk) (mul_nonneg hCR herr))).trans_eq (by ring)
  obtain ⟨hreg,hfinite,hbound⟩ := actual_original_tensor_weighted_norm_from_native_germs
    atlas param S O0 hO0 (fun _ => inter_subset_left) hS0 Rest j tau ((CT*CR)*err)
    htau (htaul.trans hell1) (mul_nonneg (mul_nonneg hCT hCR) herr) hsm hjets
  have hmember : Rest ∈ parameterRound2_originalTensorGermSpace atlas param S W := by
    constructor
    · intro i
      refine ⟨ae.symm ⁻¹' O0 i,(hO0 i).preimage ae.symm.continuous,?_,hreg i⟩
      intro y hy
      exact hS0 i (by change ae (ae.symm y) ∈ S i; simpa only [ae.apply_symm_apply] using hy)
    · intro z hz
      exact actualRepairModelFirstDefect_array_rest_symmetric (m := m) (fun z => F z.1 z.2) U phases tau R0 Q0 z.1 z.2
  exact ⟨hmember,hfinite,hbound.trans_eq (by dsimp only [C,CT,CR,err]; ring)⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_combined_original_remainder
