import Smoothing.ParameterRound2MeanRawNative
import Smoothing.ParameterRound2MeanNativeGerms
import Probes.ActualJointTensorChartTransfer

/-! Complete raw-profile producer for the SAME native global mean in the
original paper norm. Each actual inverse parameter chart is composed before
any full-joint derivative is taken. No mean/error/coefficient/source/Free/R
output norm is an input. The exact native mean identity is proved from the
original qualitative primitive conditions stored in each raw profile. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N c : ℕ} {M Tr : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_actual_raw_mean_original_germ_norms_uniform
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (tau ell Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hDelta : 0 ≤ Delta)
    (Obs : Fin A.count × Fin c → Set X)
    (hObsSub : ∀ i, Obs i ⊆ (B i.2).source ×ˢ (A.chart i.1).target)
    (data : ∀ i : Fin A.count × Fin c,
      ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n (q+2) j Rsub Lprimary reserve Bnd Mg T
        F hF g input inputbar W primary (A.chart i.1)
        (Obs i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i))
        tau ell Delta)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k),
    let TA := incrementsGlobalPrimaryMeanError F hF g input (q+2) tau
    let TB := incrementsGlobalPrimaryMeanError F hF g inputbar (q+2) tau
    let O := incrementsOriginalDifferentiation A B
    let WA := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B TA) O S
    let WB := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B TB) O S
    let WD := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B (fun t x => TA t x-TB t x)) O S
    (∃ U : (Fin A.count × Fin c) → Set (Fin (m+1+d) → ℝ),
      (∀ i, IsOpen (U i) ∧ S i ⊆ U i ∧ U i ⊆ O i ∧
        ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B TA i) (U i) ∧
        ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B TB i) (U i))) ∧
    (WA ≠ ⊤ ∧ WA.toReal ≤ C*(tau/ell)) ∧
    (WB ≠ ⊤ ∧ WB.toReal ≤ C*(tau/ell)) ∧
    (WD ≠ ⊤ ∧ WD.toReal ≤ C*(tau/ell)*Delta) := by
  obtain ⟨K,hK,hraw⟩ := parameterRound2_actual_raw_globalMean_array_uniform
    (I := 𝓘(ℝ,D)) (M := M) («Ep» := Ep) (Tr := Tr) (m := m) (N := N) (Λ := Λ) (Β := Β)
    n (q+2) j Rsub Lprimary horder reserve Bnd Mg hc hBnd hMg T hT
  let CP := actualFastChartTransferPrefix TP j
  have hCP : 0 ≤ CP := actualFastChartTransferPrefix_nonneg TP hTP j
  let C := (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*(CP*K)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by positivity) (linearModelFactor_nonneg _ _))
    (mul_nonneg hCP hK)
  refine ⟨C,hC,?_⟩
  intro A B hA hB F hF g input inputbar W primary S hSO tau ell Delta htau htaul hell1 hDelta Obs hObsSub data hParam TA TB O WA WB WD
  let a := parameterTensorModelEquiv (m+1) d
  let phi := fun i : Fin A.count × Fin c => parameterRound2_meanParameterMap (m := m) (B i.2)
  let Ubase := fun i : Fin A.count × Fin c => (B i.2).target ×ˢ (A.chart i.1).target
  let V0 := Obs
  let U := fun i : Fin A.count × Fin c => Ubase i ∩ (phi i) ⁻¹' V0 i
  let S0 := fun i => a ⁻¹' S i
  let S1 := fun i => phi i '' S0 i
  have hUbase (i) : IsOpen (Ubase i) := (B i.2).open_target.prod (A.chart i.1).open_target
  have hV (i) : IsOpen (V0 i) := (data i).hO
  have hphiBase (i) : ContDiffOn ℝ ∞ (phi i) (Ubase i) :=
    (((contMDiffOn_symm_of_mem_maximalAtlas (hB i.2)).contDiffOn).comp
      contDiffOn_fst (fun _ hz => hz.1)).prodMk contDiffOn_snd
  have hU (i) : IsOpen (U i) := (hphiBase i).continuousOn.isOpen_inter_preimage (hUbase i) (hV i)
  have hSU : ∀ i, S0 i ⊆ U i := by
    intro i z hz
    have hh := hSO i hz
    have he : (incrementsOriginalParameterPoint (a z), incrementsOriginalSourcePoint (a z)) = z :=
      a.symm_apply_apply z
    refine ⟨?_,(data i).hSO ⟨z,hz,rfl⟩⟩
    rw [← he]
    exact ⟨hh.2,hh.1⟩
  have hphi (i) : ContDiffOn ℝ ∞ (phi i) (U i) := (hphiBase i).mono inter_subset_left
  have hmap (i) : MapsTo (phi i) (U i) (V0 i) := fun _ hz => hz.2
  have hh (i) := hraw F hF g input inputbar W primary (A.chart i.1)
    (V0 i) (S1 i) tau ell Delta (data i)
  let muA := fun (i : Fin A.count × Fin c) (z : X) (k : Fin ((m+1)*(m+1))) =>
    parameterRound2_globalObservedMeanCoefficient F hF g input (q+2) tau (A.chart i.1) z
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  let muB := fun (i : Fin A.count × Fin c) (z : X) (k : Fin ((m+1)*(m+1))) =>
    parameterRound2_globalObservedMeanCoefficient F hF g inputbar (q+2) tau (A.chart i.1) z
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  let ca := fun i z k => muA i (phi i z) k
  let cb := fun i z k => muB i (phi i z) k
  have hca (i k) : ContDiffOn ℝ ∞ (fun z => ca i z k) (U i) :=
    ((hh i).1 (finProdFinEquiv.symm k)).1.comp (hphi i) (hmap i)
  have hcb (i k) : ContDiffOn ℝ ∞ (fun z => cb i z k) (U i) :=
    ((hh i).1 (finProdFinEquiv.symm k)).2.comp (hphi i) (hmap i)
  have hell : 0 < ell := htau.trans_le htaul
  have heps : 0 ≤ tau/ell := div_nonneg htau.le hell.le
  have htransfer (i) (f : X → ℂ) (hf : ContDiffOn ℝ ∞ f (V0 i)) (K0 : ℝ) (hK0 : 0 ≤ K0)
      (hb : ∀ r ≤ j, ∀ z ∈ S1 i, ell^r*‖iteratedFDeriv ℝ r f z‖ ≤ K0) :
      ∀ r ≤ j, ∀ z ∈ S0 i, ell^r*‖iteratedFDeriv ℝ r (f ∘ phi i) z‖ ≤ CP*K0 := by
    intro r hr z hz
    have ht := actual_fast_joint_chart_transfer TP hTP r (phi i) f (U i) (V0 i)
      (hU i) (hV i) (hphi i) hf (hmap i) z (hSU i hz) ell ell K0 hell le_rfl
      (fun k hk => hb k (hk.trans hr) (phi i z) ⟨z,hz,rfl⟩)
      (fun k hk hkr => hParam i z hz k hk (hkr.trans hr))
    exact ht.trans (mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix TP hTP hr) hK0)
  have hbca (i k) : ∀ r ≤ j, ∀ z ∈ S0 i,
      ell^r*‖iteratedFDeriv ℝ r (fun w => ca i w k) z‖ ≤ CP*(K*(tau/ell)) :=
    htransfer i (fun z => muA i z k) ((hh i).1 (finProdFinEquiv.symm k)).1
      (K*(tau/ell)) (mul_nonneg hK heps) ((hh i).2.1 (finProdFinEquiv.symm k))
  have hbcb (i k) : ∀ r ≤ j, ∀ z ∈ S0 i,
      ell^r*‖iteratedFDeriv ℝ r (fun w => cb i w k) z‖ ≤ CP*(K*(tau/ell)) :=
    htransfer i (fun z => muB i z k) ((hh i).1 (finProdFinEquiv.symm k)).2
      (K*(tau/ell)) (mul_nonneg hK heps) ((hh i).2.2.1 (finProdFinEquiv.symm k))
  have hbcd (i k) : ∀ r ≤ j, ∀ z ∈ S0 i,
      ell^r*‖iteratedFDeriv ℝ r (fun w => ca i w k-cb i w k) z‖ ≤ CP*(K*(tau/ell)*Delta) :=
    htransfer i (fun z => muA i z k-muB i z k)
      (((hh i).1 (finProdFinEquiv.symm k)).1.sub ((hh i).1 (finProdFinEquiv.symm k)).2)
      (K*(tau/ell)*Delta) (mul_nonneg (mul_nonneg hK heps) hDelta)
      ((hh i).2.2.2 (finProdFinEquiv.symm k))
  have hW0 (i) (y) (hy : a.symm y ∈ U i) :
      incrementsOriginalJointPoint A B i y ∈ W :=
    (data i).hmapWO (x := phi i (a.symm y)) hy.2
  have hOrig (i) (y) (hy : a.symm y ∈ U i) :
      y ∈ incrementsOriginalDifferentiation A B i := ⟨hy.1.2,hy.1.1⟩
  have heqa (i y) (hy : a.symm y ∈ U i) :
      incrementsOriginalTensorCoordinates A B TA i y = fun k => (ca i (a.symm y) k).re :=
    parameterRound2_originalMeanCoordinates_eq A B hA F hF g input W primary
      (data i).prim q hq tau htau i y (hOrig i y hy) (hW0 i y hy)
  have heqb (i y) (hy : a.symm y ∈ U i) :
      incrementsOriginalTensorCoordinates A B TB i y = fun k => (cb i (a.symm y) k).re :=
    parameterRound2_originalMeanCoordinates_eq A B hA F hF g inputbar W primary
      (data i).primbar q hq tau htau i y (hOrig i y hy) (hW0 i y hy)
  have heqd (i y) (hy : a.symm y ∈ U i) :
      incrementsOriginalTensorCoordinates A B (fun t x => TA t x-TB t x) i y =
        fun k => (ca i (a.symm y) k-cb i (a.symm y) k).re := by
    have ha := heqa i y hy
    have hb := heqb i y hy
    change incrementsOriginalTensorCoordinates A B TA i y-incrementsOriginalTensorCoordinates A B TB i y = _
    rw [ha,hb]
    ext k
    simp only [Pi.sub_apply,Complex.sub_re]
  have hna := parameterRound2_original_tensor_norm_of_complex_germs A B TA S U hU
    (fun _ _ hz => hz.1) hSU ca hca heqa
    j ell (CP*(K*(tau/ell))) hell hell1 (mul_nonneg hCP (mul_nonneg hK heps)) hbca
  have hnb := parameterRound2_original_tensor_norm_of_complex_germs A B TB S U hU
    (fun _ _ hz => hz.1) hSU cb hcb heqb
    j ell (CP*(K*(tau/ell))) hell hell1 (mul_nonneg hCP (mul_nonneg hK heps)) hbcb
  have hnd := parameterRound2_original_tensor_norm_of_complex_germs A B (fun t x => TA t x-TB t x) S U hU
    (fun _ _ hz => hz.1) hSU
    (fun i z k => ca i z k-cb i z k) (fun i k => (hca i k).sub (hcb i k)) heqd
    j ell (CP*(K*(tau/ell)*Delta)) hell hell1 (mul_nonneg hCP (mul_nonneg (mul_nonneg hK heps) hDelta)) hbcd
  refine ⟨⟨fun i => a.symm ⁻¹' U i,?_⟩,⟨hna.2.1,?_⟩,⟨hnb.2.1,?_⟩,⟨hnd.2.1,?_⟩⟩
  · intro i
    refine ⟨(hU i).preimage a.symm.continuous,?_,fun y hy => hOrig i y hy,hna.1 i,hnb.1 i⟩
    intro y hy
    exact hSU i (by change a (a.symm y) ∈ S i; simpa only [a.apply_symm_apply] using hy)
  · exact hna.2.2.trans_eq (by dsimp only [C]; ring)
  · exact hnb.2.2.trans_eq (by dsimp only [C]; ring)
  · exact hnd.2.2.trans_eq (by dsimp only [C]; ring)

#print axioms parameterRound2_actual_raw_mean_original_germ_norms_uniform
end GlobalEmbedding.Continuation
