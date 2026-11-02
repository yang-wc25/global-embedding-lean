import IncrementsCompletion.ActivePrimaryMeanRawType
import IncrementsCompletion.AtScaleMeanCoordinates
import Repair.FullIncrementNovOpenMeanNorms

/-! Local-support-count version. Every actual coefficient and norm is literal.
 Actual raw mean size/difference bounds on the unchanged original norm.
The numerical cost is literally fullIncrementNovMeanNormCost; neither the
preparation scale nor the actual data enter it. Physical mean identities
use only the seven unchanged fields, while raw profiles carry the current
analysis-scale estimates. ENNReal finiteness precedes every real bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
universe uM uP uSub
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {Sub : Type uSub} [Fintype Sub]

theorem incrementsCompletion_active_raw_mean_original_norms
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source →
      ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (z.1,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (V0 : Set P) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub Lactive : ℕ) (preparedScale : ℝ)
    (prep : ∀ i, IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub preparedScale i)
    (n q j : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W0 := incrementsOriginalParameterRegion Data
    let C := fullIncrementNovMeanNormCost.{uM,uSub} (m := m) (d := d) (N := N) (M := M)
      n q j Rsub Lactive horder reserve Bnd Mg hc hBnd hMg T hT
    0 ≤ C ∧ ∀
      (input inputbar : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0)
      (G : Set (P × M)) (hG : IsOpen G) (hGR : G ⊆ W0)
      (tau ell Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hDelta : 0 ≤ Delta)
      (raw : IncrementsCompletionActiveMeanRawProfiles Data hd hs hn g V0 cT Tinv Forward Meta Rsub Lactive preparedScale prep
        G hG input.val inputbar.val n q j reserve Bnd Mg T tau ell Delta),
      let TA := fullIncrementNovPrimaryMeanError (fun p x => Data.F (p,x)) g input.val hActive (q+2) tau
      let TB := fullIncrementNovPrimaryMeanError (fun p x => Data.F (p,x)) g inputbar.val hActive (q+2) tau
      let O := incrementsOriginalDifferentiation Data.atlas Data.parameterChart
      let WA := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart TA) O S
      let WB := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart TB) O S
      let WD := paperAtlasWeighted 0 j ell
        (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun t x => TA t x-TB t x)) O S
      (TA ∈ parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0 ∧
        TB ∈ parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0) ∧
      (WA ≠ ⊤ ∧ WA.toReal ≤ C*(tau/ell)) ∧
      (WB ≠ ⊤ ∧ WB.toReal ≤ C*(tau/ell)) ∧
      (WD ≠ ⊤ ∧ WD.toReal ≤ C*(tau/ell)*Delta) := by
  intro S W0 C
  let Tprefix := parameterRound2_numericProfilePrefix (j+1) T
  have hTprefix := parameterRound2_numericProfilePrefix_nonneg (j+1) T hT
  let K := Classical.choose (parameterRound2_actual_raw_globalMean_array_uniform_index.{0,0,uM,0,0,0,uSub}
    (I := 𝓙) (M := M) («Ep» := Ep) (Tr := ℝ) (m := m) (N := N)
    n (q+2) j Rsub Lactive horder reserve Bnd Mg hc hBnd hMg Tprefix hTprefix)
  have hK : 0 ≤ K := (Classical.choose_spec (parameterRound2_actual_raw_globalMean_array_uniform_index.{0,0,uM,0,0,0,uSub}
    (I := 𝓙) (M := M) («Ep» := Ep) (Tr := ℝ) (m := m) (N := N)
    n (q+2) j Rsub Lactive horder reserve Bnd Mg hc hBnd hMg Tprefix hTprefix)).1
  have hraw := (Classical.choose_spec (parameterRound2_actual_raw_globalMean_array_uniform_index.{0,0,uM,0,0,0,uSub}
    (I := 𝓙) (M := M) («Ep» := Ep) (Tr := ℝ) (m := m) (N := N)
    n (q+2) j Rsub Lactive horder reserve Bnd Mg hc hBnd hMg Tprefix hTprefix)).2 (Λ := Fin Data.primaryCount) (Β := Sub)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by positivity) (linearModelFactor_nonneg _ _)) hK
  refine ⟨hC,?_⟩
  intro input inputbar G hG hGR tau ell Delta htau htaul hell1 hDelta raw TA TB O WA WB WD
  let a := parameterTensorModelEquiv (m+1) d
  let F := fun i : Fin Data.atlas.count × Fin Data.parameterCount => actualOriginalOpenParameterSlice Data i
  let hF := fun i : Fin Data.atlas.count × Fin Data.parameterCount => actualOriginalOpenParameterSlice_contMDiff Data hd hs i
  let eta := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta
  let g0 := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    actualOriginalPrimaryFamily Data hd hs hn i (prep i).host (prep i).native (prep i).slices
      (prep i).data (eta i) (prep i).active
  let W := fun ip => actualOriginalParameterNeighborhood Data ip G
  let hW := fun ip => actualOriginalParameterNeighborhood_isOpen Data ip G hG
  let gn := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    parameterRound2_restrictPrimaryFamily (F i) (g0 i) (W i.2) (hW i.2)
  let primary := fun (i : Fin Data.atlas.count × Fin Data.parameterCount) nu => W i.2 ∩ (fun w : Ep × M => ((Data.parameterChart i.2).symm w.1,w.2)) ⁻¹' Data.primaryDomain nu
  let Obs := fun i : Fin Data.atlas.count × Fin Data.parameterCount => actualRawObserverOpen (Data.atlas.chart i.1) (W i.2)
  have rawPrefix : IncrementsCompletionActiveMeanRawProfiles Data hd hs hn g V0 cT Tinv Forward Meta Rsub Lactive preparedScale prep
      G hG input.val inputbar.val n q j reserve Bnd Mg Tprefix tau ell Delta := by
    intro i
    exact ⟨{ Classical.choice (raw i) with
      hphib := by
        intro nu beta k hk hkj z hz
        simpa only [Tprefix,parameterRound2_numericProfilePrefix,ite_eq_left hkj] using
          (Classical.choice (raw i)).hphib nu beta k hk hkj z hz }⟩
  let data := fun i => Classical.choice (rawPrefix i)
  let muA := fun (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : X) (k : Fin ((m+1)*(m+1))) =>
    parameterRound2_globalObservedMeanCoefficient (F i) (hF i) (gn i)
      (actualOriginalParameterTensorSlice Data i input.val) (q+2) tau (Data.atlas.chart i.1) z
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  let muB := fun (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : X) (k : Fin ((m+1)*(m+1))) =>
    parameterRound2_globalObservedMeanCoefficient (F i) (hF i) (gn i)
      (actualOriginalParameterTensorSlice Data i inputbar.val) (q+2) tau (Data.atlas.chart i.1) z
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hh (i : Fin Data.atlas.count × Fin Data.parameterCount) := hraw (F i) (hF i) (gn i)
    (actualOriginalParameterTensorSlice Data i input.val) (actualOriginalParameterTensorSlice Data i inputbar.val)
    (W i.2) (primary i) (Data.atlas.chart i.1) (Obs i) (a ⁻¹' S i) tau ell Delta (data i)
  have hO (i) : IsOpen (Obs i) := (data i).hO
  have hSO (i) : a ⁻¹' S i ⊆ Obs i := (data i).hSO
  have hOsub (i) : Obs i ⊆ (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).target := by
    intro z hz
    exact ⟨((data i).hmapWO hz).1.1,hz.1.2⟩
  have heA (i) (y) (hy : a.symm y ∈ Obs i) :
      incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart TA i y = fun k => (muA i (a.symm y) k).re := by
    exact incrementsCompletion_at_scale_original_meanError_coordinates Data hd hs hn g hActive hPreserves
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub i preparedScale (prep i) G hG hGR input.val q hq tau htau
      (data i).prim y ⟨(hOsub i hy).2,(hOsub i hy).1⟩ ((data i).hmapWO hy)
  have heB (i) (y) (hy : a.symm y ∈ Obs i) :
      incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart TB i y = fun k => (muB i (a.symm y) k).re := by
    exact incrementsCompletion_at_scale_original_meanError_coordinates Data hd hs hn g hActive hPreserves
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub i preparedScale (prep i) G hG hGR inputbar.val q hq tau htau
      (data i).primbar y ⟨(hOsub i hy).2,(hOsub i hy).1⟩ ((data i).hmapWO hy)
  have heD (i) (y) (hy : a.symm y ∈ Obs i) :
      incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun t x => TA t x-TB t x) i y =
        fun k => (muA i (a.symm y) k-muB i (a.symm y) k).re := by
    funext k
    change incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart TA i y k -
      incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart TB i y k = _
    rw [congrFun (heA i y hy) k,congrFun (heB i y hy) k,Complex.sub_re]
  have hell : 0 < ell := htau.trans_le htaul
  have hKA : 0 ≤ K*(tau/ell) := mul_nonneg hK (div_nonneg htau.le hell.le)
  have hKD : 0 ≤ K*(tau/ell)*Delta := mul_nonneg hKA hDelta
  have ha := round3Parameter_original_tensor_norm_of_complex_germs Data.atlas Data.parameterChart TA S Obs hO hOsub hSO muA
    (fun i k => ((hh i).1 (finProdFinEquiv.symm k)).1) heA j ell (K*(tau/ell)) hell hell1 hKA
    (fun i k r hr z hz => (hh i).2.1 (finProdFinEquiv.symm k) r hr z hz)
  have hb := round3Parameter_original_tensor_norm_of_complex_germs Data.atlas Data.parameterChart TB S Obs hO hOsub hSO muB
    (fun i k => ((hh i).1 (finProdFinEquiv.symm k)).2) heB j ell (K*(tau/ell)) hell hell1 hKA
    (fun i k r hr z hz => (hh i).2.2.1 (finProdFinEquiv.symm k) r hr z hz)
  have hdif := round3Parameter_original_tensor_norm_of_complex_germs Data.atlas Data.parameterChart (fun t x => TA t x-TB t x)
    S Obs hO hOsub hSO (fun i z k => muA i z k-muB i z k)
    (fun i k => (((hh i).1 (finProdFinEquiv.symm k)).1).sub (((hh i).1 (finProdFinEquiv.symm k)).2))
    heD j ell (K*(tau/ell)*Delta) hell hell1 hKD
    (fun i k r hr z hz => (hh i).2.2.2 (finProdFinEquiv.symm k) r hr z hz)
  have hsample (i) : S i ⊆ a.symm ⁻¹' Obs i := by
    intro y hy
    apply hSO i
    change a (a.symm y) ∈ S i
    simpa using hy
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,⟨ha.2.1,ha.2.2.trans_eq ?_⟩,
    ⟨hb.2.1,hb.2.2.trans_eq ?_⟩,⟨hdif.2.1,hdif.2.2.trans_eq ?_⟩⟩
  · intro i
    exact ⟨a.symm ⁻¹' Obs i,(hO i).preimage a.symm.continuous,hsample i,ha.1 i⟩
  · intro z hz
    exact (fullIncrementNov_primary_meanAt_symmetric (fun p x => Data.F (p,x)) g hActive input.val (q+2) tau z.1 z.2).sub
      (input.property.2 z hz)
  · intro i
    exact ⟨a.symm ⁻¹' Obs i,(hO i).preimage a.symm.continuous,hsample i,hb.1 i⟩
  · intro z hz
    exact (fullIncrementNov_primary_meanAt_symmetric (fun p x => Data.F (p,x)) g hActive inputbar.val (q+2) tau z.1 z.2).sub
      (inputbar.property.2 z hz)
  all_goals dsimp only [C,fullIncrementNovMeanNormCost,K,Tprefix,hTprefix]; ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_active_raw_mean_original_norms
