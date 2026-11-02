import Smoothing.ParameterRound2MeanRawPreparedCanonicalSupply
import Smoothing.ParameterRound2RawUniformIterateProfilesIndex
import Smoothing.ParameterRound2MeanRawGermFixedCostIndex
import Smoothing.ParameterRound2MeanRawGermPairEstimatesIndex
import Smoothing.ParameterRound2MeanGermOperatorNorms

/-! Actual local mean estimates on the ORIGINAL symmetric C0 reserve.
The size and Lipschitz constants are derived from concrete primitive profiles.
No estimate for T, the mean, or any finite residual is supplied. Every input
and difference size is the original weighted tensor seminorm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

universe uM uTr uΛ uΒ

variable {m d N c : ℕ} {M : Type uM} {Tr : Type uTr} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ : Type uΛ} {Β : Type uΒ} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_actual_final_prepared_raw_profiles_index
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W Vprep : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ) (hrho : 0 < rho) (B0 : ℕ → ℝ)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) :
    let C := fun s R => parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s) hc (hBnd s R) (hMg s) T TP hT hTP
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    ∀ (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (Ep × M)),
    ParameterRound2MeanRawPreparedCanonicalSupply (Tr := Tr) A B S W Vprep p H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell →
    ∀ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    (∀ s, p s H ≤ B0 s) →
    ∀ epsilon, 0 < epsilon →
      epsilon < parameterRound2_uniformMeanThreshold B0 C rho q (q+4) →
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    let K := fun i => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    let Rq := parameterRound2_uniformMeanProfile B0 C (q+4) q
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
    (∀ s, p s (K q) ≤ Rq s) ∧
    ∃ G : Set (Ep × M), ∃ hG : IsOpen G, G ⊆ W ∧ G ⊆ Vprep ∧
      (∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G) ∧
      (∀ i : Fin A.count × Fin c, actualRawObserverOpen (A.chart i.1) G ⊆ (B i.2).source ×ˢ (A.chart i.1).target) ∧
      ∀ s, Nonempty (∀ i : Fin A.count × Fin c,
        ParameterRound2GlobalMeanRawProfiles (Tr := Tr) (s+(q+4)) (q+2) s Rsub Lprimary
          reserve (Bnd s (Rq (s+(q+4)))) (Mg s) T F hF
          (parameterRound2_restrictPrimaryFamily F g G hG) (K q).val (K q).val G primary (A.chart i.1)
          (actualRawObserverOpen (A.chart i.1) G) (parameterRound2_meanParameterMap (m := m) (B i.2) ''
            ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) (epsilon*ell) ell 0) := by
  intro C p F hF g primary hStrong hsm hH epsilon he he0 Top K Rq
  have hCanon := parameterRound2_prepared_canonical_supply_to_canonical_supply
    A B S W Vprep p H rho q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell hStrong
  have hFixed := parameterRound2_canonical_neighborhood_supply_to_fixed_supply
    A B S W p H rho q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell hCanon
  have hSupply := parameterRound2_fixed_neighborhood_supply_to_germ_supply
    A B S W p H rho q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell hFixed
  have hprof := parameterRound2_actual_raw_uniform_iterate_profiles_index
    (N := N) (Tr := Tr) (Λ := Λ) (Β := Β)
    A B hA hB S W hS hSO ell hell hell1 H rho hrho B0 q Rsub Lprimary hq reserve hc
    Bnd Mg Dinput hBnd hMg hDinput T TP hT hTP hParam F hF g primary hSupply hsm hH epsilon he he0
  have hdom : p 0 (K q-H) < rho := (hprof.1 q le_rfl).trans_lt (by linarith)
  let Kfinal : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho} := ⟨K q,hdom⟩
  obtain ⟨G,hG,hGW,hPrep,hSG,hObs,hraw⟩ := hStrong Kfinal Kfinal
  refine ⟨hprof.1,hprof.2 q le_rfl,G,hG,hGW,hPrep,hSG,hObs,?_⟩
  intro s
  have he1 : epsilon ≤ 1 := he0.le.trans (parameterRound2_uniformMeanThreshold_pos B0 C rho hrho q (q+4)).2
  have hs := hraw epsilon he he1 s (Rq (s+(q+4)))
    (hprof.2 q le_rfl (s+(q+4))) (hprof.2 q le_rfl (s+(q+4)))
  have hzero : Dinput s*p (s+(q+4)) (Kfinal.val-Kfinal.val) = 0 := by
    rw [sub_self,map_zero,mul_zero]
  rw [hzero] at hs
  exact hs

#print axioms parameterRound2_actual_final_prepared_raw_profiles_index
end GlobalEmbedding.Continuation
