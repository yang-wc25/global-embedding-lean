import Probes.ActualUniformPreparedPrimaryStatementAllIndex

/-! Complete actual finite increment with uniform constants selected before
all atlases, normalized targets and smoothing scales. The numerical target
slow profile is supplied by the SAME actual smoothing gain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
universe uM uTr uLabel uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {Tr : Type uTr}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem actual_original_uniform_prepared_primary_finite_increment_all_index
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Msecondary Kcut : ℕ → ℝ)
    (hBmean : ∀ s R, 0 ≤ Bmean s R) (hMmean : ∀ s, 0 ≤ Mmean s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (hMsecondary : ∀ s, 0 ≤ Msecondary s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k) :
    ActualUniformPreparedPrimaryFiniteStatementAllIndex (m := m) (d := d) (N := N) (M := M)
      (Tr := Tr)
      B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc Bmean Mmean Dinput Msecondary Kcut
      hBmean hMmean hDinput hMsecondary hKcut T Tinv Tobs TP hT hTinv hTobs hTP := by
  unfold ActualUniformPreparedPrimaryFiniteStatementAllIndex
  intro Csize Rq Brest Mrest
  have hBrest (j) : 0 ≤ Brest j := hBmean _ _
  have hMrest (j) : 0 ≤ Mrest j := (hMmean _).trans (le_max_left _ _)
  have hbase := actual_original_uniform_restricted_raw_germ_finite_increment_all_index
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
   
    B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc Bmean Mmean Dinput Brest Mrest Kcut
    hBmean hMmean hDinput hBrest hMrest hKcut T Tinv Tobs TP hT hTinv hTobs hTP
  unfold ActualUniformRestrictedRawGermFiniteStatementAllIndex at hbase
  obtain ⟨C,hC,epsilon0,he0,he01,hbase⟩ := hbase
  let threshold := parameterRound2_uniformMeanThreshold B0 Csize rho q (q+4)
  have hthreshold := parameterRound2_uniformMeanThreshold_pos B0 Csize rho hrho q (q+4)
  refine ⟨C,hC,min epsilon0 threshold,lt_min he0 hthreshold.1,
    (min_le_left _ _).trans he01,?_⟩
  intro Label SubPrimary SubSecondary _ _ _ _ c A B hA hB S W Vprep hS hSO ell hell hell1 H p hH hParam F hF g primary hStrong
  have hCanonical := parameterRound2_prepared_canonical_supply_to_canonical_supply
    A B S W Vprep p H rho q Rsub Lprimary reserve Bmean Mmean Dinput T F hF g primary ell hStrong
  have hFixed := parameterRound2_canonical_neighborhood_supply_to_fixed_supply
    A B S W p H rho q Rsub Lprimary reserve Bmean Mmean Dinput T F hF g primary ell hCanonical
  have hSupply := parameterRound2_fixed_neighborhood_supply_to_germ_supply
    A B S W p H rho q Rsub Lprimary reserve Bmean Mmean Dinput T F hF g primary ell hFixed
  obtain ⟨hsm,hfinite⟩ := hbase Label SubPrimary SubSecondary c A B hA hB S W hS hSO ell hell hell1 H hH hParam F hF g primary hSupply
  refine ⟨hsm,?_,?_⟩
  · intro epsilon he heFinal
    exact hfinite epsilon he (heFinal.trans_le (min_le_left _ _))
  · intro epsilon he heFinal Top K
    have heThreshold : epsilon < threshold := heFinal.trans_le (min_le_right _ _)
    have hprof := parameterRound2_actual_final_prepared_raw_profiles_index
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr) (Λ := Label) (Β := SubPrimary)
      A B hA hB S W Vprep hS hSO ell hell hell1 H rho hrho B0 q Rsub Lprimary hq reserve hc
      Bmean Mmean Dinput hBmean hMmean hDinput T TP hT hTP hParam F hF g primary
      hStrong hsm hH epsilon he heThreshold
    obtain ⟨hreserve,hKprofile,G,hG,hGW,hGPrep,hSG,hObs,hraw⟩ := hprof
    refine ⟨hreserve,hKprofile,G,hG,hGW,hGPrep,hSG,hObs,?_⟩
    intro j
    let s := actualSecondarySolveOrder q j
    have hn : s+(q+4) = actualSecondaryInputOrder q j := by
      dsimp only [s,actualSecondarySolveOrder,actualSecondaryInputOrder]
      omega
    obtain ⟨data⟩ := hraw s
    refine ⟨fun i => ?_⟩
    have hi := actual_raw_profiles_enlarge_budgets
      (s+(q+4)) (q+2) s Rsub Lprimary reserve
      (Bmean s (Rq (s+(q+4)))) (Mmean s) (Brest j) (Mrest j) T
      (by simp only [hn,Brest,s]; exact le_rfl)
      (show Mmean s ≤ Mrest j from le_max_left _ _)
      F hF (parameterRound2_restrictPrimaryFamily F g G hG) (K q).val (K q).val G primary
      (A.chart i.1) (actualRawObserverOpen (A.chart i.1) G)
      (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i))
      (epsilon*ell) ell 0 (data i)
    simpa only [hn,s] using hi

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_uniform_prepared_primary_finite_increment_all_index
