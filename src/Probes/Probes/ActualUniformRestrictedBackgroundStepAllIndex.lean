import Probes.ActualUniformRestrictedBackgroundStatementAllIndex

/-! The actual raw finite construction is inserted into the literal repair
normalization. The resulting estimate contains only the original smoother
tails and the proved finite-increment rate. The SAME Kq, host choices and U
precede all later derivative orders. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
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

theorem actual_original_uniform_restricted_background_repair_step_all_index
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Brest Mrest Kcut : ℕ → ℝ)
    (hBmean : ∀ s R, 0 ≤ Bmean s R) (hMmean : ∀ s, 0 ≤ Mmean s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (hBrest : ∀ s, 0 ≤ Brest s) (hMrest : ∀ s, 0 ≤ Mrest s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k) :
    ActualUniformRestrictedBackgroundRepairStatementAllIndex (m := m) (d := d) (N := N) (M := M)
      (Tr := Tr) 
      B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc Bmean Mmean Dinput Brest Mrest Kcut
      hBmean hMmean hDinput hBrest hMrest hKcut T Tinv Tobs TP hT hTinv hTobs hTP := by
  have hincrement := actual_original_uniform_restricted_raw_germ_finite_increment_all_index
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr) 
    B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc
    Bmean Mmean Dinput Brest Mrest Kcut hBmean hMmean hDinput hBrest hMrest hKcut
    T Tinv Tobs TP hT hTinv hTobs hTP
  unfold ActualUniformRestrictedRawGermFiniteStatementAllIndex at hincrement
  unfold ActualUniformRestrictedBackgroundRepairStatementAllIndex
  obtain ⟨C,hC,epsilon0,he0,he01,hinc⟩ := hincrement
  refine ⟨C,hC,epsilon0,he0,he01,?_⟩
  intro Label SubPrimary SubSecondary _ _ _ _ c A B hA hB S W hS hSO ell hell hell1 H p hH hParam F hF g primary hSupply
  obtain ⟨hsm,hfinite⟩ := hinc Label SubPrimary SubSecondary c A B hA hB S W hS hSO ell hell hell1 H hH hParam F hF g primary hSupply
  refine ⟨hsm,?_⟩
  intro epsilon he he0lt Top K
  have hi := hfinite epsilon he he0lt
  refine ⟨hi.1,?_⟩
  intro Gdomain hGdomain hGW hSGgerm gG delta hdelta hdeltatau choice U j inputbar Delta raw Obs obs
    G SG hG hSG hBackground hstar h0 SH deltaNext hdeltaNe hdeltaNext htarget Hold Hnext O WT WM hTail hTf hMf
  have hconstructed := hi.2 Gdomain hGdomain hGW hSGgerm delta hdelta hdeltatau choice j inputbar Delta raw Obs obs
  let HG : parameterRound2_originalTensorGermSpace A B S Gdomain :=
    ⟨H.val,⟨H.property.1,fun z hz => H.property.2 z (hGW hz)⟩⟩
  have htransfer := parameterRound2_metric_error_background_germ_transfer A B S Gdomain hSO HG
    (fun z => F z.1 z.2) SG U delta Gdomain hGdomain hSGgerm hBackground hconstructed.1
  dsimp only [HG] at htransfer
  have hEreg : ∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B
        (incrementsOriginalMetricError SG U
          (fun t x => SH t x-(deltaNext/delta)^2 • h0 t x) delta) i) V0 := by
    simpa only [htarget] using htransfer.1.1
  have heq := htransfer.2 0 j (epsilon*ell)
  change WT (incrementsOriginalMetricError SG U H.val delta) =
    WT (incrementsOriginalMetricError (fun z => F z.1 z.2) U H.val delta) at heq
  have hEf0 : WT (incrementsOriginalMetricError SG U H.val delta) ≠ ⊤ := by
    rw [heq]
    exact hconstructed.2.1.1
  have hEf : WT (incrementsOriginalMetricError SG U
      (fun t x => SH t x-(deltaNext/delta)^2 • h0 t x) delta) ≠ ⊤ := by
    simpa only [htarget] using hEf0
  have hEb0 : (WT (incrementsOriginalMetricError SG U H.val delta)).toReal ≤
      C j*(delta*((epsilon*ell)/ell)^q+delta^3/(epsilon*ell)) := by
    rw [heq]
    exact hconstructed.2.1.2
  have hEb : (WT (incrementsOriginalMetricError SG U
      (fun t x => SH t x-(deltaNext/delta)^2 • h0 t x) delta)).toReal ≤
      C j*(delta*((epsilon*ell)/ell)^q+delta^3/(epsilon*ell)) := by
    simpa only [htarget] using hEb0
  have htau : 0 < epsilon*ell := mul_pos he hell
  have htau1 : epsilon*ell ≤ 1 :=
    (mul_le_mul_of_nonneg_right (he0lt.le.trans he01) hell.le |>.trans_eq (one_mul ell)).trans hell1
  exact actual_repair_germ_finite_increment_consumer A B hA S hSO G SG U
    hG hSG hconstructed.2.2.1 hstar h0 SH delta deltaNext (epsilon*ell)
    hdeltaNe hdelta hdeltaNext htau htau1 j (C j) (C j)
    (delta*((epsilon*ell)/ell)^q+delta^3/(epsilon*ell)) (hC j)
    hTail hEreg hTf hMf hEf hEb hconstructed.2.2.2.2.1 hconstructed.2.2.2.2.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_uniform_restricted_background_repair_step_all_index
