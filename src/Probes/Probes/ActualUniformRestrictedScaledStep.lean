import Probes.ActualUniformRestrictedScaledStatement

/-! The literal same smoothed finite construction now has the original
normalized six-exponent estimate, without any metric-error budget premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M Tr Label SubPrimary SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

local instance actualUniformRestrictedScaledRepairStepChartedSpace : ChartedSpace (Ep × D) (Ep × M) :=
  prodChartedSpace Ep Ep D M
local instance actualUniformRestrictedScaledRepairStepIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (Ep × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) Ep M

theorem actual_original_uniform_restricted_scaled_repair_step
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Brest Mrest Kcut : ℕ → ℝ)
    (hBmean : ∀ s R, 0 ≤ Bmean s R) (hMmean : ∀ s, 0 ≤ Mmean s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (hBrest : ∀ s, 0 ≤ Brest s) (hMrest : ∀ s, 0 ≤ Mrest s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) :
    ActualUniformRestrictedScaledRepairStatement (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr)
      (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
      B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc
      Bmean Mmean Dinput Brest Mrest Kcut hBmean hMmean hDinput hBrest hMrest hKcut
      T Tinv Tobs TP hT hTinv hTobs hTP BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius := by
  have hsmoothed := actual_original_uniform_restricted_smoothed_repair_step
    (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr)
      (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
      B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc
      Bmean Mmean Dinput Brest Mrest Kcut hBmean hMmean hDinput hBrest hMrest hKcut
      T Tinv Tobs TP hT hTinv hTobs hTP BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius
  unfold ActualUniformRestrictedSmoothedRepairStatement at hsmoothed
  unfold ActualUniformRestrictedScaledRepairStatement
  obtain ⟨C,hC,epsilon0,he0,he01,hsm⟩ := hsmoothed
  refine ⟨C,hC,epsilon0,he0,he01,?_⟩
  intro A B hA hB S W hS hSO ell hell hell1 H p hH hParam
    parameterSet RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter hSinner
  intro t helt ht1 G hG hstar h0 hstarReg delta deltaNext hd hn Hold budget hbudget
    mu kernel chi SF SH htarget
  have hfamily := hsm A B hA hB S W hS hSO ell hell hell1 H hH hParam
    parameterSet RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter hSinner
    t helt ht1 G hG hstar h0 hstarReg delta deltaNext hd hn budget hbudget htarget
  intro F hF g primary hSupply
  obtain ⟨hsm,hfinite⟩ := hfamily F hF g primary hSupply
  refine ⟨hsm,?_⟩
  intro epsilon he he0lt hdeltatau Top K
  have hi := hfinite epsilon he he0lt hdeltatau
  refine ⟨hi.1,?_⟩
  intro Gdomain hGdomain hGW hSGgerm hBackground gG choice U j inputbar Delta raw Obs obs Hnext O WT
  have hout := hi.2 Gdomain hGdomain hGW hSGgerm hBackground choice j inputbar Delta raw Obs obs
  refine ⟨hout.1,hout.2.1,?_⟩
  intro k s hk hs hqscale hellscale hdscale htauscale hrescale inherited
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  have hscale := actual_repair_stage_scalar_bounds
    (C := C j) (budget := budget) (inherited := inherited)
    (delta := delta) (ell := ell) (tau := epsilon*ell) (deltaNext := deltaNext) (q := q)
    (hell.trans_le helt) ht1 (hC j) hbudget0 ENNReal.toReal_nonneg
    k s hk hs hqscale hellscale hdscale htauscale hrescale
  exact ⟨hout.2.2.trans hscale.1,fun hsk => hout.2.2.trans_eq (hscale.2 hsk)⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_uniform_restricted_scaled_repair_step
