import Probes.ActualUniformRestrictedSmoothedStatement

/-! Same joint smoother, actual finite mean iteration and literal U1+U2
produce the original repair update without any desired output error budget. -/

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

local instance actualUniformRestrictedSmoothedRepairStepChartedSpace : ChartedSpace (Ep × D) (Ep × M) :=
  prodChartedSpace Ep Ep D M
local instance actualUniformRestrictedSmoothedRepairStepIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (Ep × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) Ep M

theorem actual_original_uniform_restricted_smoothed_repair_step
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
    ActualUniformRestrictedSmoothedRepairStatement (m := m) (d := d) (N := N) (c := c) (M := M)
      (Tr := Tr) (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
      B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc Bmean Mmean Dinput Brest Mrest Kcut
      hBmean hMmean hDinput hBrest hMrest hKcut T Tinv Tobs TP hT hTinv hTobs hTP
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius := by
  have hraw := actual_original_uniform_restricted_background_repair_step
    (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr)
    (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
    B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc
    Bmean Mmean Dinput Brest Mrest Kcut hBmean hMmean hDinput hBrest hMrest hKcut
    T Tinv Tobs TP hT hTinv hTobs hTP
  unfold ActualUniformRestrictedBackgroundRepairStatement at hraw
  unfold ActualUniformRestrictedSmoothedRepairStatement
  obtain ⟨Ci,hCi,epsilon0,he0,he01,hrepair⟩ := hraw
  have hs (j : ℕ) := exists_uniform_parameterRound2_local_set_pair_smoothing
    (n := m+1) (d := d) (N := N) (M := M) (P := Ep)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius j q
  let Cs : ℕ → ℝ := fun j => Classical.choose (hs j)
  have hCs (j) : 0 ≤ Cs j := (Classical.choose_spec (hs j)).1
  have hSmooth (j) := (Classical.choose_spec (hs j)).2
  let C := fun j => Ci j+Cs j+actualRepairCrossCost (m+1) d N j*Cs j*Ci j
  have hC (j) : 0 ≤ C j := add_nonneg (add_nonneg (hCi j) (hCs j))
    (mul_nonneg (mul_nonneg (actualRepairCrossCost_nonneg _ _ _ _) (hCs j)) (hCi j))
  refine ⟨C,hC,epsilon0,he0,he01,?_⟩
  intro A B hA hB S W hS hSO ell hell hell1 H p hH hParam
    parameterSet RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter hSinner
  intro t helt ht1 G hG hstar h0 hstarReg delta deltaNext hd hn Hold budget hbudget
    mu kernel chi SF SH htarget
  have hGcoords := parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB G hG
  have hHold := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn
    A B.chart hA hB G hG hstar hstarReg delta
  have hzero := hSmooth 0 c A B hA hB parameterSet RS RP hbuffer
    Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter S hSinner
    ell ell t hell le_rfl helt ht1 G hGcoords Hold hHold budget hbudget
  have hSF : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ SF := hzero.1
  have hSH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
      (incrementsOriginalDifferentiation A B.chart i) := hzero.2.1
  intro F hF g primary hSupply
  obtain ⟨hsm,hfinite⟩ := hrepair A B.chart hA hB S W hS hSO ell hell hell1 H hH hParam
    F hF g primary hSupply
  refine ⟨hsm,?_⟩
  intro epsilon he he0lt hdeltatau Top K
  have hi := hfinite epsilon he he0lt
  refine ⟨hi.1,?_⟩
  intro Gdomain hGdomain hGW hSGgerm hBackground gG choice U j inputbar Delta raw Obs obs Hnext O WT
  let tau := epsilon*ell
  let tail := budget*(ell/t)^q+
    (parameterLocalOriginalTotalPairWeighted A B G Hold j t
      (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal*(tau/t)^q
  let rate := delta*(tau/ell)^q+delta^3/tau
  have htau : 0 < tau := mul_pos he hell
  have htaul : tau ≤ ell := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (he0lt.le.trans he01) hell.le
  have hsj := hSmooth j c A B hA hB parameterSet RS RP hbuffer
    Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter S hSinner
    tau ell t htau htaul helt ht1 G hGcoords Hold hHold budget hbudget
  have hTail : ∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart (fun b x => Hold b x-SH b x) i) V0 :=
    fun i => ⟨O i,parameterRound2_originalDifferentiation_open A B.chart i,hSO i,(hHold i).sub (hSH i)⟩
  have hTle : WT (fun b x => Hold b x-SH b x) ≤
      parameterLocalOriginalTotalPairWeighted A B (fun z => G z-SF z) (fun b x => Hold b x-SH b x) j tau S :=
    le_add_left le_rfl
  have hMle : paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates A B.chart (fun z => G z-SF z)) O S ≤
      parameterLocalOriginalTotalPairWeighted A B (fun z => G z-SF z) (fun b x => Hold b x-SH b x) j tau S :=
    le_add_right le_rfl
  have hTf := ne_top_of_le_ne_top hsj.2.2.1 hTle
  have hMf := ne_top_of_le_ne_top hsj.2.2.1 hMle
  have hTb : (WT (fun b x => Hold b x-SH b x)).toReal ≤ Cs j*tail :=
    (ENNReal.toReal_mono hsj.2.2.1 hTle).trans hsj.2.2.2.1
  have hMb : (paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates A B.chart (fun z => G z-SF z)) O S).toReal ≤ Cs j*tail :=
    (ENNReal.toReal_mono hsj.2.2.1 hMle).trans hsj.2.2.2.1
  have hout := hi.2 Gdomain hGdomain hGW hSGgerm delta hd.le hdeltatau choice j inputbar Delta raw Obs obs G SF hGcoords
    (parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB SF hSF)
    hBackground hstar h0 SH deltaNext hd.ne' hn htarget hTail hTf hMf
  refine ⟨hout.1,hout.2.1,hout.2.2.trans ?_⟩
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  have ht : 0 < t := hell.trans_le helt
  have htail0 : 0 ≤ tail := by dsimp only [tail]; positivity
  have hrate0 : 0 ≤ rate := by dsimp only [rate]; positivity
  have hcx := actualRepairCrossCost_nonneg (m+1) d N j
  have htriple : 0 ≤ actualRepairCrossCost (m+1) d N j*Cs j*Ci j :=
    mul_nonneg (mul_nonneg hcx (hCs j)) (hCi j)
  have hCiC : Ci j ≤ C j := by dsimp only [C]; linarith [hCs j]
  have hCsC : Cs j ≤ C j := by dsimp only [C]; linarith [hCi j]
  have hCrossC : actualRepairCrossCost (m+1) d N j*Cs j*Ci j ≤ C j := by
    dsimp only [C]; linarith [hCi j,hCs j]
  have hb1 : Ci j*rate ≤ C j*rate := mul_le_mul_of_nonneg_right hCiC hrate0
  have hb2 : delta^2*(WT (fun b x => Hold b x-SH b x)).toReal ≤ C j*delta^2*tail := by
    calc
      _ ≤ delta^2*(Cs j*tail) := mul_le_mul_of_nonneg_left hTb (sq_nonneg _)
      _ ≤ delta^2*(C j*tail) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hCsC htail0) (sq_nonneg _)
      _ = _ := by ring
  have hb3 : actualRepairCrossCost (m+1) d N j*
      (paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates A B.chart (fun z => G z-SF z)) O S).toReal*(Ci j*delta) ≤
      C j*delta*tail := by
    calc
      _ ≤ actualRepairCrossCost (m+1) d N j*(Cs j*tail)*(Ci j*delta) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMb hcx) (mul_nonneg (hCi j) hd.le)
      _ = (actualRepairCrossCost (m+1) d N j*Cs j*Ci j)*delta*tail := by ring
      _ ≤ C j*delta*tail := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCrossC hd.le) htail0
  calc
    _ ≤ (deltaNext^2)⁻¹*(C j*(rate+(delta^2+delta)*tail)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
      nlinarith [hb1,hb2,hb3]
    _ = _ := by ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_uniform_restricted_smoothed_repair_step
