import Probes.ActualUniformRestrictedPairStatement

/-! The SAME smoothed finite update obeys the original full pair recurrence.
Every norm of U and the actual normalized metric defect is supplied by the
raw construction internally, including the correctly shifted base-two map. -/

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

local instance actualUniformRestrictedPairRepairStepChartedSpace : ChartedSpace (Ep × D) (Ep × M) :=
  prodChartedSpace Ep Ep D M
local instance actualUniformRestrictedPairRepairStepIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (Ep × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) Ep M

theorem actual_original_uniform_restricted_pair_repair_step
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
    ActualUniformRestrictedPairRepairStatement (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr)
      (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
      B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc
      Bmean Mmean Dinput Brest Mrest Kcut hBmean hMmean hDinput hBrest hMrest hKcut
      T Tinv Tobs TP hT hTinv hTobs hTP BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius := by
  have hscaled := actual_original_uniform_restricted_scaled_repair_step
    (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr)
      (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
      B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc
      Bmean Mmean Dinput Brest Mrest Kcut hBmean hMmean hDinput hBrest hMrest hKcut
      T Tinv Tobs TP hT hTinv hTobs hTP BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius
  unfold ActualUniformRestrictedScaledRepairStatement at hscaled
  unfold ActualUniformRestrictedPairRepairStatement
  obtain ⟨Cd,hCd,epsilon0,he0,he01,hstep⟩ := hscaled
  have hu (j : ℕ) := actual_original_increment_raw_base_two_norm_uniform
    (m := m) (d := d) (N := N) (pcount := c) (M := M) (Tr := Tr)
    (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
    (actualSecondaryInputOrder q (j+1)) (actualSecondarySolveOrder q (j+1)) j q Rsub Lprimary Rsecondary hq
    (by dsimp only [actualSecondarySolveOrder]; omega)
    (by dsimp only [actualSecondarySolveOrder,actualSecondaryInputOrder]; omega)
    reserve (Brest (j+1)) (Mrest (j+1)) (Kcut (j+1)) hc (hBrest (j+1)) (hMrest (j+1)) (hKcut (j+1))
    T Tinv Tobs TP hT hTinv hTobs hTP
  let Cu : ℕ → ℝ := fun j => Classical.choose (hu j)
  have hCu (j) : 0 ≤ Cu j := (Classical.choose_spec (hu j)).1
  have hUbound (j) := (Classical.choose_spec (hu j)).2
  let C := fun j => Cd j+Cu j
  have hC (j) : 0 ≤ C j := add_nonneg (hCd j) (hCu j)
  refine ⟨C,hC,epsilon0,he0,he01,?_⟩
  intro A B hA hB S W hS hSO ell hell hell1 H p hH hParam
    parameterSet RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter hSinner
  intro t helt ht1 G hG hstar h0 hstarReg h0Reg delta deltaNext hd hn Hold budget hbudget
    mu kernel chi SF SH htarget
  have hfamily := hstep A B hA hB S W hS hSO ell hell hell1 H hH hParam
    parameterSet RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter hSinner
    t helt ht1 G hG hstar h0 hstarReg delta deltaNext hd hn budget hbudget htarget
  intro F hF g primary hSupply
  obtain ⟨hsm,hfinite⟩ := hfamily F hF g primary hSupply
  refine ⟨hsm,?_⟩
  intro epsilon he he0lt hdeltatau Top K
  have hi := hfinite epsilon he he0lt hdeltatau
  refine ⟨hi.1,?_⟩
  intro Gdomain hGdomain hGW hSGgerm hBackground gG choice U j inputbar Delta raw Obs obs inputbarHigher DeltaHigher rawHigher ObsHigher obsHigher Hnext O nextPair
  have hout := hi.2 Gdomain hGdomain hGW hSGgerm hBackground choice j inputbar Delta raw Obs obs
  have ht : 0 < t := hell.trans_le helt
  have htau : 0 < epsilon*ell := mul_pos he hell
  have htaul : epsilon*ell ≤ ell := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (he0lt.le.trans he01) hell.le
  have hUm := hUbound j A B.chart hA hB F hF gG (K q).val inputbarHigher
    Gdomain primary S hSO ell delta (epsilon*ell) DeltaHigher htau htaul hell1 hd.le hdeltatau
    choice rawHigher ObsHigher obsHigher (fun i z hz r hr _ => hParam i z hz r hr)
  let f := incrementsOriginalMapCoordinates A B.chart G
  let u := incrementsOriginalMapCoordinates A B.chart U
  let ref := incrementsOriginalTensorCoordinates A B.chart h0
  let defect := incrementsOriginalTensorCoordinates A B.chart (fun b x => Hnext b x-h0 b x)
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B.chart
  have hGcoords := parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB G hG
  have hHold := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn
    A B.chart hA hB G hG hstar hstarReg delta
  have hfull := parameterRound2_original_pair_on_compact_finite A B Omega Q
    hOmega hQ hOmegaTarget hQTarget G hGcoords Hold hHold j t
  have hdomains : ∀ i, S i ⊆ incrementsOriginalEvaluation A B.chart Omega Q univ i := by
    intro i y hy
    have hh := hSinner i hy
    exact ⟨hh.1,hsource i.1 (bufferedInner_subset_sampling A i.1 hh.2.1),
      hparameter i.2 (tensorLocalInner_subset_sampling B i.2 hh.2.2.1),Set.mem_univ _⟩
  have hFle : paperAtlasWeighted 2 j t f O S ≤ parameterLocalOriginalTotalPairWeighted A B G Hold j t
      (incrementsOriginalEvaluation A B.chart Omega Q univ) :=
    (paperAtlasWeighted_mono_evaluation 2 j t f O S _ hdomains).trans (le_add_right le_rfl)
  have hFfinite := ne_top_of_le_ne_top hfull hFle
  have hRefFinite := parameterRound2_paperAtlasCj_finite_of_compact ref O S hO hS hSO h0Reg j
  have hFsmall := ne_top_of_le_ne_top hFfinite
    (parameterRound2_paperAtlasWeighted_mono_scale 2 j (epsilon*ell) t (htaul.trans helt) f O S)
  have hRefSmall := parameterRound2_paperAtlasWeighted_finite_of_topOrder 0 j (epsilon*ell) ref O S (by simpa using hRefFinite)
  have hf : ∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (f i) V0 :=
    fun i => ⟨O i,hO i,hSO i,hGcoords i⟩
  have hr : ∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (ref i) V0 :=
    fun i => ⟨O i,hO i,hSO i,h0Reg i⟩
  have hug : ∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (u i) V0 := by
    intro i
    obtain ⟨V0,hV0,hSV0,hVO,hreg⟩ := hUm.1 i
    exact ⟨V0,hV0,hSV0,hreg⟩
  have hdg : ∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (defect i) V0 := by
    intro i
    obtain ⟨V0,hV0,hSV0,hVO,hmap,hreg⟩ := hout.1 i
    exact ⟨V0,hV0,hSV0,hreg⟩
  have heqT : (fun i x => defect i x+ref i x) = incrementsOriginalTensorCoordinates A B.chart Hnext := by
    funext i x k
    change (incrementsOriginalTensorCoordinates A B.chart Hnext i x k-
      incrementsOriginalTensorCoordinates A B.chart h0 i x k)+
      incrementsOriginalTensorCoordinates A B.chart h0 i x k =
      incrementsOriginalTensorCoordinates A B.chart Hnext i x k
    exact sub_add_cancel _ _
  have hMap := actual_paper_weighted_add_germs 2 j htau f u O S hO hSO hf hug hFsmall hUm.2.1
  have hTensor := actual_paper_weighted_add_germs 0 j htau defect ref O S hO hSO hdg hr hout.2.1 hRefSmall
  rw [heqT] at hTensor
  refine ⟨?_,ENNReal.add_ne_top.mpr ⟨hMap.1,hTensor.1⟩,?_⟩
  · intro i
    obtain ⟨V0,hV0,hSV0,hVO,hmap,hreg⟩ := hout.1 i
    refine ⟨V0,hV0,hSV0,hVO,hmap,?_⟩
    have hh : ContDiffOn ℝ ∞ (fun x => defect i x+ref i x) V0 :=
      hreg.add ((h0Reg i).mono hVO)
    exact hh.congr (fun x hx => (congrFun (congrFun heqT i) x).symm)
  · intro k s hk hs hqscale hellscale hdscale htauscale hrescale inherited
    let theta := t^(1/5 : ℝ)
    let CE := 2*Cd j*(1+budget)
    have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
    have hCE : 0 ≤ CE := mul_nonneg (mul_nonneg (by norm_num) (hCd j)) (by linarith)
    have hDefectBound := (hout.2.2 k s hk hs hqscale hellscale hdscale htauscale hrescale).1
    have hpair := actual_repair_pair_norm_from_components j (epsilon*ell) t delta theta (Cu j) CE inherited
      htau ht (htaul.trans helt) ht1 f u ref defect O S hO hSO hf hug hr hdg
      hFfinite hRefFinite hUm.2.1 hout.2.1 (ENNReal.toReal_mono hfull hFle) hUm.2.2 hDefectBound
    rw [heqT] at hpair
    have habs' := actual_repair_pair_component_absorption_at_scales
      (tau := epsilon*ell) (delta := delta) ht ht1 (hCu j) hCE
      (show 0 ≤ inherited from ENNReal.toReal_nonneg)
      (show 0 ≤ (paperAtlasCj j ref O S).toReal from ENNReal.toReal_nonneg) j k hk hdscale htauscale
    have hcoefficient : 1+j*(paperAtlasCj j ref O S).toReal+Cu j+CE ≤
        1+j*(paperAtlasCj j ref O S).toReal+2*C j*(1+budget) :=
      actual_repair_pair_cost_increase (Cd j) (Cu j) budget (paperAtlasCj j ref O S).toReal j (hCu j) hbudget0
    have htheta : 0 ≤ theta := Real.rpow_nonneg ht.le _
    have hcost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefficient htheta)
      (show 0 ≤ 1+inherited by positivity)
    have hcorrection := habs'.trans hcost
    have hfinal := hpair.2
    change nextPair.toReal ≤ _ at hfinal
    exact actual_repair_pair_finish hfinal hcorrection

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_uniform_restricted_pair_repair_step
