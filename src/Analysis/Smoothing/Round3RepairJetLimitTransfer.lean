import Probes.ActualJointChartTransfer
import Smoothing.Round3RepairClosedSeries

/-! Actual coordinate derivative limits survive fixed smooth chart changes.
The pointwise finite-jet bound proves the transfer, without adding a new
uniform atlas cost to the final original MAX norm estimate. -/
noncomputable section
open GlobalEmbedding.Offline Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A fixed genuine coordinate transition transports the actual derivative
limit. Only finitely many lower derivatives are used at each order. -/
theorem round3_repair_jet_limit_comp
    (f : ℕ → Y → Z) (g : Y → Z) (phi : X → Y) (V : Set Y) (hV : IsOpen V)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) V) (hg : ContDiffOn ℝ ∞ g V)
    (x : X) (hphi : ContDiffAt ℝ ∞ phi x) (hx : phi x ∈ V)
    (a : ℕ)
    (hlim : ∀ r ≤ a, Tendsto (fun j => iteratedFDeriv ℝ r (f j) (phi x)) atTop
      (𝓝 (iteratedFDeriv ℝ r g (phi x)))) :
    Tendsto (fun j => iteratedFDeriv ℝ a (f j ∘ phi) x) atTop
      (𝓝 (iteratedFDeriv ℝ a (g ∘ phi) x)) := by
  obtain ⟨U,hU,hphiU⟩ := hphi.contDiffOn (m := (a : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨O,hOsub,hO,hxO⟩ := mem_nhds_iff.mp
    (inter_mem hU (hphi.continuousAt.preimage_mem_nhds (hV.mem_nhds hx)))
  have hphiO : ContDiffOn ℝ a phi O := hphiU.mono (fun _ hy => (hOsub hy).1)
  have hMap : MapsTo phi O V := fun _ hy => (hOsub hy).2
  let D : ℝ := 1+∑ r ∈ Finset.range (a+1), ‖iteratedFDeriv ℝ r phi x‖
  have hD1 : 1 ≤ D := by
    dsimp only [D]
    linarith [Finset.sum_nonneg (s := Finset.range (a+1)) (fun r _ => norm_nonneg (iteratedFDeriv ℝ r phi x))]
  let C : ℕ → ℝ := fun j => ∑ r ∈ Finset.range (a+1),
    ‖iteratedFDeriv ℝ r (f j) (phi x)-iteratedFDeriv ℝ r g (phi x)‖
  have hC : Tendsto C atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.range (a+1)) (fun r hr =>
      tendsto_iff_norm_sub_tendsto_zero.mp (hlim r (by simpa using hr)))
    simpa only [Finset.sum_const_zero] using h
  have hBound (j : ℕ) :
      ‖iteratedFDeriv ℝ a (f j ∘ phi) x-iteratedFDeriv ℝ a (g ∘ phi) x‖ ≤ (a.factorial : ℝ)*C j*D^a := by
    have hDiff : ContDiffOn ℝ a (f j-g) V := ((hf j).sub hg).of_le (by simp)
    have hc (r : ℕ) (hr : r ≤ a) : ‖iteratedFDerivWithin ℝ r (f j-g) V (phi x)‖ ≤ C j := by
      rw [iteratedFDerivWithin_of_isOpen r hV hx,
        iteratedFDeriv_sub_apply (((hf j).contDiffAt (hV.mem_nhds hx)).of_le (by simp))
          ((hg.contDiffAt (hV.mem_nhds hx)).of_le (by simp))]
      change _ ≤ ∑ s ∈ Finset.range (a+1),
        ‖iteratedFDeriv ℝ s (f j) (phi x)-iteratedFDeriv ℝ s g (phi x)‖
      exact Finset.single_le_sum (fun s _ => norm_nonneg (iteratedFDeriv ℝ s (f j) (phi x)-iteratedFDeriv ℝ s g (phi x)))
        (show r ∈ Finset.range (a+1) by simpa using hr)
    have hd (r : ℕ) (hr : 1 ≤ r) (hra : r ≤ a) :
        ‖iteratedFDerivWithin ℝ r phi O x‖ ≤ D^r := by
      rw [iteratedFDerivWithin_of_isOpen r hO hxO]
      have hSum : ‖iteratedFDeriv ℝ r phi x‖ ≤
          ∑ s ∈ Finset.range (a+1), ‖iteratedFDeriv ℝ s phi x‖ :=
        Finset.single_le_sum (fun s _ => norm_nonneg (iteratedFDeriv ℝ s phi x))
          (show r ∈ Finset.range (a+1) by simpa using hra)
      apply le_trans (b := D) (by dsimp only [D]; linarith)
      exact le_self_pow₀ hD1 (by omega)
    have h := norm_iteratedFDerivWithin_comp_le hDiff hphiO (n := a) le_rfl
      hV.uniqueDiffOn hO.uniqueDiffOn hMap hxO hc hd
    rw [iteratedFDerivWithin_of_isOpen a hO hxO] at h
    have heq : (f j-g) ∘ phi = (f j ∘ phi)-(g ∘ phi) := rfl
    rw [heq,iteratedFDeriv_sub_apply
      (((((hf j).of_le (by simp : (a : ℕ∞ω) ≤ ∞)).comp hphiO hMap).contDiffAt (hO.mem_nhds hxO)).of_le le_rfl)
      ((((hg.of_le (by simp : (a : ℕ∞ω) ≤ ∞)).comp hphiO hMap).contDiffAt (hO.mem_nhds hxO)).of_le le_rfl)] at h
    exact h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hUpper : Tendsto (fun j => (a.factorial : ℝ)*C j*D^a) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hC).mul_const (D^a)
  exact squeeze_zero (fun _ => norm_nonneg _) hBound hUpper

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_jet_limit_comp
