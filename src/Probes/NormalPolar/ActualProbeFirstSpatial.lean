import NormalPolar.ParameterDisplacementReference
import NormalPolar.ActualRepairBudgetTransfer
import NormalPolar.OriginalProbeScales

/-!
# The actual contracted reference plus the complete first increment

The two first-model spatial fields follow from the actual U0 budgets.
The reference constants are produced by compactness, and both constants are
selected before the scale and parameter.  The whole given threshold is
retained; the estimates do not quietly assume t <= 1.
-/

noncomputable section
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

/-- Constant scaling in the original atlas norm, with its actual coordinate
domains and actual support samples. -/
theorem actual_probe_const_smul_Cj_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (j : ℕ) (c : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : probeAtlasCj A j F ≤ ENNReal.ofReal C) :
    probeAtlasCj A j (fun x => c • F x) ≤ ENNReal.ofReal (|c| * C) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  apply iSup_le
  intro i
  let O := e '' (A.chart i).target
  let S := e '' ((A.chart i) '' A.support i)
  let f := fun y => v (F ((A.chart i).symm (e.symm y)))
  have hO : IsOpen O := e.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSO : S ⊆ O := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨A.chart i y,(A.chart i).map_source (hA.support_subset i hy),rfl⟩
  have hlocal : paperCoordinateCj j f O S ≤ ENNReal.ofReal C :=
    (le_iSup (fun k => paperCoordinateCj j
      (fun y => v (F ((A.chart k).symm (e.symm y))))
      (e '' (A.chart k).target) (e '' ((A.chart k) '' A.support k))) i).trans hbound
  simpa only [f,O,S,e,v,map_smul] using paperCoordinateCj_smul_le j hO hSO f
    (probeAtlas_coordinate_smooth A hA F hF i) c hC hlocal

/-- The actual reference contraction costs at most the true reference Cj
budget, also when the total square-root expression is evaluated off its
positive branch. -/
theorem actual_probe_contracted_reference_Cj_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (j : ℕ) (delta : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : probeAtlasCj A j F ≤ ENNReal.ofReal C) :
    probeAtlasCj A j (fun x => Real.sqrt (1-delta^2) • F x) ≤ ENNReal.ofReal C := by
  apply (actual_probe_const_smul_Cj_bound A hA F hF j _ hC hbound).trans
  apply ENNReal.ofReal_le_ofReal
  have hs : |Real.sqrt (1-delta^2)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg delta])
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hC

def actualProbeFirstSpatialConstant
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (threshold Cinc2 Cinc3 : ℝ) : ℝ :=
  compactReferenceCjConstant A hA hcompact F₀ hF₀ 2 * (max 1 threshold)^((56 : ℝ)/5) + Cinc2 +
  compactReferenceCjConstant A hA hcompact F₀ hF₀ 3 + Cinc3 * (max 1 threshold)^((38 : ℝ)/5)

theorem actualProbeFirstSpatialConstant_nonneg
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (threshold Cinc2 Cinc3 : ℝ) (h2 : 0 ≤ Cinc2) (h3 : 0 ≤ Cinc3) :
    0 ≤ actualProbeFirstSpatialConstant A hA hcompact F₀ hF₀ threshold Cinc2 Cinc3 := by
  have hr2 := compactReferenceCjConstant_nonneg A hA hcompact F₀ hF₀ 2
  have hr3 := compactReferenceCjConstant_nonneg A hA hcompact F₀ hF₀ 3
  unfold actualProbeFirstSpatialConstant
  positivity

/-- The full first G1 has the original C2 closeness and uniform C3 fields.
The input budgets concern U0 alone; they are supplied by the physical
complete-increment producer, with the actual contraction retained here. -/
theorem actual_probe_first_spatial_budgets
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (U₀ : M → V) (hU₀ : ContMDiff IM 𝓘(ℝ,V) ∞ U₀)
    (threshold Cinc2 Cinc3 t : ℝ) (h2 : 0 ≤ Cinc2) (h3 : 0 ≤ Cinc3)
    (ht : 0 < t) (htt : t < threshold)
    (hinc2 : probeAtlasCj A 2 U₀ ≤ ENNReal.ofReal (Cinc2*t^(10 : ℕ)/t^((6 : ℝ)/5)))
    (hinc3 : probeAtlasCj A 3 U₀ ≤ ENNReal.ofReal (Cinc3*t^(10 : ℕ)/(t^((6 : ℝ)/5))^2)) :
    let G₀ := fun x => Real.sqrt (1-(t^(10 : ℕ))^2) • F₀ x
    let G₁ := G₀+U₀
    let C := actualProbeFirstSpatialConstant A hA hcompact F₀ hF₀ threshold Cinc2 Cinc3
    probeAtlasCj A 2 (G₁-F₀) ≤ ENNReal.ofReal (C*t^((44 : ℝ)/5)) ∧
    probeAtlasCj A 3 G₁ ≤ ENNReal.ofReal C := by
  intro G₀ G₁ C
  let Cref2 := compactReferenceCjConstant A hA hcompact F₀ hF₀ 2
  let Cref3 := compactReferenceCjConstant A hA hcompact F₀ hF₀ 3
  let R := max 1 threshold
  have hr2 : 0 ≤ Cref2 := compactReferenceCjConstant_nonneg A hA hcompact F₀ hF₀ 2
  have hr3 : 0 ≤ Cref3 := compactReferenceCjConstant_nonneg A hA hcompact F₀ hF₀ 3
  have hR : 0 ≤ R := zero_le_one.trans (le_max_left _ _)
  have hc : ContMDiff IM 𝓘(ℝ,ℝ) ∞
      (fun _ : M => Real.sqrt (1-(t^(10 : ℕ))^2)) := contMDiff_const
  have hG₀ : ContMDiff IM 𝓘(ℝ,V) ∞ G₀ := hc.smul hF₀
  have hG₁ : ContMDiff IM 𝓘(ℝ,V) ∞ G₁ := hG₀.add hU₀
  have hdiff : G₁-G₀ = U₀ := by dsimp only [G₁]; abel
  have hi2 : probeAtlasCj A 2 U₀ ≤ ENNReal.ofReal (Cinc2*t^((44 : ℝ)/5)) := by
    simpa only [mul_div_assoc,probe_delta_div_tau_eq_sigma t ht] using hinc2
  have hi3 : probeAtlasCj A 3 U₀ ≤ ENNReal.ofReal (Cinc3*t^((38 : ℝ)/5)) := by
    simpa only [mul_div_assoc,probe_delta_div_tau_sq_eq_C3_scale t ht] using hinc3
  have hb0 : probeAtlasCj A 2 (G₀-F₀) ≤ ENNReal.ofReal (Cref2*t^(20 : ℕ)) := by
    have h := actual_probe_initial_scaling_Cj_bound A hA F₀ hF₀ 2 (t^(10 : ℕ)) hr2
      (compactReferenceCjConstant_bound A hA hcompact F₀ hF₀ 2)
    have he : (t^(10 : ℕ))^2*Cref2 = Cref2*t^(20 : ℕ) := by ring
    simpa only [he] using h
  have hbase := probeAtlasCj_three_point_bound A hA 2 F₀ G₀ G₁ hF₀ hG₀ hG₁
    (by positivity : 0 ≤ Cref2*t^(20 : ℕ)) (by positivity : 0 ≤ Cinc2*t^((44 : ℝ)/5)) hb0
    (by simpa only [hdiff] using hi2)
  have hpow20 : t^(20 : ℕ) ≤ R^((56 : ℝ)/5)*t^((44 : ℝ)/5) := by
    rw [← Real.rpow_natCast t 20]
    exact probe_rpow_le_threshold_envelope threshold t 20 ((44 : ℝ)/5) ((56 : ℝ)/5)
      ht htt (by norm_num) (by norm_num)
  have hpow3 : t^((38 : ℝ)/5) ≤ R^((38 : ℝ)/5) :=
    Real.rpow_le_rpow ht.le (htt.le.trans (le_max_right _ _)) (by norm_num)
  have hsum3 := actual_repair_spatial_budget_of_model_tail A hA 3 G₁ G₀ hG₁ hG₀
    hr3 (by positivity : 0 ≤ Cinc3*t^((38 : ℝ)/5))
    (actual_probe_contracted_reference_Cj_bound A hA F₀ hF₀ 3 (t^(10 : ℕ)) hr3
      (compactReferenceCjConstant_bound A hA hcompact F₀ hF₀ 3))
    (by simpa only [hdiff] using hi3)
  have hclose : Cref2*R^((56 : ℝ)/5)+Cinc2 ≤ C := by
    change _ ≤ Cref2*R^((56 : ℝ)/5)+Cinc2+Cref3+Cinc3*R^((38 : ℝ)/5)
    have hn : 0 ≤ Cinc3*R^((38 : ℝ)/5) := by positivity
    linarith
  have hsmooth : Cref3+Cinc3*R^((38 : ℝ)/5) ≤ C := by
    change _ ≤ Cref2*R^((56 : ℝ)/5)+Cinc2+Cref3+Cinc3*R^((38 : ℝ)/5)
    have hn : 0 ≤ Cref2*R^((56 : ℝ)/5)+Cinc2 := by positivity
    linarith
  constructor
  · apply hbase.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ Cref2*(R^((56 : ℝ)/5)*t^((44 : ℝ)/5))+Cinc2*t^((44 : ℝ)/5) :=
        add_le_add (mul_le_mul_of_nonneg_left hpow20 hr2) le_rfl
      _ = (Cref2*R^((56 : ℝ)/5)+Cinc2)*t^((44 : ℝ)/5) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hclose (Real.rpow_nonneg ht.le _)
  · apply hsum3.trans (ENNReal.ofReal_le_ofReal ?_)
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow3 h3)).trans hsmooth

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actual_probe_first_spatial_budgets
