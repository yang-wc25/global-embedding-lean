import NormalPolar.ParameterDisplacementCenter
import GlobalEmbedding.Offline.RepairDisplacementBudget

/-!
# The actual contracted reference, full first increment and repair center

The source starts at G0 = sqrt(1-delta^2) F0, then sets G1 = G0 + U0.
The entire actual U0, including its background contribution at u=0, is kept.
The center bound is proved from the original C1 budgets of U0 and the literal
correction Fstar-G1. There is no hypothesis giving the final center bound and
no assumption that G1 at zero equals F0.

The frozen scalar contraction lemma is valid for every real delta. All
scale-to-rate conversions use the given threshold, so no smaller threshold
or additional t ≤ 1 condition is introduced.
-/

noncomputable section
open Manifold Set GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The real reference contraction in the original atlas norm, obtained
from the frozen original-coordinate scaling theorem. -/
theorem actual_probe_initial_scaling_Cj_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (j : ℕ) (delta : ℝ) {Cref : ℝ} (hCref : 0 ≤ Cref)
    (href : probeAtlasCj A j F₀ ≤ ENNReal.ofReal Cref) :
    probeAtlasCj A j ((fun x ↦ Real.sqrt (1 - delta ^ 2) • F₀ x) - F₀) ≤
      ENNReal.ofReal (delta ^ 2 * Cref) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  unfold probeAtlasCj paperAtlasCj
  apply iSup_le
  intro i
  let O := e '' (A.chart i).target
  let S := e '' ((A.chart i) '' A.support i)
  let f := fun y ↦ v (F₀ ((A.chart i).symm (e.symm y)))
  have hO : IsOpen O := e.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSO : S ⊆ O := by
    rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨A.chart i x, (A.chart i).map_source (hA.support_subset i hx), rfl⟩
  have hf : ContDiffOn ℝ ∞ f O := probeAtlas_coordinate_smooth A hA F₀ hF₀ i
  have hlocal : paperCoordinateCj j f O S ≤ ENNReal.ofReal Cref :=
    (le_iSup (fun k ↦ paperCoordinateCj j
      (fun y ↦ v (F₀ ((A.chart k).symm (e.symm y))))
      (e '' (A.chart k).target) (e '' ((A.chart k) '' A.support k))) i).trans href
  have h := initial_scaling_paperCoordinateCj_le j hO hSO f hf delta hCref hlocal
  simpa only [f, O, S, e, v, Pi.sub_apply, map_sub, map_smul] using h

/-- The paper's actual first map, with the entire supplied first increment.
This is a function definition, not an identity required of the final map. -/
def actualProbeFirstMap {r : ℕ} (F₀ : M → V)
    (U₀ : ℝ → ProbeParameters r → M → V) (t : ℝ) (u : ProbeParameters r) (x : M) : V :=
  Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F₀ x + U₀ t u x

/-- The final actual center pays all three terms: reference contraction,
the full first increment, and the actual correction from that first map.
The bounds all use the same original atlas norm and genuine maps. -/
theorem actual_probe_center_C1_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (U₀ Fstar : ℝ → ProbeParameters r → M → V)
    (t : ℝ) (ht : 0 < t)
    (hU : ContMDiff IM 𝓘(ℝ, V) ∞ (U₀ t 0))
    (hFstar : ContMDiff IM 𝓘(ℝ, V) ∞ (Fstar t 0))
    (Cref Cinc Ctail : ℝ) (hCref : 0 ≤ Cref) (hCinc : 0 ≤ Cinc) (hCtail : 0 ≤ Ctail)
    (href : probeAtlasCj A 1 F₀ ≤ ENNReal.ofReal Cref)
    (hinc : probeAtlasCj A 1 (U₀ t 0) ≤ ENNReal.ofReal (Cinc * t ^ (10 : ℕ)))
    (htail : probeAtlasCj A 1 (Fstar t 0 - actualProbeFirstMap F₀ U₀ t 0) ≤
      ENNReal.ofReal (Ctail * t ^ (12 : ℕ))) :
    probeAtlasCj A 1 (Fstar t 0 - F₀) ≤
      ENNReal.ofReal (Cref * t ^ (20 : ℕ) + Cinc * t ^ (10 : ℕ) +
        Ctail * t ^ (12 : ℕ)) := by
  let G₀ : M → V := fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F₀ x
  let G₁ : M → V := actualProbeFirstMap F₀ U₀ t 0
  have hc : ContMDiff IM 𝓘(ℝ, ℝ) ∞
      (fun _ : M ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2)) := contMDiff_const
  have hG₀ : ContMDiff IM 𝓘(ℝ, V) ∞ G₀ := hc.smul hF₀
  have hG₁ : ContMDiff IM 𝓘(ℝ, V) ∞ G₁ := hG₀.add hU
  have hg₀ : probeAtlasCj A 1 (G₀ - F₀) ≤ ENNReal.ofReal (Cref * t ^ (20 : ℕ)) := by
    have h := actual_probe_initial_scaling_Cj_bound A hA F₀ hF₀ 1 (t ^ (10 : ℕ)) hCref href
    have hpow : (t ^ (10 : ℕ)) ^ 2 * Cref = Cref * t ^ (20 : ℕ) := by ring
    simpa only [hpow] using h
  have heq : G₁ - G₀ = U₀ t 0 := by
    funext x
    simp only [G₁, G₀, actualProbeFirstMap, Pi.sub_apply]
    abel
  have hg₁ : probeAtlasCj A 1 (G₁ - F₀) ≤
      ENNReal.ofReal (Cref * t ^ (20 : ℕ) + Cinc * t ^ (10 : ℕ)) := by
    apply probeAtlasCj_three_point_bound A hA 1 F₀ G₀ G₁ hF₀ hG₀ hG₁
      (mul_nonneg hCref (pow_nonneg ht.le _)) (mul_nonneg hCinc (pow_nonneg ht.le _)) hg₀
    simpa only [heq] using hinc
  exact probeAtlasCj_three_point_bound A hA 1 F₀ G₁ (Fstar t 0) hF₀ hG₁ hFstar
    (add_nonneg (mul_nonneg hCref (pow_nonneg ht.le _)) (mul_nonneg hCinc (pow_nonneg ht.le _)))
    (mul_nonneg hCtail (pow_nonneg ht.le _)) hg₁ htail

/-- Fixed-threshold absorption of the actual three-term center budget.
The reference term is order twenty and the repair tail order twelve. -/
theorem actual_probe_center_C1_ten_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (U₀ Fstar : ℝ → ProbeParameters r → M → V)
    (threshold Cref Cinc Ctail : ℝ) (hCref : 0 ≤ Cref) (hCinc : 0 ≤ Cinc) (hCtail : 0 ≤ Ctail)
    (href : probeAtlasCj A 1 F₀ ≤ ENNReal.ofReal Cref)
    (hU : ∀ t, 0 < t → t < threshold → ContMDiff IM 𝓘(ℝ, V) ∞ (U₀ t 0))
    (hFstar : ∀ t, 0 < t → t < threshold → ContMDiff IM 𝓘(ℝ, V) ∞ (Fstar t 0))
    (hinc : ∀ t, 0 < t → t < threshold →
      probeAtlasCj A 1 (U₀ t 0) ≤ ENNReal.ofReal (Cinc * t ^ (10 : ℕ)))
    (htail : ∀ t, 0 < t → t < threshold →
      probeAtlasCj A 1 (Fstar t 0 - actualProbeFirstMap F₀ U₀ t 0) ≤
        ENNReal.ofReal (Ctail * t ^ (12 : ℕ))) :
    ∀ t, 0 < t → t < threshold →
      probeAtlasCj A 1 (Fstar t 0 - F₀) ≤ ENNReal.ofReal
        ((Cref * (max 1 threshold) ^ (10 : ℕ) + Cinc + Ctail * (max 1 threshold) ^ (2 : ℕ)) *
          t ^ (10 : ℕ)) := by
  intro t ht htt
  have h := actual_probe_center_C1_bound A hA F₀ hF₀ U₀ Fstar t ht
    (hU t ht htt) (hFstar t ht htt) Cref Cinc Ctail hCref hCinc hCtail
    href (hinc t ht htt) (htail t ht htt)
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  have htmax : t ≤ max 1 threshold := htt.le.trans (le_max_right _ _)
  have h20 : t ^ (20 : ℕ) ≤ (max 1 threshold) ^ (10 : ℕ) * t ^ (10 : ℕ) := by
    calc
      t ^ (20 : ℕ) = t ^ (10 : ℕ) * t ^ (10 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le htmax 10)
        (pow_nonneg ht.le _)
  have h12 := pow_twelve_le_threshold_sq_mul_pow_ten threshold t ht htt
  calc
    _ ≤ Cref * ((max 1 threshold) ^ (10 : ℕ) * t ^ (10 : ℕ)) + Cinc * t ^ (10 : ℕ) +
        Ctail * ((max 1 threshold) ^ (2 : ℕ) * t ^ (10 : ℕ)) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left h20 hCref) le_rfl)
        (mul_le_mul_of_nonneg_left h12 hCtail)
    _ = _ := by ring

end GlobalEmbedding.NormalPolar
