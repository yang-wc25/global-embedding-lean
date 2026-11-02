import GlobalEmbedding.Paper.CollarLocalAnalyticComplexification
import GlobalEmbedding.Paper.CollarComplexExtensionOverlap

/-!
# Actual period-invariant complex analytic extension of real analytic data

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Periodicity must hold on an actual invariant complex open domain.
-/

open Set Filter
open scoped Topology NNReal ENNReal

namespace GlobalEmbedding.Paper

/-- Real analytic data with actual real periods have an actual complex analytic extension on
an invariant complex open domain, with genuine complex-domain periodicity.

Source: Proposition `prop:collar`, proof lines 530–534. Construct the local extensions at the
specified real analytic locus, then take all translates of their actual balls and functions by
the given real period group. Every translated local function still agrees with the original
real data. The real-center overlap theorem proves compatibility everywhere on complex overlaps.
Explicit gluing constructs an actual complex analytic function on the open union. Translating
the index gives invariance of the union and exact periodicity of the glued function.
No complex extension, overlap compatibility or complex periodicity is an input. -/
theorem collar_periodic_analytic_complexification
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    {Γ : Type*} [AddCommGroup Γ] {m : ℕ}
    (L : Γ →+ (Fin m → ℝ)) (f : (Fin m → ℝ) → F) (S : Set (Fin m → ℝ))
    (hf : AnalyticOnNhd ℝ f S) (hperiod : ∀ y t, f (y + L t) = f y) :
    ∃ U : Set (Fin m → ℂ), IsOpen U ∧
      (∀ x ∈ S, (fun j ↦ (x j : ℂ)) ∈ U) ∧
      (∀ z t, z + (fun j ↦ (L t j : ℂ)) ∈ U ↔ z ∈ U) ∧
      ∃ g : (Fin m → ℂ) → F, AnalyticOnNhd ℂ g U ∧
        (∀ x : Fin m → ℝ, (fun j ↦ (x j : ℂ)) ∈ U → g (fun j ↦ (x j : ℂ)) = f x) ∧
        (∀ z ∈ U, ∀ t, g (z + (fun j ↦ (L t j : ℂ))) = g z) := by
  classical
  let ι (x : Fin m → ℝ) : Fin m → ℂ := fun j ↦ (x j : ℂ)
  have hiadd (x y : Fin m → ℝ) : ι (x + y) = ι x + ι y := by ext j; simp [ι]
  have hisub (x y : Fin m → ℝ) : ι (x - y) = ι x - ι y := by ext j; simp [ι]
  have hidist (x y : Fin m → ℝ) : dist (ι x) (ι y) = dist x y :=
    (Isometry.piMap (fun _ : Fin m ↦ ((↑) : ℝ → ℂ))
      (fun _ ↦ Complex.isometry_ofReal)).dist_eq x y
  let shift (t : Γ) := ι (L t)
  have hadd (s t : Γ) : shift (s + t) = shift s + shift t := by
    simp only [shift, map_add, hiadd]
  have hneg (t : Γ) : shift (-t) = -shift t := by ext j; simp [shift, ι]
  have hlocal (x : S) : ∃ ρ : ℝ≥0, 0 < ρ ∧ ∃ g : (Fin m → ℂ) → F,
      AnalyticOnNhd ℂ g (Metric.ball (ι x.val) (ρ : ℝ)) ∧
      (∀ y : Fin m → ℝ, ι y ∈ Metric.ball (ι x.val) (ρ : ℝ) → g (ι y) = f y) := by
    obtain ⟨ρ, hρ, g, hg, hreal⟩ := collar_local_analytic_complexification f x.val (hf _ x.property)
    refine ⟨ρ, hρ, g, by simpa only [Metric.eball_coe] using hg, ?_⟩
    intro y hy
    exact hreal y (by simpa only [Metric.mem_ball, hidist, dist_eq_norm] using hy)
  choose ρ hρ G hG hreal using hlocal
  let center (i : S × Γ) : Fin m → ℝ := i.1.val + L i.2
  let B (i : S × Γ) := Metric.ball (ι (center i)) (ρ i.1 : ℝ)
  let H (i : S × Γ) (z : Fin m → ℂ) := G i.1 (z - shift i.2)
  have hmem (i : S × Γ) (z : Fin m → ℂ) :
      z ∈ B i ↔ z - shift i.2 ∈ Metric.ball (ι i.1.val) (ρ i.1 : ℝ) := by
    simp only [B, center, hiadd, Metric.mem_ball, dist_eq_norm]
    have he : z - (ι i.1.val + ι (L i.2)) = z - shift i.2 - ι i.1.val := by
      change z - (ι i.1.val + shift i.2) = _
      abel
    rw [he]
  have hH (i : S × Γ) : AnalyticOnNhd ℂ (H i) (B i) := by
    intro z hz
    have ht : AnalyticAt ℂ (fun w : Fin m → ℂ ↦ w - shift i.2) z :=
      analyticAt_id.sub analyticAt_const
    exact (hG i.1 _ ((hmem i z).mp hz)).comp
      (f := fun w : Fin m → ℂ ↦ w - shift i.2) (x := z) ht
  have hHreal (i : S × Γ) (y : Fin m → ℝ) (hy : ι y ∈ B i) : H i (ι y) = f y := by
    have hy' : ι (y - L i.2) ∈ Metric.ball (ι i.1.val) (ρ i.1 : ℝ) := by
      rw [hisub]
      exact (hmem i (ι y)).mp hy
    change G i.1 (ι y - shift i.2) = f y
    rw [← hisub, hreal i.1 (y - L i.2) hy']
    simpa only [sub_add_cancel] using (hperiod (y - L i.2) i.2).symm
  have hcompat (i j : S × Γ) : EqOn (H i) (H j) (B i ∩ B j) :=
    collar_complex_extension_overlap f (H i) (H j) (center i) (center j)
      (ρ i.1 : ℝ) (ρ j.1 : ℝ) (hH i) (hH j) (hHreal i) (hHreal j)
  let U := ⋃ i : S × Γ, B i
  let idx (z : Fin m → ℂ) (hz : z ∈ U) := Classical.choose (mem_iUnion.mp hz)
  have hidx (z : Fin m → ℂ) (hz : z ∈ U) : z ∈ B (idx z hz) :=
    Classical.choose_spec (mem_iUnion.mp hz)
  let g (z : Fin m → ℂ) := if hz : z ∈ U then H (idx z hz) z else 0
  have hball (i : S × Γ) (z : Fin m → ℂ) (hz : z ∈ B i) : g z = H i z := by
    have hzU : z ∈ U := mem_iUnion.mpr ⟨i, hz⟩
    simp only [g, dite_eq_left hzU]
    exact hcompat (idx z hzU) i ⟨hidx z hzU, hz⟩
  have hshiftmem (i : S × Γ) (z : Fin m → ℂ) (t : Γ) :
      z + shift t ∈ B (i.1, i.2 + t) ↔ z ∈ B i := by
    rw [hmem, hmem]
    simp only [hadd]
    have he : z + shift t - (shift i.2 + shift t) = z - shift i.2 := by abel
    rw [he]
  have hforward (z : Fin m → ℂ) (hz : z ∈ U) (t : Γ) : z + shift t ∈ U := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨(i.1, i.2 + t), (hshiftmem i z t).mpr hi⟩
  refine ⟨U, isOpen_iUnion (fun _ ↦ Metric.isOpen_ball), ?_, ?_, g, ?_, ?_, ?_⟩
  · intro x hx
    refine mem_iUnion.mpr ⟨(⟨x, hx⟩, 0), ?_⟩
    change ι x ∈ Metric.ball (ι (x + L 0)) (ρ ⟨x, hx⟩ : ℝ)
    simp only [map_zero, add_zero]
    exact Metric.mem_ball_self (by exact_mod_cast hρ ⟨x, hx⟩)
  · intro z t
    constructor
    · intro hz
      have he := hforward (z + shift t) hz (-t)
      simpa only [hneg, add_neg_cancel_right] using he
    · exact fun hz ↦ hforward z hz t
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have he : g =ᶠ[𝓝 z] H i := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hi] with w hw
      exact hball i w hw
    exact (analyticAt_congr he).mpr (hH i z hi)
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (hball i _ hi).trans (hHreal i x hi)
  · intro z hz t
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    rw [hball (i.1, i.2 + t) _ ((hshiftmem i z t).mpr hi), hball i z hi]
    change G i.1 (z + shift t - shift (i.2 + t)) = G i.1 (z - shift i.2)
    rw [hadd]
    congr 1
    abel

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_periodic_analytic_complexification
