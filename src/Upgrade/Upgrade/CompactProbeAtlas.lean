import Upgrade.ProbeInterface
import Upgrade.CompactAtlasBudget
import Upgrade.ProtectionMargins

/-!
# Original atlas budgets control actual global displacements

The raw `BufferedAtlas.support` sets are independent data.  Their actual cover
is therefore retained explicitly, rather than silently deduced from the inner
cover.  No differentiability is needed for the order-zero part of the original
norm.  This supplies the genuine two-endpoint protection from a C² budget.
-/

noncomputable section
open Bundle Manifold Set GlobalEmbedding.Paper
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual original atlas norm bounds the global ambient displacement,
with the explicit Euclidean/sup-coordinate target conversion factor.  The
statement includes zero-dimensional targets and empty sources. -/
theorem norm_le_of_probeAtlasCj
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x : M, ∃ i, x ∈ A.support i)
    (j : ℕ) (f : M → V) {d : ℝ} (hd : 0 ≤ d)
    (hbound : probeAtlasCj A j f ≤ ENNReal.ofReal d) (x : M) :
    ‖f x‖ ≤ ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ * d := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  obtain ⟨i, hxi⟩ := hcover x
  have hxchart : x ∈ (A.chart i).source := hA.support_subset i hxi
  let z : e '' ((A.chart i) '' A.support i) := ⟨e (A.chart i x),
    ⟨A.chart i x, ⟨x, hxi, rfl⟩, rfl⟩⟩
  have hcomponent (c : Fin N) : ‖v (f x) c‖ ≤ d := by
    have hz : ENNReal.ofReal ‖v (f x) c‖ ≤ probeAtlasCj A j f := by
      unfold probeAtlasCj paperAtlasCj paperCoordinateCj
      apply le_iSup_of_le i
      apply le_iSup_of_le ⟨[], by simp⟩
      apply le_iSup_of_le z
      apply le_iSup_of_le c
      simp only [paperCoordinatePartial, z, e, v, ContinuousLinearEquiv.symm_apply_apply,
        (A.chart i).left_inv hxchart, le_refl]
    exact (ENNReal.ofReal_le_ofReal_iff hd).mp (hz.trans hbound)
  have hcoord : ‖v (f x)‖ ≤ d := (pi_norm_le_iff_of_nonneg hd).mpr hcomponent
  calc
    ‖f x‖ = ‖v.symm (v (f x))‖ := by rw [v.symm_apply_apply]
    _ ≤ ‖v.symm.toContinuousLinearMap‖ * ‖v (f x)‖ :=
      v.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖v.symm.toContinuousLinearMap‖ * d :=
      mul_le_mul_of_nonneg_left hcoord (norm_nonneg _)

/-- One original C² tolerance preserves a previously established actual pair
gap on the closures of the protected neighborhoods.  The global bound is
applied at both endpoints; the corrected map is never assumed supported. -/
theorem exists_probeAtlasC2_protected_gap_budget
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x : M, ∃ i, x ∈ A.support i)
    {F : M → V} {P : Set (M × M)} {O : Set M} {d : ℝ} (hd : 0 < d)
    (hgap : ∀ z ∈ P, z.1 ∈ closure O ∨ z.2 ∈ closure O → d < ‖F z.1 - F z.2‖) :
    ∃ e > 0, ∀ G : M → V,
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal e →
      ∀ z ∈ P, z.1 ∈ closure O ∨ z.2 ∈ closure O →
        d / 2 ≤ ‖G z.1 - G z.2‖ := by
  let C := ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  let e := d / (4 * (1 + C))
  have he : 0 < e := div_pos hd (by positivity)
  have hCe : C * e ≤ d / 4 := by
    have hCe0 : (1 + C) * e = d / 4 := by dsimp [e]; field_simp
    exact (mul_le_mul_of_nonneg_right (by linarith : C ≤ 1 + C) he.le).trans_eq hCe0
  refine ⟨e, he, ?_⟩
  intro G hbudget
  apply protected_pair_gap_after_perturbation F G hgap
  intro x
  exact (norm_le_of_probeAtlasCj A hA hcover 2 (G - F) he.le hbudget x).trans hCe

/-- The literal coordinate representative in `probeAtlasCj` is smooth on its
original open differentiation domain.  This follows from maximal-atlas
membership of the actual buffered chart, without changing its support set. -/
theorem probeAtlas_coordinate_smooth
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (i : Fin A.count) :
    ContDiffOn ℝ ∞
      (fun x ↦ (EuclideanSpace.equiv (Fin N) ℝ)
        (F ((A.chart i).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x))))
      ((EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  have hc := contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i)
  have hr : ContDiffOn ℝ ∞ (F ∘ (A.chart i).symm) (A.chart i).target :=
    (hF.comp_contMDiffOn hc).contDiffOn
  apply v.contDiff.comp_contDiffOn
  apply hr.comp e.symm.contDiff.contDiffOn
  rintro x ⟨y, hy, rfl⟩
  change e.symm (e y) ∈ (A.chart i).target
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy

/-- Every prefix of finitely many actual global perturbations satisfies the
sum of its original `probeAtlasCj` budgets on the same fixed buffered atlas.
The actual maps are telescoped, so there is no chart-count multiplier. -/
theorem finite_probeAtlas_prefix_budget
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (j m : ℕ) (F : ℕ → M → V)
    (hF : ∀ k ≤ m, ContMDiff IM 𝓘(ℝ, V) ∞ (F k))
    (b : ℕ → ℝ) (hb : ∀ k < m, 0 ≤ b k)
    (hstep : ∀ k < m,
      probeAtlasCj A j (F (k + 1) - F k) ≤ ENNReal.ofReal (b k)) :
    ∀ k ≤ m, probeAtlasCj A j (F k - F 0) ≤
      ENNReal.ofReal (∑ l ∈ Finset.range k, b l) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  let chart := fun i x ↦ (A.chart i).symm (e.symm x)
  let O := fun i ↦ e '' (A.chart i).target
  let S := fun i ↦ e '' ((A.chart i) '' A.support i)
  let coord := fun k x ↦ v (F k x)
  have hO (i : Fin A.count) : IsOpen (O i) :=
    e.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSO (i : Fin A.count) : S i ⊆ O i := by
    rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨A.chart i z, (A.chart i).map_source (hA.support_subset i hz), rfl⟩
  have hcoord (k : ℕ) (hk : k ≤ m) (i : Fin A.count) :
      ContDiffOn ℝ ∞ (coord k ∘ chart i) (O i) :=
    probeAtlas_coordinate_smooth A hA (F k) (hF k hk) i
  have hstep' (k : ℕ) (hk : k < m) :
      paperAtlasCj j (fun i ↦ (coord (k + 1) ∘ chart i) - (coord k ∘ chart i)) O S ≤
        ENNReal.ofReal (b k) := by
    simpa only [probeAtlasCj, coord, chart, O, S, e, v,
      Function.comp_def, Pi.sub_def, Pi.sub_apply, map_sub] using hstep k hk
  have htotal := finite_global_perturbations_paperAtlas_budget j m coord chart O S
    hO hSO hcoord b hb hstep'
  intro k hk
  simpa only [probeAtlasCj, coord, chart, O, S, e, v,
    Function.comp_def, Pi.sub_def, Pi.sub_apply, map_sub] using htotal k hk

/-- All intermediate maps remain within one strict original C² budget,
including the last map; the real projection is used only after finiteness. -/
theorem finite_probeAtlas_C2_prefix_lt
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (m : ℕ) (F : ℕ → M → V)
    (hF : ∀ k ≤ m, ContMDiff IM 𝓘(ℝ, V) ∞ (F k))
    (b : ℕ → ℝ) (hb : ∀ k < m, 0 ≤ b k)
    (hstep : ∀ k < m,
      probeAtlasCj A 2 (F (k + 1) - F k) ≤ ENNReal.ofReal (b k))
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsum : ∑ l ∈ Finset.range m, b l < epsilon) :
    ∀ k ≤ m,
      probeAtlasCj A 2 (F k - F 0) ≠ ⊤ ∧
        (probeAtlasCj A 2 (F k - F 0)).toReal < epsilon := by
  intro k hk
  have hbound := finite_probeAtlas_prefix_budget A hA 2 m F hF b hb hstep k hk
  have hsumle : ∑ l ∈ Finset.range k, b l ≤ ∑ l ∈ Finset.range m, b l :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      (fun l hl _ ↦ hb l (Finset.mem_range.mp hl))
  have hstrict := hbound.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hepsilon).mpr (hsumle.trans_lt hsum))
  have hfinite := ne_of_lt (hstrict.trans ENNReal.ofReal_lt_top)
  refine ⟨hfinite, ?_⟩
  exact (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hstrict |>.trans_eq
    (ENNReal.toReal_ofReal hepsilon.le)

/-- Exact metrics of successive actual maps telescope to the original metric.
This is finite upgrade bookkeeping, independent of increments or repair. -/
theorem finite_exactMetric_chain
    (m : ℕ) (F : ℕ → M → V)
    (hstep : ∀ k < m, ∀ x,
      inducedMetric (I := IM) (F (k + 1)) x = inducedMetric (I := IM) (F k) x) :
    ∀ k ≤ m, ∀ x, inducedMetric (I := IM) (F k) x = inducedMetric (I := IM) (F 0) x := by
  intro k hk
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    exact (hstep k (by omega) x).trans (ih (by omega) x)

end GlobalEmbedding.Upgrade
