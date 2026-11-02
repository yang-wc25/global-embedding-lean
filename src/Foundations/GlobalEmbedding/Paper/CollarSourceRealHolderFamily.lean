import GlobalEmbedding.Paper.CollarHolomorphicHolderCoefficients
import GlobalEmbedding.Paper.CollarEuclideanRealForm
import GlobalEmbedding.Paper.CollarComplexHolderClosedRealForm

/-!
# Actual original real little Hölder coefficient families from real source data

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. This constructs the real family and its exact complex-family agreement.
-/

open Set Filter WithLp
open scoped Topology NNReal ENNReal

namespace GlobalEmbedding.Paper

/-- Actual real analytic periodic source data construct both an analytic complex Hölder family
and an actual original real little Hölder family on the canonical real parameter submodule.
Near the actual base parameter, the real family has the exact original translated source lift,
the complex family is its actual pointwise real inclusion, and their original norms agree.

Source: Proposition `prop:collar`, proof lines 530–534. Construct the genuine complex coefficient
norm series from the original real source. Its continuous actual real-part map constructs an
actual original real little family, analytic for the real parameters. At a nearby canonical real
parameter the complex parameter increment is in the norm-series ball and the real base is in
the source agreement neighborhood. Zero imaginary coordinates identify the translated complex
slice with the original real source value. Actual real-part evaluation gives the real family's
exact lift. Its pointwise inclusion is the complex family; the actual original-norm real-form
isometry therefore proves exact norm equality. No real Holder membership or family-matching
data are assumptions, and the parameter submodule is canonical and shared across value dimensions.
-/
theorem collar_source_real_holder_family {b a N : ℕ}
    (f : (Fin (b + a) → ℝ) → (Fin N → ℝ)) (V : Set (Fin b → ℝ))
    (hV : IsOpen V) (p₀ : Fin b → ℝ) (hp₀ : p₀ ∈ V)
    (hf : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      AnalyticAt ℝ f x)
    (hperiod : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        f (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = f x) :
    let p₀R := collarEuclideanRealEquiv (b + a)
      (toLp 2 (Fin.append p₀ (fun _ : Fin a ↦ (0 : ℝ))))
    ∃ (F : EuclideanSpace ℂ (Fin (b + a)) → CollarComplexHolderSpace a N 2 (1 / 2 : ℝ))
      (AR : collarEuclideanRealSubmodule (b + a) →
        LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)),
      AnalyticAt ℂ F (p₀R : EuclideanSpace ℂ (Fin (b + a))) ∧
      AnalyticAt ℝ AR p₀R ∧
      ∀ᶠ p : collarEuclideanRealSubmodule (b + a) in 𝓝 p₀R,
        (∀ y : EuclideanSpace ℝ (Fin a), (AR p).val.toFun y =
          toLp 2 (fun l ↦ f
            (Fin.append (fun i : Fin b ↦ (p.val (Fin.castAdd a i)).re)
              (fun j : Fin a ↦ y j + (p.val (Fin.natAdd b j)).re)) l)) ∧
        (∀ y, collarComplexHolderFunction (F p.val) y =
          toLp 2 (fun l ↦ (((AR p).val.toFun y l : ℝ) : ℂ))) ∧
        ‖F p.val‖ = ‖AR p‖ := by
  dsimp only
  let p₀R := collarEuclideanRealEquiv (b + a)
    (toLp 2 (Fin.append p₀ (fun _ : Fin a ↦ (0 : ℝ))))
  let z₀ : EuclideanSpace ℂ (Fin (b + a)) :=
    toLp 2 (Fin.append (fun i ↦ (p₀ i : ℂ)) (fun _ : Fin a ↦ 0))
  have hp₀C : (p₀R : EuclideanSpace ℂ (Fin (b + a))) = z₀ := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [p₀R, z₀, collarEuclideanRealEquiv]
  obtain ⟨_, g, ε, ρ, F, q, hε, hρ, _, _, hreal, hFq, _, hF, _⟩ :=
    collar_holomorphic_holder_coefficients f V hV p₀ hp₀ hf hperiod
  obtain ⟨_, r, _, _, hr, _, _, _, _, _⟩ :=
    collar_complex_holder_real_form (a := a) (N := N) (k := 2) (α := (1 / 2 : ℝ))
  let AR (p : collarEuclideanRealSubmodule (b + a)) := r (F p.val)
  have hFc : AnalyticAt ℂ F (p₀R : EuclideanSpace ℂ (Fin (b + a))) := by
    rw [hp₀C]
    exact hFq.analyticAt
  have hAR : AnalyticAt ℝ AR p₀R :=
    (r.analyticAt _).comp (hFc.restrictScalars.comp
      ((collarEuclideanRealSubmodule (b + a)).subtypeL.analyticAt p₀R))
  obtain ⟨R, _, e, _, _, he, _, _, _, _⟩ :=
    collar_complex_holder_closed_real_form (a := a) (N := N) (k := 2) (α := (1 / 2 : ℝ))
  let J := R.subtypeₗᵢ.comp e.toLinearIsometry
  have hJ (u : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
      (y : EuclideanSpace ℝ (Fin a)) :
      collarComplexHolderFunction (J u) y =
        toLp 2 (fun l ↦ ((u.val.toFun y l : ℝ) : ℂ)) := he u y
  have hρR : 0 < (ρ : ℝ) := by exact_mod_cast hρ
  let δ := min (ρ : ℝ) ε
  have hδ : 0 < δ := lt_min hρR hε
  refine ⟨F, AR, hFc, hAR, ?_⟩
  filter_upwards [Metric.ball_mem_nhds p₀R hδ] with p hp
  have hpd : ‖p.val - z₀‖ < δ := by
    change dist p.val (p₀R : EuclideanSpace ℂ (Fin (b + a))) < δ at hp
    simpa only [dist_eq_norm, hp₀C] using hp
  have hz : p.val - z₀ ∈ Metric.eball (0 : EuclideanSpace ℂ (Fin (b + a))) (ρ : ℝ≥0∞) := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    exact (ENNReal.ofReal_lt_coe_iff (norm_nonneg _)).mpr (hpd.trans_le (min_le_left _ _))
  have hpbase (i : Fin b) : |(p.val (Fin.castAdd a i)).re - p₀ i| < ε := by
    have hc := (Complex.abs_re_le_norm ((p.val - z₀) (Fin.castAdd a i))).trans
      (PiLp.norm_apply_le (p.val - z₀) (Fin.castAdd a i))
    have hb := hc.trans_lt (hpd.trans_le (min_le_right _ _))
    simpa only [PiLp.sub_apply, z₀, Fin.append_left, Complex.sub_re,
      Complex.ofReal_re] using hb
  have hcoord (i : Fin (b + a)) : ((p.val i).re : ℂ) = p.val i := by
    apply Complex.ext
    · rfl
    · exact (p.property i).symm
  let source (y : EuclideanSpace ℝ (Fin a)) : EuclideanSpace ℝ (Fin N) :=
    toLp 2 (fun l ↦ f
      (Fin.append (fun i : Fin b ↦ (p.val (Fin.castAdd a i)).re)
        (fun j : Fin a ↦ y j + (p.val (Fin.natAdd b j)).re)) l)
  have hFsource (y : EuclideanSpace ℝ (Fin a)) :
      collarComplexHolderFunction (F p.val) y =
        toLp 2 (fun l ↦ ((source y l : ℝ) : ℂ)) := by
    have hd := hF (p.val - z₀) hz y
    dsimp only at hd
    have hcenter : z₀ + (p.val - z₀) = p.val := by abel
    rw [hcenter] at hd
    have hb : toLp 2 (fun i : Fin b ↦ p.val (Fin.castAdd a i)) =
        toLp 2 (fun i : Fin b ↦ ((p.val (Fin.castAdd a i)).re : ℂ)) := by
      ext i
      exact (hcoord _).symm
    have hy : toLp 2 (fun j : Fin a ↦ (y j : ℂ) + p.val (Fin.natAdd b j)) =
        toLp 2 (fun j : Fin a ↦ ((y j + (p.val (Fin.natAdd b j)).re : ℝ) : ℂ)) := by
      ext j
      change (y j : ℂ) + p.val (Fin.natAdd b j) =
        ((y j + (p.val (Fin.natAdd b j)).re : ℝ) : ℂ)
      rw [Complex.ofReal_add, hcoord]
    rw [hb, hy] at hd
    exact hd.trans (hreal _ _ hpbase).2
  have hARsource (y : EuclideanSpace ℝ (Fin a)) : (AR p).val.toFun y = source y := by
    change (r (F p.val)).val.toFun y = _
    rw [hr, hFsource]
    ext l
    exact Complex.ofReal_re _
  have hJF : J (AR p) = F p.val := by
    apply collarComplexHolderFunction_injective
    funext y
    rw [hJ, hARsource, hFsource]
  refine ⟨hARsource, ?_, ?_⟩
  · intro y
    rw [hFsource, hARsource]
  · calc
      ‖F p.val‖ = ‖J (AR p)‖ := congrArg norm hJF.symm
      _ = ‖AR p‖ := J.norm_map _

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_source_real_holder_family
