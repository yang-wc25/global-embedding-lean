import GlobalEmbedding.Paper.CollarPeriodicAnalyticComplexification
import GlobalEmbedding.Paper.CollarCompactPeriodicJetBounds
import GlobalEmbedding.Paper.CollarTorusComplexStripNeighborhood
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual uniform complex torus strip from real analytic periodic data

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Every extension and uniform bound in this module is constructed.
-/

open Set Filter Metric
open scoped Topology

namespace GlobalEmbedding.Paper

/-- Real analytic periodic data near a whole real orbit have a genuine complex analytic
extension on a common complex base neighborhood times imaginary torus strip. All joint
complex derivatives are uniformly bounded there, modulo the real periodic coordinates.

Source: Proposition `prop:collar`, proof lines 530–534. Construct the actual invariant-domain
complex extension from its real Taylor series, gluing all period translates of its actual
local balls. Thicken the compact real fundamental orbit cube inside that open domain, with
the thickening compact, and bound every actual joint derivative on all its period translates.
The open periodic union of the smaller thickenings contains the entire real orbit. Its exact
uniform strip geometry provides one base/imaginary radius. Every point in that strip reduces
to the compact thickening, so the previously constructed derivative bounds apply there.
No holomorphic extension, coefficient series or spatial derivative bound is an input. -/
theorem collar_periodic_complex_strip
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    {b a : ℕ} (f : (Fin (b + a) → ℝ) → F) (p₀ : Fin b → ℝ)
    (hf : ∀ y : Fin a → ℝ, AnalyticAt ℝ f (Fin.append p₀ y))
    (hperiod : ∀ (x : Fin (b + a) → ℝ) (t : Fin a → ℤ),
      f (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = f x) :
    ∃ (U : Set (Fin (b + a) → ℂ)) (g : (Fin (b + a) → ℂ) → F) (ε : ℝ)
      (M : ℕ → ℝ), 0 < ε ∧ IsOpen U ∧ AnalyticOnNhd ℂ g U ∧
      (∀ x : Fin (b + a) → ℝ, (fun j ↦ (x j : ℂ)) ∈ U → g (fun j ↦ (x j : ℂ)) = f x) ∧
      (∀ (z : Fin (b + a) → ℂ) (t : Fin a → ℤ),
        z + Fin.append (fun _ : Fin b ↦ (0 : ℂ)) (fun j ↦ (t j : ℂ)) ∈ U ↔ z ∈ U) ∧
      (∀ z ∈ U, ∀ t : Fin a → ℤ,
        g (z + Fin.append (fun _ : Fin b ↦ (0 : ℂ)) (fun j ↦ (t j : ℂ))) = g z) ∧
      (∀ j, 0 ≤ M j) ∧
      (∀ z : Fin (b + a) → ℂ,
        (∀ i : Fin b, ‖z (Fin.castAdd a i) - (p₀ i : ℂ)‖ < ε) →
        (∀ j : Fin a, |(z (Fin.natAdd b j)).im| < ε) →
        z ∈ U ∧ ∀ j : ℕ, ‖iteratedFDeriv ℂ j g z‖ ≤ M j) := by
  classical
  let ι (x : Fin (b + a) → ℝ) : Fin (b + a) → ℂ := fun j ↦ (x j : ℂ)
  let L : (Fin a → ℤ) →+ (Fin (b + a) → ℝ) :=
    { toFun := fun t ↦ Fin.append (fun _ : Fin b ↦ 0) (fun j ↦ (t j : ℝ))
      map_zero' := by ext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
      map_add' := by intro s t; ext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp }
  let T : (Fin a → ℤ) →+ (Fin (b + a) → ℂ) :=
    { toFun := fun t ↦ Fin.append (fun _ : Fin b ↦ 0) (fun j ↦ (t j : ℂ))
      map_zero' := by ext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
      map_add' := by intro s t; ext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp }
  have hT (t : Fin a → ℤ) : ι (L t) = T t := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [ι, L, T]
  let S := Set.range (fun y : Fin a → ℝ ↦ Fin.append p₀ y)
  have hfS : AnalyticOnNhd ℝ f S := by
    rintro _ ⟨y, rfl⟩
    exact hf y
  obtain ⟨U, hU, hcover, hinv, g, hg, hreal, hgp⟩ :=
    collar_periodic_analytic_complexification L f S hfS hperiod
  have hUi (z : Fin (b + a) → ℂ) (t : Fin a → ℤ) : z + T t ∈ U ↔ z ∈ U := by
    simpa only [← hT] using hinv z t
  have hgperiod (z : Fin (b + a) → ℂ) (hz : z ∈ U) (t : Fin a → ℤ) : g (z + T t) = g z := by
    simpa only [← hT] using hgp z hz t
  let φ (y : Fin a → ℝ) : Fin (b + a) → ℂ :=
    Fin.append (fun i ↦ (p₀ i : ℂ)) (fun j ↦ (y j : ℂ))
  have hφreal (y : Fin a → ℝ) : φ y = ι (Fin.append p₀ y) := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [φ, ι]
  have hφ : Continuous φ := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [φ, Fin.append_left, Fin.append_right] <;> fun_prop
  let K := φ '' Icc (0 : Fin a → ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image hφ
  have hKU : K ⊆ U := by
    rintro _ ⟨y, _, rfl⟩
    rw [hφreal]
    exact hcover _ ⟨y, rfl⟩
  obtain ⟨δ, hδ, _, hctU, hbounds⟩ :=
    collar_compact_periodic_jet_bounds T g U K hU hg hK hKU hUi hgperiod
  choose M hM hbound using hbounds
  let V : Set (Fin (b + a) → ℂ) := ⋃ t : Fin a → ℤ,
    (fun z ↦ z - T t) ⁻¹' thickening δ K
  have hV : IsOpen V := isOpen_iUnion (fun _ ↦ isOpen_thickening.preimage
    (continuous_id.sub continuous_const))
  have hVshift (z : Fin (b + a) → ℂ) (s : Fin a → ℤ) : z + T s ∈ V ↔ z ∈ V := by
    constructor
    · intro hz
      obtain ⟨t, ht⟩ := mem_iUnion.mp hz
      refine mem_iUnion.mpr ⟨t - s, ?_⟩
      change z - T (t - s) ∈ thickening δ K
      have he : z - T (t - s) = z + T s - T t := by rw [map_sub]; abel
      rw [he]
      exact ht
    · intro hz
      obtain ⟨t, ht⟩ := mem_iUnion.mp hz
      refine mem_iUnion.mpr ⟨t + s, ?_⟩
      change z + T s - T (t + s) ∈ thickening δ K
      rw [map_add]
      have he : z + T s - (T t + T s) = z - T t := by abel
      rw [he]
      exact ht
  have hbaseV (y : Fin a → ℝ) : φ y ∈ V := by
    let t : Fin a → ℤ := fun j ↦ ⌊y j⌋
    let v : Fin a → ℝ := fun j ↦ Int.fract (y j)
    have hv : v ∈ Icc (0 : Fin a → ℝ) 1 :=
      ⟨fun _ ↦ Int.fract_nonneg _, fun _ ↦ (Int.fract_lt_one _).le⟩
    have he : φ y - T t = φ v := by
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [φ, T]
      · intro j
        simp only [φ, T, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Fin.append_right]
        have htj : (t j : ℂ) = ((t j : ℝ) : ℂ) := by norm_cast
        have hreal : y j - (t j : ℝ) = v j := Int.self_sub_floor _
        rw [htj, ← Complex.ofReal_sub, hreal]
    refine mem_iUnion.mpr ⟨t, ?_⟩
    change φ y - T t ∈ thickening δ K
    rw [he]
    exact (self_subset_thickening hδ K) ⟨v, hv, rfl⟩
  obtain ⟨ε, hε, hstrip⟩ := collar_torus_complex_strip_neighborhood V hV p₀ hbaseV hVshift
  refine ⟨U, g, ε, M, hε, hU, hg, hreal, hUi, hgperiod, hM, ?_⟩
  intro z hp him
  obtain ⟨t, ht⟩ := mem_iUnion.mp (hstrip z hp him)
  have hct : z - T t ∈ cthickening δ K := (thickening_subset_cthickening δ K) ht
  have hzU : z ∈ U := by simpa only [sub_add_cancel] using (hbound 0 (z - T t) hct t).1
  refine ⟨hzU, ?_⟩
  intro j
  simpa only [sub_add_cancel] using (hbound j (z - T t) hct t).2

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_periodic_complex_strip
