import GlobalEmbedding.Paper.MatrixAngularConeFiniteSpan
import GlobalEmbedding.Paper.MatrixPlanarOppositeSamples
import GlobalEmbedding.Paper.MatrixParametricPhaseSampling
import GlobalEmbedding.Paper.MatrixNativePlanarProfiles
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp

/-!
# Actual robust angular cone, uniform over the genuine Hopf sphere

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:matrix, lines327–332.
DAG: matrix-angular-cone. W3 owns this exact source before its first edit.
-/
noncomputable section
open Set Filter Metric Manifold
open scoped Topology ContDiff RealInnerProductSpace
namespace GlobalEmbedding.Paper

/-- The literal four angular coordinates; the third argument is the scaled actual
angle derivative. W5 transports this vector to its actual skew-matrix coordinates. -/
def matrixAngularVector (κ θ d : ℝ) : MatrixAngularSpace :=
  WithLp.toLp 2 ![κ * Real.sin θ, κ * Real.cos θ, d, κ]

private theorem angularVector_continuous :
    Continuous (fun x : ℝ × ℝ × ℝ ↦ matrixAngularVector x.1 x.2.1 x.2.2) := by
  unfold matrixAngularVector
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp <;> fun_prop

private theorem normalizedAngular_continuousAt
    {P : Type*} [TopologicalSpace P] (κ s : P → ℝ) (p : P)
    (hκ : ContinuousAt κ p) (hs : ContinuousAt s p) (hn : κ p ≠ 0) (φ : ℝ) :
    ContinuousAt (fun x : P × (ℝ × ℝ) ↦ |κ x.1|⁻¹ •
      matrixAngularVector (κ x.1) (φ + x.2.1) (κ x.1 * s x.1 + x.2.2))
      (p, (0, 0)) := by
  have hk : ContinuousAt (fun x : P × (ℝ × ℝ) ↦ κ x.1) (p, (0, 0)) :=
    hκ.comp continuousAt_fst
  have hss : ContinuousAt (fun x : P × (ℝ × ℝ) ↦ s x.1) (p, (0, 0)) :=
    hs.comp continuousAt_fst
  apply (hk.abs.inv₀ (abs_ne_zero.mpr hn)).smul
  exact angularVector_continuous.continuousAt.comp
    (hk.prodMk ((continuousAt_const.add continuousAt_snd.fst).prodMk
      ((hk.mul hss).add continuousAt_snd.snd)))

private theorem normalizedAngular_center (κ c φ : ℝ) (b : Bool)
    (hκ : if b then 0 < κ else κ < 0) :
    |κ|⁻¹ • matrixAngularVector κ φ (κ * c) =
      if b then WithLp.toLp 2 ![Real.sin φ, Real.cos φ, c, 1]
      else -(WithLp.toLp 2 ![Real.sin φ, Real.cos φ, c, 1]) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hκ ⊢
    rw [abs_of_neg hκ]
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [matrixAngularVector, PiLp.smul_apply, smul_eq_mul,
      hκ.ne]
  · simp only [↓reduceIte] at hκ ⊢
    rw [abs_of_pos hκ]
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [matrixAngularVector, PiLp.smul_apply, smul_eq_mul,
      hκ.ne']

private theorem angular_sample_persistence
    {P : Type*} [TopologicalSpace P] (q : P → ℝ → ℝ) (κ s : P × ℝ → ℝ)
    (hq : Continuous (fun x : P × ℝ ↦ q x.1 x.2)) (hκ : Continuous κ)
    (hs : Continuous s) (p₀ : P) (a q' φ ε : ℝ) (hε : 0 < ε)
    (hd : HasStrictDerivAt (q p₀) q' a) (hq' : q' ≠ 0)
    (hn : κ (p₀, a) ≠ 0) (v : MatrixAngularSpace)
    (hv : |κ (p₀, a)|⁻¹ • matrixAngularVector (κ (p₀, a)) φ
      (κ (p₀, a) * s (p₀, a)) = v) :
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧ ∃ δ m T₀ : ℝ,
      0 < δ ∧ 0 < m ∧ 0 < T₀ ∧
      ∀ p ∈ W, ∀ T : ℝ, T₀ ≤ T → ∀ θ d : ℝ → ℝ,
        (∀ t, |θ t - T * q p t| ≤ δ) →
        (∀ t, |d t - κ (p, t) * s (p, t)| ≤ δ) →
        ∃ t : ℝ, m < |κ (p, t)| ∧
          ‖|κ (p, t)|⁻¹ • matrixAngularVector (κ (p, t)) (θ t) (d t) - v‖ < ε := by
  let N := fun x : (P × ℝ) × (ℝ × ℝ) ↦ |κ x.1|⁻¹ •
    matrixAngularVector (κ x.1) (φ + x.2.1) (κ x.1 * s x.1 + x.2.2)
  have hN := normalizedAngular_continuousAt κ s (p₀, a)
    hκ.continuousAt hs.continuousAt hn φ
  have he : {x | ‖N x - v‖ < ε} ∈ 𝓝 ((p₀, a), (0, 0)) :=
    (hN.sub continuousAt_const).norm (Iio_mem_nhds (by
      change ‖|κ (p₀, a)|⁻¹ • matrixAngularVector (κ (p₀, a)) (φ + 0)
        (κ (p₀, a) * s (p₀, a) + 0) - v‖ < ε
      simpa only [add_zero, hv, sub_self, norm_zero] using hε))
  let m := |κ (p₀, a)| / 2
  have hm : 0 < m := by dsimp [m]; positivity
  have hkm : m < |κ (p₀, a)| := by
    have hh := abs_pos.mpr hn
    dsimp [m]
    linarith
  have hκa : ContinuousAt (fun x : (P × ℝ) × (ℝ × ℝ) ↦ |κ x.1|)
      ((p₀, a), (0, 0)) := hκ.continuousAt.abs.comp continuousAt_fst
  have hg := inter_mem he (hκa (Ioi_mem_nhds hkm))
  obtain ⟨V, E, hV, hpV, hE, hpE, hVE⟩ := mem_nhds_prod_iff'.mp hg
  obtain ⟨W, U, hW, hpW, hU, haU, hWU⟩ := mem_nhds_prod_iff'.mp (hV.mem_nhds hpV)
  obtain ⟨ρ, hρ, hρE⟩ := Metric.mem_nhds_iff.mp (hE.mem_nhds hpE)
  obtain ⟨W', hW', hpW', T₀, hT₀, hsample⟩ :=
    matrix_parametric_phase_sampling q hq p₀ a q' hd hq' U (hU.mem_nhds haU)
  refine ⟨W ∩ W', hW.inter hW', ⟨hpW, hpW'⟩, ρ / 2, m, T₀,
    by positivity, hm, hT₀, ?_⟩
  intro p hp T hT θ d hθ hd'
  obtain ⟨t, ht, n, hphase⟩ := hsample p hp.2 T hT φ
  let e := θ t - T * q p t
  let e' := d t - κ (p, t) * s (p, t)
  have heE : (e, e') ∈ E := by
    apply hρE
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
    exact max_lt (lt_of_le_of_lt (hθ t) (by linarith))
      (lt_of_le_of_lt (hd' t) (by linarith))
  have hgood := hVE (show ((p, t), (e, e')) ∈ V ×ˢ E from
    ⟨hWU (show (p, t) ∈ W ×ˢ U from ⟨hp.1, ht⟩), heE⟩)
  have hsin : Real.sin (θ t) = Real.sin (φ + e) := by
    have hh : θ t = (φ + e) + n * (2 * Real.pi) := by dsimp [e]; linarith
    rw [hh, Real.sin_add_int_mul_two_pi]
  have hcos : Real.cos (θ t) = Real.cos (φ + e) := by
    have hh : θ t = (φ + e) + n * (2 * Real.pi) := by dsimp [e]; linarith
    rw [hh, Real.cos_add_int_mul_two_pi]
  have hNeq : N ((p, t), (e, e')) =
      |κ (p, t)|⁻¹ • matrixAngularVector (κ (p, t)) (θ t) (d t) := by
    have heq : κ (p, t) * s (p, t) + e' = d t := by dsimp [e']; ring
    simp only [N, matrixAngularVector, ← hsin, ← hcos, heq]
  have hnorm : ‖N ((p, t), (e, e')) - v‖ < ε := hgood.1
  rw [hNeq] at hnorm
  exact ⟨t, hgood.2, hnorm⟩

private theorem local_angular_cone
    {P : Type*} [TopologicalSpace P] (q : P → ℝ → ℝ) (κ s : P × ℝ → ℝ)
    (hq : Continuous (fun x : P × ℝ ↦ q x.1 x.2)) (hκ : Continuous κ)
    (hs : Continuous s) (p₀ : P) (a q' : MatrixAngularSample → ℝ)
    (c₀ c₁ : ℝ) (hc : c₀ ≠ c₁)
    (hd : ∀ i, HasStrictDerivAt (q p₀) (q' i) (a i))
    (hq' : ∀ i, q' i ≠ 0) (hn : ∀ i, κ (p₀, a i) ≠ 0)
    (hv : ∀ i, |κ (p₀, a i)|⁻¹ • matrixAngularVector (κ (p₀, a i))
      ((i.1.2 : ℝ) * Real.pi / 2) (κ (p₀, a i) * s (p₀, a i)) =
        matrixAngularTemplate c₀ c₁ i) :
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧ ∃ δ r T₀ : ℝ,
      0 < δ ∧ 0 < r ∧ 0 < T₀ ∧
      ∀ p ∈ W, ∀ T : ℝ, T₀ ≤ T → ∀ θ d : ℝ → ℝ,
        (∀ t, |θ t - T * q p t| ≤ δ) →
        (∀ t, |d t - κ (p, t) * s (p, t)| ≤ δ) →
        ∀ ξ : MatrixAngularSpace, ‖ξ‖ = 1 → ∃ t : ℝ,
          κ (p, t) ≠ 0 ∧ r ≤ ⟪ξ, matrixAngularVector (κ (p, t)) (θ t) (d t)⟫ := by
  classical
  obtain ⟨ε, r, hε, hr, hstable⟩ := matrixAngularTemplate_stable c₀ c₁ hc
  have hone (i : MatrixAngularSample) := angular_sample_persistence q κ s hq hκ hs p₀
    (a i) (q' i) ((i.1.2 : ℝ) * Real.pi / 2) ε hε (hd i) (hq' i) (hn i)
    (matrixAngularTemplate c₀ c₁ i) (hv i)
  choose W hW hpW δ m T₀ hδ hm hT₀ hsample using hone
  let δ₀ := Finset.univ.inf' Finset.univ_nonempty δ
  let m₀ := Finset.univ.inf' Finset.univ_nonempty m
  let T₁ := Finset.univ.sup' Finset.univ_nonempty T₀
  have hδ₀ : 0 < δ₀ := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ ↦ hδ i)
  have hm₀ : 0 < m₀ := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ ↦ hm i)
  have hδle (i) : δ₀ ≤ δ i := Finset.inf'_le _ (Finset.mem_univ i)
  have hmle (i) : m₀ ≤ m i := Finset.inf'_le _ (Finset.mem_univ i)
  have hTle (i) : T₀ i ≤ T₁ := Finset.le_sup' _ (Finset.mem_univ i)
  have hT₁ : 0 < T₁ := (hT₀ default).trans_le (hTle default)
  refine ⟨⋂ i, W i, isOpen_iInter_of_finite hW, by simpa using hpW,
    δ₀, m₀ * r, T₁, hδ₀, mul_pos hm₀ hr, hT₁, ?_⟩
  intro p hp T hT θ d hθ hd' ξ hξ
  have hsi (i : MatrixAngularSample) := hsample i p (mem_iInter.mp hp i) T
    ((hTle i).trans hT) θ d
    (fun t ↦ (hθ t).trans (hδle i)) (fun t ↦ (hd' t).trans (hδle i))
  choose t hkt hnorm using hsi
  let w : MatrixAngularSample → MatrixAngularSpace := fun i ↦ |κ (p, t i)|⁻¹ •
    matrixAngularVector (κ (p, t i)) (θ (t i)) (d (t i))
  obtain ⟨i, hi⟩ := (hstable w (fun i ↦ (hnorm i).le)).1 ξ hξ
  have hki : 0 < |κ (p, t i)| := (hm i).trans (hkt i)
  refine ⟨t i, abs_pos.mp hki, ?_⟩
  have heq : matrixAngularVector (κ (p, t i)) (θ (t i)) (d (t i)) =
      |κ (p, t i)| • w i := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hki.ne', one_smul]
  rw [heq, real_inner_smul_right]
  exact mul_le_mul ((hmle i).trans (hkt i).le) hi hr.le hki.le

private theorem actual_local_angular_cone {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (z : PlanarHopfSphere C) :
    ∃ W : Set (PlanarHopfSphere C), IsOpen W ∧ z ∈ W ∧ ∃ δ r T₀ : ℝ,
      0 < δ ∧ 0 < r ∧ 0 < T₀ ∧
      ∀ p ∈ W, ∀ T : ℝ, T₀ ≤ T → ∀ θ d : PlanarHopfSphere C → ℝ,
        (∀ w, |θ w - T * matrixPlanarT f w| ≤ δ) →
        (∀ w, |d w - planarOrbitCurvature planarHopfFlow f w * matrixPlanarS f w| ≤ δ) →
        ∀ ξ : MatrixAngularSpace, ‖ξ‖ = 1 → ∃ t : ℝ,
          planarOrbitCurvature planarHopfFlow f (planarHopfFlow t p) ≠ 0 ∧
          r ≤ ⟪ξ, matrixAngularVector
            (planarOrbitCurvature planarHopfFlow f (planarHopfFlow t p))
            (θ (planarHopfFlow t p)) (d (planarHopfFlow t p))⟫ := by
  classical
  obtain ⟨cross⟩ := matrix_planar_opposite_samples f hf z
  let q := fun p : PlanarHopfSphere C ↦ fun t : ℝ ↦ matrixPlanarT f (planarHopfFlow t p)
  let κ := fun x : PlanarHopfSphere C × ℝ ↦
    planarOrbitCurvature planarHopfFlow f (planarHopfFlow x.2 x.1)
  let s := fun x : PlanarHopfSphere C × ℝ ↦ matrixPlanarS f (planarHopfFlow x.2 x.1)
  let a := fun i : MatrixAngularSample ↦ cross.time i.1.1 i.2
  let c₀ := Real.cos (cross.level 0)
  let c₁ := Real.cos (cross.level 1)
  have hcj (j : Fin 2) : ![c₀, c₁] j = Real.cos (cross.level j) := by
    fin_cases j <;> rfl
  have hsc (i : MatrixAngularSample) : s (z, a i) = ![c₀, c₁] i.1.1 := by
    rw [hcj]
    exact cross.velocity_zero _ _
  have hsign (i : MatrixAngularSample) : if i.2 then 0 < κ (z, a i) else κ (z, a i) < 0 := by
    rcases i with ⟨⟨j, k⟩, b⟩
    cases b
    · exact cross.negative j
    · exact cross.positive j
  have hkn (i : MatrixAngularSample) : κ (z, a i) ≠ 0 := by
    have hh := hsign i
    split_ifs at hh
    · exact hh.ne'
    · exact hh.ne
  have hsn (i : MatrixAngularSample) : s (z, a i) ≠ 0 := by
    rw [hsc, hcj]
    exact cross.cos_nonzero _
  have hdata := matrix_planar_data_contMDiff f hf.smooth
  have hflow : Continuous (fun x : PlanarHopfSphere C × ℝ ↦ planarHopfFlow x.2 x.1) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_snd.prodMk continuous_fst)
  have hqc : Continuous (fun x : PlanarHopfSphere C × ℝ ↦ q x.1 x.2) :=
    hdata.2.1.continuous.comp hflow
  have hκc : Continuous κ := hf.curvature_smooth.continuous.comp hflow
  have hsc' : Continuous s := hdata.1.continuous.comp hflow
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf.smooth
  have hvd (w : PlanarHopfSphere C) : Differentiable ℝ
      (fun t : ℝ ↦ orbitDeriv planarHopfFlow f (planarHopfFlow t w)) :=
    fun t ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add _ hv t w).differentiableAt
  have hqd (t : ℝ) : HasDerivAt (q z) (κ (z, t) * s (z, t)) t := by
    have hh := planarOrbitCoordinate_hasDerivAt planarHopfFlow planarHopfFlow_add
      (orbitDeriv planarHopfFlow f) hvd z t 1
    rw [hf.acceleration] at hh
    simpa only [q, κ, s, matrixPlanarT, matrixPlanarS, PiLp.smul_apply, smul_eq_mul,
      planarQuarterTurn_apply_one] using hh
  have hqsmooth : ContDiff ℝ ∞ (q z) :=
    (hdata.2.1.comp ((planarHopfFlow_contMDiff C).comp
      (contMDiff_id.prodMk contMDiff_const))).contDiff
  have hd (i : MatrixAngularSample) :
      HasStrictDerivAt (q z) (κ (z, a i) * s (z, a i)) (a i) :=
    hqsmooth.contDiffAt.hasStrictDerivAt' (hqd (a i)) (by simp)
  have hbase (i : MatrixAngularSample) :
      |κ (z, a i)|⁻¹ • matrixAngularVector (κ (z, a i)) ((i.1.2 : ℝ) * Real.pi / 2)
        (κ (z, a i) * s (z, a i)) = matrixAngularTemplate c₀ c₁ i := by
    rw [normalizedAngular_center _ _ _ _ (hsign i), hsc]
    rfl
  obtain ⟨W, hW, hzW, δ, r, T₀, hδ, hr, hT₀, hlocal⟩ := local_angular_cone
    q κ s hqc hκc hsc' z a (fun i ↦ κ (z, a i) * s (z, a i)) c₀ c₁
    cross.cos_levels_ne hd (fun i ↦ mul_ne_zero (hkn i) (hsn i)) hkn hbase
  refine ⟨W, hW, hzW, δ, r, T₀, hδ, hr, hT₀, ?_⟩
  intro p hp T hT θ d hθ hd' ξ hξ
  exact hlocal p hp T hT (fun t ↦ θ (planarHopfFlow t p))
    (fun t ↦ d (planarHopfFlow t p)) (fun t ↦ hθ _) (fun t ↦ hd' _) ξ hξ

/-- The actual four-coordinate cone has a uniform positive-support margin on every
actual Hopf orbit under uniform small errors in the angle and its scaled derivative.
The constants are constructed from the given actual selector, not assumed as data.
Compactness is used on the genuine sphere; no quotient chart or global angle is needed. -/
theorem matrix_angular_cone_uniform {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f) :
    ∃ δ r T₀ : ℝ, 0 < δ ∧ 0 < r ∧ 0 < T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ θ d : PlanarHopfSphere C → ℝ,
        (∀ w, |θ w - T * matrixPlanarT f w| ≤ δ) →
        (∀ w, |d w - planarOrbitCurvature planarHopfFlow f w * matrixPlanarS f w| ≤ δ) →
        ∀ p : PlanarHopfSphere C, ∀ ξ : MatrixAngularSpace, ‖ξ‖ = 1 → ∃ t : ℝ,
          planarOrbitCurvature planarHopfFlow f (planarHopfFlow t p) ≠ 0 ∧
          r ≤ ⟪ξ, matrixAngularVector
            (planarOrbitCurvature planarHopfFlow f (planarHopfFlow t p))
            (θ (planarHopfFlow t p)) (d (planarHopfFlow t p))⟫ := by
  let Good := fun S : Set (PlanarHopfSphere C) ↦
    ∃ δ r T₀ : ℝ, 0 < δ ∧ 0 < r ∧ 0 < T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ θ d : PlanarHopfSphere C → ℝ,
        (∀ w, |θ w - T * matrixPlanarT f w| ≤ δ) →
        (∀ w, |d w - planarOrbitCurvature planarHopfFlow f w * matrixPlanarS f w| ≤ δ) →
        ∀ p ∈ S, ∀ ξ : MatrixAngularSpace, ‖ξ‖ = 1 → ∃ t : ℝ,
          planarOrbitCurvature planarHopfFlow f (planarHopfFlow t p) ≠ 0 ∧
          r ≤ ⟪ξ, matrixAngularVector
            (planarOrbitCurvature planarHopfFlow f (planarHopfFlow t p))
            (θ (planarHopfFlow t p)) (d (planarHopfFlow t p))⟫
  have hall : Good univ := by
    apply (isCompact_univ : IsCompact (univ : Set (PlanarHopfSphere C))).induction_on (p := Good)
    · refine ⟨1, 1, 1, one_pos, one_pos, one_pos, ?_⟩
      intro T hT θ d hθ hd p hp
      exact (notMem_empty p hp).elim
    · intro S S' hsub hgood
      obtain ⟨δ, r, T₀, hδ, hr, hT₀, hh⟩ := hgood
      exact ⟨δ, r, T₀, hδ, hr, hT₀, fun T hT θ d hθ hd p hp ↦
        hh T hT θ d hθ hd p (hsub hp)⟩
    · intro S S' hgood hgood'
      obtain ⟨δ, r, T₀, hδ, hr, hT₀, hh⟩ := hgood
      obtain ⟨δ', r', T₀', hδ', hr', hT₀', hh'⟩ := hgood'
      refine ⟨min δ δ', min r r', max T₀ T₀', lt_min hδ hδ', lt_min hr hr',
        hT₀.trans_le (le_max_left _ _), ?_⟩
      intro T hT θ d hθ hd p hp ξ hξ
      rcases hp with hp | hp
      · obtain ⟨t, ht, hm⟩ := hh T ((le_max_left _ _).trans hT) θ d
          (fun w ↦ (hθ w).trans (min_le_left _ _))
          (fun w ↦ (hd w).trans (min_le_left _ _)) p hp ξ hξ
        exact ⟨t, ht, (min_le_left _ _).trans hm⟩
      · obtain ⟨t, ht, hm⟩ := hh' T ((le_max_right _ _).trans hT) θ d
          (fun w ↦ (hθ w).trans (min_le_right _ _))
          (fun w ↦ (hd w).trans (min_le_right _ _)) p hp ξ hξ
        exact ⟨t, ht, (min_le_right _ _).trans hm⟩
    · intro p hp
      obtain ⟨W, hW, hpW, δ, r, T₀, hδ, hr, hT₀, hh⟩ := actual_local_angular_cone f hf p
      refine ⟨W, nhdsWithin_le_nhds (hW.mem_nhds hpW), δ, r, T₀, hδ, hr, hT₀, ?_⟩
      intro T hT θ d hθ hd p hp
      exact hh p hp T hT θ d hθ hd
  obtain ⟨δ, r, T₀, hδ, hr, hT₀, hh⟩ := hall
  exact ⟨δ, r, T₀, hδ, hr, hT₀, fun T hT θ d hθ hd p ↦
    hh T hT θ d hθ hd p (mem_univ p)⟩

private theorem actual_phase_orbitDeriv {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (z : PlanarHopfSphere C) : orbitDeriv planarHopfFlow (matrixPlanarT f) z =
      planarOrbitCurvature planarHopfFlow f z * matrixPlanarS f z := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf.smooth
  have hvd (w : PlanarHopfSphere C) : Differentiable ℝ
      (fun t : ℝ ↦ orbitDeriv planarHopfFlow f (planarHopfFlow t w)) :=
    fun t ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add _ hv t w).differentiableAt
  have hd := (planarOrbitCoordinate_hasDerivAt planarHopfFlow planarHopfFlow_add
    (orbitDeriv planarHopfFlow f) hvd z 0 1).deriv
  rw [hf.acceleration] at hd
  change deriv (fun t : ℝ ↦ matrixPlanarT f (planarHopfFlow t z)) 0 = _
  simpa only [matrixPlanarT, matrixPlanarS, planarHopfFlow_zero, PiLp.smul_apply,
    smul_eq_mul, planarQuarterTurn_apply_one] using hd

private theorem actual_angle_error_orbitDeriv {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) (T : ℝ)
    (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (fun w ↦ θ w - T * matrixPlanarT f w) z =
      orbitDeriv planarHopfFlow θ z -
        T * (planarOrbitCurvature planarHopfFlow f z * matrixPlanarS f z) := by
  have hdθ := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add θ hθ 0 z
  have hdq := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add (matrixPlanarT f) (matrix_planar_data_contMDiff f hf.smooth).2.1 0 z
  have hh := (hdθ.fun_sub (hdq.const_mul T)).deriv
  have heq : orbitDeriv planarHopfFlow (fun w ↦ θ w - T * matrixPlanarT f w) z =
      orbitDeriv planarHopfFlow θ z - T * orbitDeriv planarHopfFlow (matrixPlanarT f) z := by
    simpa only [orbitDeriv, planarHopfFlow_zero, Pi.sub_apply] using hh
  rw [actual_phase_orbitDeriv f hf] at heq
  exact heq

/-- The original uniform C0 plus scaled actual-X error is sufficient for the actual
uniform angular cone. The four coordinates are literally those of the paper,
including the actual derivative Xtheta/T, and samples avoid actual curvature zero. -/
theorem matrix_angular_cone_scaled_error {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f) :
    ∃ δ r T₀ : ℝ, 0 < δ ∧ 0 < r ∧ 0 < T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ θ : PlanarHopfSphere C → ℝ,
        ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ →
        (∀ w, |θ w - T * matrixPlanarT f w| + T⁻¹ *
          |orbitDeriv planarHopfFlow (fun z ↦ θ z - T * matrixPlanarT f z) w| ≤ δ) →
        ∀ p : PlanarHopfSphere C, ∀ ξ : MatrixAngularSpace, ‖ξ‖ = 1 → ∃ t : ℝ,
          planarOrbitCurvature planarHopfFlow f (planarHopfFlow t p) ≠ 0 ∧
          r ≤ ⟪ξ, matrixAngularVector
            (planarOrbitCurvature planarHopfFlow f (planarHopfFlow t p))
            (θ (planarHopfFlow t p))
            (T⁻¹ * orbitDeriv planarHopfFlow θ (planarHopfFlow t p))⟫ := by
  obtain ⟨δ, r, T₀, hδ, hr, hT₀, hcone⟩ := matrix_angular_cone_uniform f hf
  refine ⟨δ, r, T₀, hδ, hr, hT₀, ?_⟩
  intro T hT θ hθ he
  have hTp : 0 < T := hT₀.trans_le hT
  apply hcone T hT θ (fun w ↦ T⁻¹ * orbitDeriv planarHopfFlow θ w)
  · intro w
    exact (le_add_of_nonneg_right
      (mul_nonneg (inv_nonneg.mpr hTp.le) (abs_nonneg _))).trans (he w)
  · intro w
    have hid : T⁻¹ * orbitDeriv planarHopfFlow θ w -
        planarOrbitCurvature planarHopfFlow f w * matrixPlanarS f w =
      T⁻¹ * orbitDeriv planarHopfFlow (fun z ↦ θ z - T * matrixPlanarT f z) w := by
      rw [actual_angle_error_orbitDeriv f hf θ hθ]
      field_simp
    rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hTp)]
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (he w)

/-- Under the original scaled-error convergence, all sufficiently large actual
angles give true positive support in every nonzero four-dimensional direction,
on every actual Hopf orbit and away from its actual curvature zeros. -/
theorem matrix_angular_cone {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : ℝ → PlanarHopfSphere C → ℝ)
    (hθ : ∀ᶠ T in atTop, ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (θ T))
    (he : ∀ ε > 0, ∀ᶠ T in atTop, ∀ w,
      |θ T w - T * matrixPlanarT f w| + T⁻¹ *
        |orbitDeriv planarHopfFlow (fun z ↦ θ T z - T * matrixPlanarT f z) w| ≤ ε) :
    ∀ᶠ T in atTop, ∀ p : PlanarHopfSphere C, ∀ ξ : MatrixAngularSpace, ξ ≠ 0 → ∃ t : ℝ,
      planarOrbitCurvature planarHopfFlow f (planarHopfFlow t p) ≠ 0 ∧
      0 < ⟪ξ, matrixAngularVector
        (planarOrbitCurvature planarHopfFlow f (planarHopfFlow t p))
        (θ T (planarHopfFlow t p))
        (T⁻¹ * orbitDeriv planarHopfFlow (θ T) (planarHopfFlow t p))⟫ := by
  obtain ⟨δ, r, T₀, hδ, hr, hT₀, hcone⟩ := matrix_angular_cone_scaled_error f hf
  filter_upwards [eventually_ge_atTop T₀, hθ, he δ hδ] with T hT hθT heT
  intro p ξ hξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hunit : ‖‖ξ‖⁻¹ • ξ‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  obtain ⟨t, hκ, hi⟩ := hcone T hT (θ T) hθT heT p (‖ξ‖⁻¹ • ξ) hunit
  have hpos := hr.trans_le hi
  rw [real_inner_smul_left] at hpos
  exact ⟨t, hκ, (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hpos⟩

end GlobalEmbedding.Paper
