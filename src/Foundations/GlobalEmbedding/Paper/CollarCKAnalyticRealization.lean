import GlobalEmbedding.Paper.CollarCKAnalyticRealizationUnique
import GlobalEmbedding.Paper.CollarCKGoursatAnalyticPrepared
import GlobalEmbedding.Paper.CollarCKMajorantDomination

/-!
# Actual analytic uniqueness of the same canonical CK solution

Source: Gantumur, notes2, Theorem18. The compiled actual-PDE prefix is frozen separately as
CollarCKAnalyticPDEBridge.lean; its scalar parameters are now discharged by their accepted sole
W3/W6 providers.
Continue the full original parent here by converting actual competitors to the same formal
solution and invoking the accepted equality-of-coefficients to equality-of-germs theorem.
-/

noncomputable section
open scoped Topology
namespace GlobalEmbedding.Paper
variable {n m : ℕ}
local notation "S" => (CollarCKFullIndex n → ℝ)
local notation "V" => (Fin m → ℝ)
local notation "A" => ((Fin n ⊕ CollarCKSlot n m) → ℝ)

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "E" => (ℝ × X)
local notation "D" => (X × ℝ × V × (Fin n → V))

/-- Transport the genuine nonlinear PDE through the sole accepted full-coordinate equivalence.
Source: Gantumur, Theorem18, change of finite-dimensional coordinates. Reuse the accepted
actual scalar coordinate derivative identities and native vector projection derivative. -/
theorem collarCKNativeCoordinatePDE_iff (H : D → V) (w : E → V)
    (hw : AnalyticAt ℝ w 0) :
    (∀ᶠ z in 𝓝 (0 : S), ∀ j,
      fderiv ℝ (fun y ↦ w (collarCKFullCoordinates y) j) z (Pi.single (Sum.inl ()) 1) =
        (H ∘ collarCKRHSCoordinates)
          (Sum.elim (fun i ↦ z (Sum.inr i))
            (Sum.elim (fun _ ↦ z (Sum.inl ()))
              (Sum.elim (fun j ↦ w (collarCKFullCoordinates z) j)
                (fun ij ↦ fderiv ℝ (fun y ↦ w (collarCKFullCoordinates y) ij.2) z
                  (Pi.single (Sum.inr ij.1) 1))))) j) ↔
    (∀ᶠ z in 𝓝 (0 : E), fderiv ℝ w z (1, 0) =
      H (z.2, z.1, w z, fun i ↦ fderiv ℝ w z (0, EuclideanSpace.single i 1))) := by
  have hC : Filter.Tendsto (collarCKFullCoordinates (n := n)) (𝓝 0) (𝓝 0) := by
    have ht : Filter.Tendsto (collarCKFullCoordinates (n := n)) (𝓝 0)
        (𝓝 (collarCKFullCoordinates 0)) := collarCKFullCoordinates.continuous.continuousAt
    simpa only [map_zero] using ht
  have hCi : Filter.Tendsto (collarCKFullCoordinates (n := n)).symm (𝓝 0) (𝓝 0) := by
    have ht : Filter.Tendsto (collarCKFullCoordinates (n := n)).symm (𝓝 0)
        (𝓝 (collarCKFullCoordinates.symm 0)) :=
      collarCKFullCoordinates.symm.continuous.continuousAt
    simpa only [map_zero] using ht
  have hd : ∀ᶠ z : S in 𝓝 0, ∀ j,
      fderiv ℝ (fun y ↦ w (collarCKFullCoordinates y) j) z (Pi.single (Sum.inl ()) 1) =
        fderiv ℝ w (collarCKFullCoordinates z) (1, 0) j ∧
      ∀ i, fderiv ℝ (fun y ↦ w (collarCKFullCoordinates y) j) z
          (Pi.single (Sum.inr i) 1) =
        fderiv ℝ w (collarCKFullCoordinates z) (0, EuclideanSpace.single i 1) j := by
    have hscalar : ∀ j : Fin m, ∀ᶠ z : S in 𝓝 0,
        fderiv ℝ (fun y ↦ w (collarCKFullCoordinates y) j) z
            (Pi.single (Sum.inl ()) 1) =
          fderiv ℝ (fun y ↦ w y j) (collarCKFullCoordinates z) (1, 0) ∧
        ∀ i, fderiv ℝ (fun y ↦ w (collarCKFullCoordinates y) j) z
            (Pi.single (Sum.inr i) 1) =
          fderiv ℝ (fun y ↦ w y j) (collarCKFullCoordinates z)
            (0, EuclideanSpace.single i 1) := by
      intro j
      exact collarCKGoursat_coordinate_derivatives (fun y ↦ w y j)
        (((ContinuousLinearMap.proj j : V →L[ℝ] ℝ).analyticAt _).comp hw)
    filter_upwards [Filter.eventually_all.mpr hscalar,
      hC.eventually hw.eventually_analyticAt] with z hz hzw j
    simpa only [fderiv_apply hzw.differentiableAt, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using hz j
  have hpoint : ∀ᶠ z : S in 𝓝 0,
      (∀ j, fderiv ℝ (fun y ↦ w (collarCKFullCoordinates y) j) z
          (Pi.single (Sum.inl ()) 1) =
        (H ∘ collarCKRHSCoordinates)
          (Sum.elim (fun i ↦ z (Sum.inr i))
            (Sum.elim (fun _ ↦ z (Sum.inl ()))
              (Sum.elim (fun j ↦ w (collarCKFullCoordinates z) j)
                (fun ij ↦ fderiv ℝ (fun y ↦ w (collarCKFullCoordinates y) ij.2) z
                  (Pi.single (Sum.inr ij.1) 1))))) j) ↔
      fderiv ℝ w (collarCKFullCoordinates z) (1, 0) =
        H ((collarCKFullCoordinates z).2, (collarCKFullCoordinates z).1,
          w (collarCKFullCoordinates z),
          fun i ↦ fderiv ℝ w (collarCKFullCoordinates z) (0, EuclideanSpace.single i 1)) := by
    filter_upwards [hd] with z hz
    have hslots : collarCKRHSCoordinates
        (Sum.elim (fun i ↦ z (Sum.inr i))
          (Sum.elim (fun _ ↦ z (Sum.inl ()))
            (Sum.elim (fun j ↦ w (collarCKFullCoordinates z) j)
              (fun ij ↦ fderiv ℝ (fun y ↦ w (collarCKFullCoordinates y) ij.2) z
                (Pi.single (Sum.inr ij.1) 1))))) =
        ((collarCKFullCoordinates z).2, (collarCKFullCoordinates z).1,
          w (collarCKFullCoordinates z),
          fun i ↦ fderiv ℝ w (collarCKFullCoordinates z) (0, EuclideanSpace.single i 1)) := by
      change (WithLp.toLp 2 (fun i ↦ z (Sum.inr i)), z (Sum.inl ()),
        w (collarCKFullCoordinates z), _) = _
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
      funext i j
      exact (hz j).2 i
    simp only [Function.comp_apply, hslots, (hz _).1]
    exact funext_iff.symm
  constructor
  · intro h
    have hn := (Filter.eventually_congr hpoint).mp h
    have ht := hCi.eventually hn
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using ht
  · intro h
    exact (Filter.eventually_congr hpoint).mpr (hC.eventually h)

/-- The same actual normalized solution and actual analytic-competitor uniqueness in the
original joint Euclidean coordinates. Source: Gantumur, Theorem18. Transport the already
constructed full-coordinate solution through the accepted continuous linear equivalence;
its derivative transport is exactly the preceding reuse wrapper. No dimension positivity. -/
theorem collarCKNativeExistenceUniqueGeometric
    (H : D → V) (p : FormalMultilinearSeries ℝ A V)
    (hp : HasFPowerSeriesAt (H ∘ collarCKRHSCoordinates) p 0)
    (M s : ℝ) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hbound : ∀ d j,
      |MvPowerSeries.coeff d
        (collarCKFlatten (collarCKFormalSolution (collarCKTaylorRHS p)) j)| ≤
          M * s ^ d.degree) :
    ∃ w : E → V, AnalyticAt ℝ w 0 ∧ (∀ x, w (0, x) = 0) ∧
      (∀ᶠ z in 𝓝 (0 : E), fderiv ℝ w z (1, 0) =
        H (z.2, z.1, w z, fun i ↦ fderiv ℝ w z (0, EuclideanSpace.single i 1))) ∧
      ∀ v : E → V, AnalyticAt ℝ v 0 →
        (∀ᶠ x : X in 𝓝 0, v (0, x) = 0) →
        (∀ᶠ z in 𝓝 (0 : E), fderiv ℝ v z (1, 0) =
          H (z.2, z.1, v z, fun i ↦ fderiv ℝ v z (0, EuclideanSpace.single i 1))) →
        w =ᶠ[𝓝 0] v := by
  obtain ⟨u, hu, hui, huPDE, huniq⟩ :=
    collarCKAnalyticExistenceUniqueGeometric (H ∘ collarCKRHSCoordinates) p hp M s hM hs hbound
  let w : E → V := u ∘ collarCKFullCoordinates.symm
  have hw : AnalyticAt ℝ w 0 := hu.comp_of_eq
    (collarCKFullCoordinates.symm.toContinuousLinearMap.analyticAt 0) (map_zero _)
  have hwPDE := (collarCKNativeCoordinatePDE_iff H w hw).mp (by
    simpa only [w, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using huPDE)
  refine ⟨w, hw, ?_, hwPDE, ?_⟩
  · intro x
    apply hui
    rfl
  · intro v hv hvi hvPDE
    have hvC : AnalyticAt ℝ (v ∘ collarCKFullCoordinates) 0 := hv.comp_of_eq
      (collarCKFullCoordinates.toContinuousLinearMap.analyticAt 0) (map_zero _)
    have hCi : Filter.Tendsto (collarCKFullCoordinates (n := n)).symm (𝓝 0) (𝓝 0) := by
      have ht : Filter.Tendsto (collarCKFullCoordinates (n := n)).symm (𝓝 0)
          (𝓝 (collarCKFullCoordinates.symm 0)) :=
        collarCKFullCoordinates.symm.continuous.continuousAt
      simpa only [map_zero] using ht
    have hX : Filter.Tendsto (WithLp.toLp 2 : (Fin n → ℝ) → X) (𝓝 0) (𝓝 0) := by
      have ht : Filter.Tendsto (WithLp.toLp 2 : (Fin n → ℝ) → X) (𝓝 0)
          (𝓝 (WithLp.toLp 2 (0 : Fin n → ℝ))) :=
        (PiLp.continuous_toLp 2 _).continuousAt
      simpa using ht
    have hviC : ∀ᶠ x : Fin n → ℝ in 𝓝 0,
        (v ∘ collarCKFullCoordinates) (Sum.elim (fun _ : Unit ↦ (0 : ℝ)) x) = 0 := by
      exact hX.eventually hvi
    have hEq := huniq (v ∘ collarCKFullCoordinates) hvC hviC
      ((collarCKNativeCoordinatePDE_iff H v hv).mpr hvPDE)
    have ht := hCi.eventually hEq
    change ∀ᶠ x : E in 𝓝 0, u (collarCKFullCoordinates.symm x) = v x
    simpa only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using ht

/-- Original-data analytic existence and actual competitor uniqueness as germs, without
positive-dimension restrictions. Source: Gantumur, Theorem18 and Corollary20. Consume the
accepted actual majorant bound, then undo the accepted actual normalization for both the
constructed solution and every competing analytic function. -/
theorem collarCKOriginalExistenceUniqueGerm
    (G : D → V) (v₀ : X → V) (x₀ : X) (hv₀ : AnalyticAt ℝ v₀ x₀)
    (hG : AnalyticAt ℝ G (x₀, 0, v₀ x₀, collarCKInitialSpatialJet v₀ x₀)) :
    ∃ u : E → V, AnalyticAt ℝ u (0, x₀) ∧ (∀ x, u (0, x) = v₀ x) ∧
      (∀ᶠ z in 𝓝 ((0, x₀) : E), fderiv ℝ u z (1, 0) =
        G (z.2, z.1, u z, fun i ↦ fderiv ℝ u z (0, EuclideanSpace.single i 1))) ∧
      ∀ v : E → V, AnalyticAt ℝ v (0, x₀) →
        (∀ᶠ x : X in 𝓝 x₀, v (0, x) = v₀ x) →
        (∀ᶠ z in 𝓝 ((0, x₀) : E), fderiv ℝ v z (1, 0) =
          G (z.2, z.1, v z, fun i ↦ fderiv ℝ v z (0, EuclideanSpace.single i 1))) →
        u =ᶠ[𝓝 (0, x₀)] v := by
  obtain ⟨p, hp, _, M, s, hM, hs, hbound⟩ :=
    collarCKOriginalData_formal_geometric G v₀ x₀ hv₀ hG
  obtain ⟨w, hw, hwi, hwPDE, hwuniq⟩ := collarCKNativeExistenceUniqueGeometric
    (collarCKNormalizedRHS G v₀ x₀) p hp M s hM.le hs.le hbound
  let u := collarCKRestoreUnknown G v₀ x₀ w
  have hu : AnalyticAt ℝ u (0, x₀) :=
    collarCKRestoreUnknown_analyticAt G v₀ x₀ w 0 x₀
      (by simpa only [sub_self, Prod.zero_eq_mk] using hw) hv₀
  have hminus : Filter.Tendsto (fun z : E ↦ (z.1, z.2 - x₀))
      (𝓝 (0, x₀)) (𝓝 0) := by
    have hc : Continuous (fun z : E ↦ (z.1, z.2 - x₀)) := by fun_prop
    simpa only [sub_self, Prod.zero_eq_mk] using hc.tendsto (0, x₀)
  have hplus : Filter.Tendsto (fun z : E ↦ (z.1, x₀ + z.2))
      (𝓝 0) (𝓝 (0, x₀)) := by
    have hc : Continuous (fun z : E ↦ (z.1, x₀ + z.2)) := by fun_prop
    simpa using hc.tendsto 0
  have hvnear : ∀ᶠ z : E in 𝓝 (0, x₀), AnalyticAt ℝ v₀ z.2 :=
    (continuous_snd.tendsto ((0, x₀) : E)).eventually hv₀.eventually_analyticAt
  have huPDE : ∀ᶠ z : E in 𝓝 (0, x₀), fderiv ℝ u z (1, 0) =
      G (z.2, z.1, u z, fun i ↦ fderiv ℝ u z (0, EuclideanSpace.single i 1)) := by
    filter_upwards [hminus.eventually hwPDE, hu.eventually_analyticAt, hvnear]
      with z hz huz hvz
    have he := collarCKNormalizeUnknown_equation_iff G v₀ x₀ u z.1 (z.2 - x₀)
      (by simpa using huz.differentiableAt) (by simpa using hvz.differentiableAt)
    have hn : collarCKNormalizeUnknown G v₀ x₀ u = w :=
      collarCKNormalizeUnknown_restore G v₀ x₀ w
    rw [hn] at he
    simpa using he.mp hz
  refine ⟨u, hu, ?_, huPDE, ?_⟩
  · intro x
    simp [u, collarCKRestoreUnknown, hwi]
  · intro v hv hvi hvPDE
    let wv := collarCKNormalizeUnknown G v₀ x₀ v
    have hwv : AnalyticAt ℝ wv 0 := by
      simpa only [wv, Prod.zero_eq_mk] using
        collarCKNormalizeUnknown_analyticAt G v₀ x₀ v 0 0
        (by simpa using hv) (by simpa using hv₀)
    have hspatial : Filter.Tendsto (fun y : X ↦ x₀ + y) (𝓝 0) (𝓝 x₀) := by
      have hc : Continuous (fun y : X ↦ x₀ + y) := by fun_prop
      simpa only [add_zero] using hc.tendsto (0 : X)
    have hwvi : ∀ᶠ y : X in 𝓝 0, wv (0, y) = 0 := by
      filter_upwards [hspatial.eventually hvi] with y hy
      exact (collarCKNormalizeUnknown_initial_iff G v₀ x₀ v y).mpr hy
    have hwvPDE : ∀ᶠ z : E in 𝓝 0, fderiv ℝ wv z (1, 0) =
        collarCKNormalizedRHS G v₀ x₀
          (z.2, z.1, wv z, fun i ↦ fderiv ℝ wv z (0, EuclideanSpace.single i 1)) := by
      filter_upwards [hplus.eventually hvPDE, hplus.eventually hv.eventually_analyticAt,
        hplus.eventually hvnear] with z hz hvz hv₀z
      exact (collarCKNormalizeUnknown_equation_iff G v₀ x₀ v z.1 z.2
        hvz.differentiableAt hv₀z.differentiableAt).mpr hz
    have hEq := hwuniq wv hwv hwvi hwvPDE
    have hEq' := hminus.eventually hEq
    change ∀ᶠ z : E in 𝓝 (0, x₀), u z = v z
    filter_upwards [hEq'] with z hz
    have hrestore := congrArg
      (fun a : V ↦ a + v₀ z.2 + z.1 • collarCKInitialRHS G v₀ x₀) hz
    change collarCKRestoreUnknown G v₀ x₀ w z = v z
    have hid := congrFun (collarCKRestoreUnknown_normalize G v₀ x₀ v) z
    exact hrestore.trans hid

/-- Full original first-order CK existence and quantitative local uniqueness, including
zero spatial or value dimension. Source: Gantumur, Theorem18 and Corollary20. Choose a ball
inside the actual analytic/PDE neighborhood and shrink the competitor equality ball below
both supplied radii. This is the original theorem's complete conclusion without dimension
positivity; every analytic and majorant premise comes from the original data alone. -/
theorem collarCKOriginalExistenceUnique
    (G : D → V) (v₀ : X → V) (x₀ : X) (hv₀ : AnalyticAt ℝ v₀ x₀)
    (hG : AnalyticAt ℝ G (x₀, 0, v₀ x₀, collarCKInitialSpatialJet v₀ x₀)) :
    ∃ ε > 0, ∃ u : E → V,
      AnalyticOnNhd ℝ u (Metric.ball (0, x₀) ε) ∧
      (∀ r x, (r, x) ∈ Metric.ball (0, x₀) ε →
        fderiv ℝ u (r, x) (1, 0) =
          G (x, r, u (r, x), fun i ↦ fderiv ℝ u (r, x) (0, EuclideanSpace.single i 1))) ∧
      (∀ x, x ∈ Metric.ball x₀ ε → u (0, x) = v₀ x) ∧
      (∀ v η, 0 < η → AnalyticOnNhd ℝ v (Metric.ball (0, x₀) η) →
        (∀ r x, (r, x) ∈ Metric.ball (0, x₀) η →
          fderiv ℝ v (r, x) (1, 0) =
            G (x, r, v (r, x), fun i ↦ fderiv ℝ v (r, x) (0, EuclideanSpace.single i 1))) →
        (∀ x, x ∈ Metric.ball x₀ η → v (0, x) = v₀ x) →
        ∃ δ > 0, δ ≤ ε ∧ δ ≤ η ∧
          ∀ r x, (r, x) ∈ Metric.ball (0, x₀) δ → u (r, x) = v (r, x)) := by
  obtain ⟨u, hu, hui, huPDE, huniq⟩ := collarCKOriginalExistenceUniqueGerm G v₀ x₀ hv₀ hG
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hu.eventually_analyticAt.and huPDE)
  refine ⟨ε, hε, u, ?_, ?_, fun x _ ↦ hui x, ?_⟩
  · intro z hz
    exact (hball z hz).1
  · intro r x hx
    exact (hball (r, x) hx).2
  · intro v η hη hv hvPDE hvi
    have hv0 : AnalyticAt ℝ v (0, x₀) := hv _ (Metric.mem_ball_self hη)
    have hvi' : ∀ᶠ x : X in 𝓝 x₀, v (0, x) = v₀ x := by
      filter_upwards [Metric.ball_mem_nhds x₀ hη] with x hx
      exact hvi x hx
    have hvPDE' : ∀ᶠ z : E in 𝓝 (0, x₀), fderiv ℝ v z (1, 0) =
        G (z.2, z.1, v z, fun i ↦ fderiv ℝ v z (0, EuclideanSpace.single i 1)) := by
      filter_upwards [Metric.ball_mem_nhds ((0, x₀) : E) hη] with z hz
      exact hvPDE z.1 z.2 hz
    have hEq := huniq v hv0 hvi' hvPDE'
    obtain ⟨δ₀, hδ₀, hEqball⟩ := Metric.eventually_nhds_iff_ball.mp hEq
    refine ⟨min δ₀ (min ε η), lt_min hδ₀ (lt_min hε hη),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _), ?_⟩
    intro r x hx
    exact hEqball (r, x) (Metric.ball_subset_ball (min_le_left _ _) hx)

#print axioms collarCKNativeCoordinatePDE_iff
#print axioms collarCKNativeExistenceUniqueGeometric
#print axioms collarCKOriginalExistenceUniqueGerm
#print axioms collarCKOriginalExistenceUnique
end GlobalEmbedding.Paper
