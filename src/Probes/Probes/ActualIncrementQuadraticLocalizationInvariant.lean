import Probes.ActualIncrementQuadraticChartTransfer

/-! The actual secondary forcing is constructed once in a fixed host chart.
Its inverse-Jacobian localization agrees on every actual observation overlap
with the localization written in that observation chart. The same global
cutoff, signed record, delta and actual primary amplitudes occur on both sides. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-- The equality is on the actual observer/adapted target, precisely where the
same local h is consumed by the physical secondary mode. No covariance of an
independent forcing field or equality of chosen h-fields is an input. -/
theorem actual_original_quadratic_localization_observer_independent
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (length : ℕ) (tau delta : ℝ)
    (e1 e2 : OpenPartialHomeomorph M D)
    (he1 : ContMDiffOn I 𝓘(ℝ,D) ∞ e1 e1.source)
    (he1Inv : ContMDiffOn 𝓘(ℝ,D) I ∞ e1.symm e1.target)
    (he2 : ContMDiffOn I 𝓘(ℝ,D) ∞ e2 e2.source)
    (he2Inv : ContMDiffOn 𝓘(ℝ,D) I ∞ e2.symm e2.target)
    (a : OpenPartialHomeomorph (Ep × M) X)
    (hhost : ∀ w ∈ a.source, w.2 ∈ e1.source)
    (hsourceW : a.source ⊆ W)
    (hinv2 : ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod e2).symm.trans a).symm
      (((OpenPartialHomeomorph.refl Ep).prod e2).symm.trans a).target)
    (rho : Ep × M → ℝ) (nu mu : Λ) (q : Fin 4) :
    let b1 := (OpenPartialHomeomorph.refl Ep).prod e1
    let b2 := (OpenPartialHomeomorph.refl Ep).prod e2
    let Hobs := fun (e : OpenPartialHomeomorph M D) (y : X) =>
      incrementsSecondaryQuadraticForcing
        (fun l t x => g.phase l (t,e.symm x)) tau (fun _ _ _ _ => 1)
        (fun l t b x => delta • incrementsGlobalPrimaryExtension F hF g input length tau true l b (t,e.symm x))
        (fun l t b x => delta • incrementsGlobalPrimaryExtension F hF g input length tau false l b (t,e.symm x))
        (fun i _ => EuclideanSpace.single i 1) nu mu q y
    EqOn (actualSecondaryInverseForcing (b1.symm.trans a) (rho ∘ b1.symm)
        (fun y => actualRealTensorAssembly (Hobs e1 y)))
      (actualSecondaryInverseForcing (b2.symm.trans a) (rho ∘ b2.symm)
        (fun y => actualRealTensorAssembly (Hobs e2 y))) (b2.symm.trans a).target ∧
    EqOn (actualSecondaryInverseForcing (b1.symm.trans a) (rho ∘ b1.symm)
        (fun y => actualImaginaryTensorAssembly (Hobs e1 y)))
      (actualSecondaryInverseForcing (b2.symm.trans a) (rho ∘ b2.symm)
        (fun y => actualImaginaryTensorAssembly (Hobs e2 y))) (b2.symm.trans a).target := by
  intro b1 b2 Hobs
  let t1 := b1.symm.trans a
  let t2 := b2.symm.trans a
  have htarget (z : X) (hz : z ∈ t2.target) :
      z ∈ a.target ∧ (a.symm z).2 ∈ e2.source := by
    change z ∈ a.target ∧ a.symm z ∈ b2.source at hz
    exact ⟨hz.1,hz.2.2⟩
  have hinv (z : X) (hz : z ∈ t2.target) :
      actualJointSpatialJacobian t1.symm z =
      (fderiv ℝ (e1 ∘ e2.symm) (t2.symm z).2).comp
        (actualJointSpatialJacobian t2.symm z) := by
    let u : D → D := fun x => (t2.symm (z.1,x)).2
    have hu : DifferentiableAt ℝ u z.2 := by
      have hh := (hinv2.snd.contDiffAt (t2.open_target.mem_nhds hz)).comp z.2
        (contDiffAt_const.prodMk contDiffAt_id)
      exact hh.differentiableAt (by simp)
    have hp := htarget z hz
    have he2p : e2.symm (t2.symm z).2 = (a.symm z).2 := e2.left_inv hp.2
    have he1p : MDifferentiableAt I 𝓘(ℝ,D) e1 (e2.symm (t2.symm z).2) := by
      rw [he2p]
      exact (he1.contMDiffAt (e1.open_source.mem_nhds
        (hhost (a.symm z) (a.map_target hp.1)))).mdifferentiableAt (by simp)
    have he2p' : MDifferentiableAt 𝓘(ℝ,D) I e2.symm (t2.symm z).2 :=
      (he2Inv.contMDiffAt (e2.open_target.mem_nhds (e2.map_source hp.2))).mdifferentiableAt (by simp)
    have houter : DifferentiableAt ℝ (e1 ∘ e2.symm) (u z.2) :=
      (he1p.comp _ he2p').differentiableAt
    have heq : (fun x : D => (t1.symm (z.1,x)).2) =ᶠ[𝓝 z.2] (e1 ∘ e2.symm) ∘ u := by
      filter_upwards [(t2.open_target.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz]
        with x hx
      change e1 (a.symm (z.1,x)).2 = e1 (e2.symm (e2 (a.symm (z.1,x)).2))
      rw [e2.left_inv (htarget (z.1,x) hx).2]
    exact heq.fderiv_eq.trans (fderiv_comp z.2 houter hu)
  have hchannels (z : X) (hz : z ∈ t2.target) :
      actualSecondaryInverseForcing t1 (rho ∘ b1.symm)
          (fun y => actualRealTensorAssembly (Hobs e1 y)) z =
        actualSecondaryInverseForcing t2 (rho ∘ b2.symm)
          (fun y => actualRealTensorAssembly (Hobs e2 y)) z ∧
      actualSecondaryInverseForcing t1 (rho ∘ b1.symm)
          (fun y => actualImaginaryTensorAssembly (Hobs e1 y)) z =
        actualSecondaryInverseForcing t2 (rho ∘ b2.symm)
          (fun y => actualImaginaryTensorAssembly (Hobs e2 y)) z := by
    have hp := htarget z hz
    have ha : a.symm z ∈ a.source := a.map_target hp.1
    have he1p : (a.symm z).2 ∈ e1.source := hhost _ ha
    have hpoint : (fun y : X => (y.1,e1 (e2.symm y.2))) (t2.symm z) = t1.symm z := by
      change ((a.symm z).1,e1 (e2.symm (e2 (a.symm z).2))) = ((a.symm z).1,e1 (a.symm z).2)
      rw [e2.left_inv hp.2]
    have hbase : ((t2.symm z).1,e2.symm (t2.symm z).2) = a.symm z := by
      change ((a.symm z).1,e2.symm (e2 (a.symm z).2)) = a.symm z
      rw [e2.left_inv hp.2]
    have hb2 : (t2.symm z).2 ∈ e2.target := e2.map_source hp.2
    have hb12 : e2.symm (t2.symm z).2 ∈ e1.source := by
      change e2.symm (e2 (a.symm z).2) ∈ e1.source
      rw [e2.left_inv hp.2]
      exact he1p
    have hbW : ((t2.symm z).1,e2.symm (t2.symm z).2) ∈ W := by
      rw [hbase]
      exact hsourceW ha
    have hc := actual_original_quadratic_forcing_chart_transfer F hF g input W primary h length tau delta
      e1 e2 he1 he1Inv he2 he2Inv (t2.symm z) hb2 hb12 hbW nu mu q
    change actualRealTensorAssembly (Hobs e2 (t2.symm z)) =
        (actualRealTensorAssembly (Hobs e1 ((fun y : X => (y.1,e1 (e2.symm y.2))) (t2.symm z)))).bilinearComp
          (fderiv ℝ (e1 ∘ e2.symm) (t2.symm z).2) (fderiv ℝ (e1 ∘ e2.symm) (t2.symm z).2) ∧
      actualImaginaryTensorAssembly (Hobs e2 (t2.symm z)) =
        (actualImaginaryTensorAssembly (Hobs e1 ((fun y : X => (y.1,e1 (e2.symm y.2))) (t2.symm z)))).bilinearComp
          (fderiv ℝ (e1 ∘ e2.symm) (t2.symm z).2) (fderiv ℝ (e1 ∘ e2.symm) (t2.symm z).2) at hc
    rw [hpoint] at hc
    have hcut1 : (rho ∘ b1.symm) (t1.symm z) = rho (a.symm z) := by
      change rho ((a.symm z).1,e1.symm (e1 (a.symm z).2)) = rho (a.symm z)
      rw [e1.left_inv he1p]
    have hcut2 : (rho ∘ b2.symm) (t2.symm z) = rho (a.symm z) := by
      change rho ((a.symm z).1,e2.symm (e2 (a.symm z).2)) = rho (a.symm z)
      rw [e2.left_inv hp.2]
    constructor
    · funext i j
      simp only [actualSecondaryInverseForcing,actualTensorBasisCoefficients,
        actualSecondaryInverseForcingTensor,hcut1,hcut2,hc.1,hinv z hz,
        smul_apply,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply]
    · funext i j
      simp only [actualSecondaryInverseForcing,actualTensorBasisCoefficients,
        actualSecondaryInverseForcingTensor,hcut1,hcut2,hc.2,hinv z hz,
        smul_apply,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply]
  exact ⟨fun z hz => (hchannels z hz).1,fun z hz => (hchannels z hz).2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_quadratic_localization_observer_independent
