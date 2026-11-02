import NormalPolar.JointMixedQuadraticTransfer

/-! A same-data mixed forcing is selected once in its actual host chart. Its
true inverse-Jacobian localization agrees with every later original observer.
No new forcing is chosen and neither tensor slot is dropped. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {M Ep Label : Type*} {m N : ℕ}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem jointMixed_quadratic_localization_observer_independent
    (phase : Label → Ep × M → ℝ) (R Q : Label → Ep × M → V) (tau : ℝ)
    (e1 e2 : OpenPartialHomeomorph M D)
    (he1 : e1 ∈ maximalAtlas IM ∞ M) (he2 : e2 ∈ maximalAtlas IM ∞ M)
    (a : OpenPartialHomeomorph (Ep × M) X)
    (hhost : ∀ w ∈ a.source, w.2 ∈ e1.source)
    (hinv2 : ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod e2).symm.trans a).symm
      (((OpenPartialHomeomorph.refl Ep).prod e2).symm.trans a).target)
    (rho : Ep × M → ℝ) (nu mu : Label) (q : Fin 4) :
    let b1 := (OpenPartialHomeomorph.refl Ep).prod e1
    let b2 := (OpenPartialHomeomorph.refl Ep).prod e2
    let Hobs := fun (e : OpenPartialHomeomorph M D) (y : X) =>
      incrementsSecondaryQuadraticForcing (fun l b x => phase l (b,e.symm x)) tau
        (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
        (fun l b (_ : Unit) x => R l (b,e.symm x))
        (fun l b (_ : Unit) x => Q l (b,e.symm x))
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
    have he1p : MDifferentiableAt IM 𝓘(ℝ,D) e1 (e2.symm (t2.symm z).2) := by
      rw [he2p]
      exact ((contMDiffOn_of_mem_maximalAtlas he1).contMDiffAt (e1.open_source.mem_nhds
        (hhost (a.symm z) (a.map_target hp.1)))).mdifferentiableAt (by simp)
    have he2p' : MDifferentiableAt 𝓘(ℝ,D) IM e2.symm (t2.symm z).2 :=
      ((contMDiffOn_symm_of_mem_maximalAtlas he2).contMDiffAt (e2.open_target.mem_nhds (e2.map_source hp.2))).mdifferentiableAt (by simp)
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
    have hc := jointMixed_quadratic_forcing_chart_transfer phase R Q tau
      e1 e2 he1 he2 (t2.symm z) hb2 hb12 nu mu q
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
#print axioms GlobalEmbedding.Continuation.jointMixed_quadratic_localization_observer_independent

