import NormalPolar.GlobalWaveResponseBackgroundPhysical
import Probes.Round4ParameterProbeCombinedPrimary

/-! Exact response assembly for the complete first map. The fixed contracted
reference has zero probe response, while the full physical background,
complete prescribed wave, and complete secondary remain in the sum. This
module assembles already constructed component responses; it does not infer
that an arbitrary initial-state record equals this map. -/
noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {P X Y : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
private local instance initialSumHessianSemi : SeminormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance initialSumHessianNormed : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance initialSumHessianSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedSpace

theorem globalWave_native_hessian_add
    (f g : X → Y) (x : X) (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y+g y)) x =
      fderiv ℝ (fderiv ℝ f) x+fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun y => f y+g y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y+fderiv ℝ g y) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
    exact fderiv_fun_add (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_fun_add
    ((hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num))

/-- The actual contracted reference remains spatially nonconstant, but its
probe-parameter responses are exactly zero. -/
theorem globalWave_contracted_reference_parameter_zero
    (F₀ : X → Y) (t : ℝ) (u : P) (x : X) :
    fderiv ℝ (fun _ : P => Real.sqrt (1-t^(20:ℕ)) • F₀ x) u = 0 ∧
    fderiv ℝ (fun _ : P => fderiv ℝ (fderiv ℝ
      (fun y => Real.sqrt (1-t^(20:ℕ)) • F₀ y)) x) u = 0 := by
  simp

theorem globalWave_native_parameter_sum
    (reference : Y) (background probe secondary : P → Y) (u : P)
    (hb : DifferentiableAt ℝ background u) (hp : DifferentiableAt ℝ probe u)
    (hs : DifferentiableAt ℝ secondary u) :
    fderiv ℝ (fun v => reference+background v+probe v+secondary v) u =
      fderiv ℝ background u+fderiv ℝ probe u+fderiv ℝ secondary u := by
  have h := (((hasFDerivAt_const reference u).add hb.hasFDerivAt).add hp.hasFDerivAt).add hs.hasFDerivAt
  change fderiv ℝ ((fun _ : P => reference)+background+probe+secondary) u = _
  simpa only [zero_add] using h.fderiv

theorem globalWave_initial_sum_native_responses
    (U : Set P) (O : Set X) (hU : IsOpen U) (hO : IsOpen O)
    (reference : X → Y) (background probe secondary : P → X → Y)
    (hr : ContDiffOn ℝ ∞ reference O)
    (hb : ContDiffOn ℝ ∞ (Function.uncurry background) (U ×ˢ O))
    (hp : ContDiffOn ℝ ∞ (Function.uncurry probe) (U ×ˢ O))
    (hs : ContDiffOn ℝ ∞ (Function.uncurry secondary) (U ×ˢ O))
    (u : P) (hu : u ∈ U) (x : X) (hx : x ∈ O) :
    let G := fun v y => reference y+background v y+probe v y+secondary v y
    (fderiv ℝ (fun v => G v x) u =
      fderiv ℝ (fun v => background v x) u+fderiv ℝ (fun v => probe v x) u+
        fderiv ℝ (fun v => secondary v x) u) ∧
    (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (G v)) x) u =
      fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (background v)) x) u+
        fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (probe v)) x) u+
          fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (secondary v)) x) u) := by
  intro G
  have hprod := (hU.prod hO).mem_nhds (show (u,x) ∈ U ×ˢ O from ⟨hu,hx⟩)
  have hvalue (f : P → X → Y) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ O)) :
      DifferentiableAt ℝ (fun v => f v x) u :=
    ((hf.contDiffAt hprod).comp u (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  refine ⟨globalWave_native_parameter_sum _ _ _ _ u (hvalue _ hb) (hvalue _ hp) (hvalue _ hs),?_⟩
  have hspatial (f : P → X → Y) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ O))
      (v : P) (hv : v ∈ U) : ContDiffAt ℝ 2 (f v) x :=
    (((hf.contDiffAt ((hU.prod hO).mem_nhds ⟨hv,hx⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id))).of_le (by simp)
  have hH (f : P → X → Y) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ O)) :
      DifferentiableAt ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) x) u := by
    have hj := (incrementsJointSpatialJets_bridge (Function.uncurry f) (U ×ˢ O) (hU.prod hO) hf).2.2
    exact ((hj.contDiffAt hprod).comp u (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have he : (fun v => fderiv ℝ (fderiv ℝ (G v)) x) =ᶠ[𝓝 u]
      (fun v => fderiv ℝ (fderiv ℝ reference) x+
        fderiv ℝ (fderiv ℝ (background v)) x+fderiv ℝ (fderiv ℝ (probe v)) x+
          fderiv ℝ (fderiv ℝ (secondary v)) x) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    have hrx := (hr.contDiffAt (hO.mem_nhds hx)).of_le (show (2:ℕ∞ω) ≤ ∞ by simp)
    have hbx := hspatial _ hb v hv
    have hpx := hspatial _ hp v hv
    have hsx := hspatial _ hs v hv
    change fderiv ℝ (fderiv ℝ (fun y => (reference y+background v y+probe v y)+secondary v y)) x = _
    rw [globalWave_native_hessian_add _ _ _ ((hrx.add hbx).add hpx) hsx,
      globalWave_native_hessian_add _ _ _ (hrx.add hbx) hpx,
      globalWave_native_hessian_add _ _ _ hrx hbx]
  rw [he.fderiv_eq]
  exact globalWave_native_parameter_sum _ _ _ _ u (hH _ hb) (hH _ hp) (hH _ hs)

/-- The middle derivative is obtained from the same joint family. In
particular the sharp first spatial response does not follow by weakening
the Hessian response bound. -/
theorem globalWave_initial_sum_native_first
    (U : Set P) (O : Set X) (hU : IsOpen U) (hO : IsOpen O)
    (reference : X → Y) (background probe secondary : P → X → Y)
    (hr : ContDiffOn ℝ ∞ reference O)
    (hb : ContDiffOn ℝ ∞ (Function.uncurry background) (U ×ˢ O))
    (hp : ContDiffOn ℝ ∞ (Function.uncurry probe) (U ×ˢ O))
    (hs : ContDiffOn ℝ ∞ (Function.uncurry secondary) (U ×ˢ O))
    (u : P) (hu : u ∈ U) (x : X) (hx : x ∈ O) :
    let G := fun v y => reference y+background v y+probe v y+secondary v y
    fderiv ℝ (fun v => fderiv ℝ (G v) x) u =
      fderiv ℝ (fun v => fderiv ℝ (background v) x) u+
        fderiv ℝ (fun v => fderiv ℝ (probe v) x) u+
          fderiv ℝ (fun v => fderiv ℝ (secondary v) x) u := by
  intro G
  have hprod := (hU.prod hO).mem_nhds (show (u,x) ∈ U ×ˢ O from ⟨hu,hx⟩)
  have hspatial (f : P → X → Y) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ O))
      (v : P) (hv : v ∈ U) : DifferentiableAt ℝ (f v) x :=
    (((hf.contDiffAt ((hU.prod hO).mem_nhds ⟨hv,hx⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
  have hD (f : P → X → Y) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ O)) :
      DifferentiableAt ℝ (fun v => fderiv ℝ (f v) x) u := by
    have hj := (incrementsJointSpatialJets_bridge (Function.uncurry f) (U ×ˢ O) (hU.prod hO) hf).2.1
    exact ((hj.contDiffAt hprod).comp u (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have he : (fun v => fderiv ℝ (G v) x) =ᶠ[𝓝 u]
      (fun v => fderiv ℝ reference x+fderiv ℝ (background v) x+
        fderiv ℝ (probe v) x+fderiv ℝ (secondary v) x) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    have hrx := (hr.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hbx := hspatial _ hb v hv
    have hpx := hspatial _ hp v hv
    have hsx := hspatial _ hs v hv
    change fderiv ℝ (reference+background v+probe v+secondary v) x = _
    exact (((hrx.hasFDerivAt.add hbx.hasFDerivAt).add hpx.hasFDerivAt).add hsx.hasFDerivAt).fderiv
  rw [he.fderiv_eq]
  exact globalWave_native_parameter_sum _ _ _ _ u (hD _ hb) (hD _ hp) (hD _ hs)

/-- A fixed principal target belongs to the actual probe component; the
full background and secondary errors are both added explicitly. -/
theorem globalWave_three_response_error_bound
    (background probe secondary target : Y) (eb ep es : ℝ)
    (hb : ‖background‖ ≤ eb) (hp : ‖probe-target‖ ≤ ep) (hs : ‖secondary‖ ≤ es) :
    ‖background+probe+secondary-target‖ ≤ eb+ep+es := by
  have he : background+probe+secondary-target = (background+(probe-target))+secondary := by abel
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add hb hp)) hs)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_initial_sum_native_responses
#print axioms GlobalEmbedding.NormalPolar.globalWave_contracted_reference_parameter_zero

#print axioms GlobalEmbedding.NormalPolar.globalWave_initial_sum_native_first
