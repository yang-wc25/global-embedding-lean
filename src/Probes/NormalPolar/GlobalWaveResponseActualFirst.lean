import NormalPolar.GlobalWaveResponseInitialSum

/-! The literal combined primary array is used in the first-map response.
Its input is allowed to be the genuine parameter-dependent finite mean
iterate. The secondary argument is the entire signed correction, with the
same original probe parameter. No identification of a later closed-state
record with this explicit map is assumed silently. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation GlobalEmbedding.Upgrade
variable {E H M Ep X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Params" => ProbeParameters r

private local instance actualFirstHessianSemi : SeminormedAddCommGroup (X →L[ℝ] X →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance actualFirstHessianNormed : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance actualFirstHessianSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

theorem globalWave_actual_first_native_responses
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I:=I) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
    (label : (Fin r × Bool) ↪ Fin p) (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D))
    (input : (Fin p → ℝ) → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (secondary : (Fin p → ℝ) → Ep × M → V) (reference : Ep × M → V)
    (e : X → Ep × M) (U : Set Params) (O : Set X) (hU : IsOpen U) (hO : IsOpen O)
    (hr : ContDiffOn ℝ ∞ (reference ∘ e) O)
    (hb : ContDiffOn ℝ ∞ (fun z : Params × X => delta • incrementsGlobalPrimaryWave F hF g
      (input (probeParameterEmbedding label z.1)) backgroundLength tau (e z.2)) (U ×ˢ O))
    (hp : ContDiffOn ℝ ∞ (fun z : Params × X => round4PrescribedGlobalWave label F hF c vf phase
      tau probeLength a (probeParameterEmbedding label z.1) (e z.2)) (U ×ˢ O))
    (hs : ContDiffOn ℝ ∞ (fun z : Params × X => secondary (probeParameterEmbedding label z.1) (e z.2)) (U ×ˢ O))
    (u : Params) (hu : u ∈ U) (x : X) (hx : x ∈ O) :
    let G := fun v y => reference (e y)+round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a (input (probeParameterEmbedding label v)) (probeParameterEmbedding label v) (e y)+
        secondary (probeParameterEmbedding label v) (e y)
    let B := fun v y => delta • incrementsGlobalPrimaryWave F hF g
      (input (probeParameterEmbedding label v)) backgroundLength tau (e y)
    let P := fun v y => round4PrescribedGlobalWave label F hF c vf phase tau probeLength a
      (probeParameterEmbedding label v) (e y)
    let S := fun v y => secondary (probeParameterEmbedding label v) (e y)
    (fderiv ℝ (fun v => G v x) u = fderiv ℝ (fun v => B v x) u+
      fderiv ℝ (fun v => P v x) u+fderiv ℝ (fun v => S v x) u) ∧
    (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (G v)) x) u =
      fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (B v)) x) u+
        fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (P v)) x) u+
          fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (S v)) x) u) := by
  intro G B P S
  have he : G = fun v y => (reference ∘ e) y+B v y+P v y+S v y := by
    funext v y
    dsimp only [G,B,P,S,Function.comp_apply]
    rw [round4ParameterProbeCombinedPrimary_eq]
    abel
  rw [he]
  exact globalWave_initial_sum_native_responses U O hU hO (reference ∘ e) B P S hr hb hp hs u hu x hx

/-- The reference G0 is fixed in the actual probe parameter. Both complete
background and complete secondary responses contribute to the first-state
error, together with the true prescribed-wave residual. -/
theorem globalWave_initial_sum_response_bounds
    {P Y X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set P) (O : Set X) (hU : IsOpen U) (hO : IsOpen O)
    (reference : X → Y) (background probe secondary : P → X → Y)
    (hr : ContDiffOn ℝ ∞ reference O)
    (hb : ContDiffOn ℝ ∞ (Function.uncurry background) (U ×ˢ O))
    (hp : ContDiffOn ℝ ∞ (Function.uncurry probe) (U ×ˢ O))
    (hs : ContDiffOn ℝ ∞ (Function.uncurry secondary) (U ×ˢ O))
    (u direction : P) (hu : u ∈ U) (x : X) (hx : x ∈ O)
    (valueTarget : Y) (hessianTarget : X →L[ℝ] X →L[ℝ] Y)
    (eBV ePV eSV eBH ePH eSH : ℝ)
    (hBV : ‖fderiv ℝ (fun v => background v x) u direction‖ ≤ eBV)
    (hPV : ‖fderiv ℝ (fun v => probe v x) u direction-valueTarget‖ ≤ ePV)
    (hSV : ‖fderiv ℝ (fun v => secondary v x) u direction‖ ≤ eSV)
    (hBH : ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (background v)) x) u direction‖ ≤ eBH)
    (hPH : ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (probe v)) x) u direction-hessianTarget‖ ≤ ePH)
    (hSH : ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (secondary v)) x) u direction‖ ≤ eSH) :
    let G := fun v y => reference y+background v y+probe v y+secondary v y
    ‖fderiv ℝ (fun v => G v x) u direction-valueTarget‖ ≤ eBV+ePV+eSV ∧
    ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (G v)) x) u direction-hessianTarget‖ ≤ eBH+ePH+eSH := by
  intro G
  have he := globalWave_initial_sum_native_responses U O hU hO reference background probe secondary
    hr hb hp hs u hu x hx
  rw [he.1,he.2]
  simp only [add_apply]
  exact ⟨globalWave_three_response_error_bound _ _ _ _ _ _ _ hBV hPV hSV,
    globalWave_three_response_error_bound (Y:=X →L[ℝ] X →L[ℝ] Y) _ _ _ _ _ _ _ hBH hPH hSH⟩

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_actual_first_native_responses
#print axioms GlobalEmbedding.NormalPolar.globalWave_initial_sum_response_bounds
