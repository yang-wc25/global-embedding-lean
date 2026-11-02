import Smoothing.IntegrationSpatialCoordinates
import GlobalEmbedding.Offline.ProbeTailEstimates

/-!
# Actual source slices of the original joint-coordinate tail

This file identifies the literal source partials of a fixed parameter slice
with the source-first words of the same joint map. The differentiation domain
is the actual open slice of the original domain; the norm sampling set is
kept separate. No extension beyond that open domain is assumed.
-/

noncomputable section
open Set Filter GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar

variable {n p q : ℕ}

/-- The actual source coordinate slice of the original open joint domain. -/
def actualRepairModelSlice (u : Fin p → ℝ) (O : Set (Fin (n+p) → ℝ)) :
    Set (Fin n → ℝ) := (fun x => sourceFirstCoordinates n p (u,x)) ⁻¹' O

theorem actualRepairModelSlice_open (u : Fin p → ℝ)
    {O : Set (Fin (n+p) → ℝ)} (hO : IsOpen O) :
    IsOpen (actualRepairModelSlice u O) :=
  hO.preimage ((sourceFirstCoordinates n p).continuous.comp
    (continuous_const.prodMk continuous_id))

/-- Every native source partial uses the same actual joint map and the same
open domain. The parameter is fixed only after the joint field is supplied. -/
theorem actualRepairModel_source_partial
    (f : (Fin (n+p) → ℝ) → ℝ) (O : Set (Fin (n+p) → ℝ))
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (u : Fin p → ℝ) (l : List (Fin n)) :
    ∀ x ∈ actualRepairModelSlice u O,
      paperCoordinatePartial l (fun y => f (sourceFirstCoordinates n p (u,y)))
        (actualRepairModelSlice u O) x =
      paperCoordinatePartial (l.map (Fin.castAdd p)) f O
        (sourceFirstCoordinates n p (u,x)) := by
  induction l with
  | nil => intro x hx; rfl
  | cons i l ih =>
    intro x hx
    rw [paperCoordinatePartial]
    rw [lineDerivWithin_congr' (fun y hy => ih y hy) hx]
    rw [lineDerivWithin_of_isOpen (actualRepairModelSlice_open u hO) hx]
    have hpartial := paperCoordinatePartial_smooth (l.map (Fin.castAdd p)) f O hO hf
    have hd := (hpartial.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hslice := hd.hasFDerivAt.comp x
      ((sourceFirstCoordinates n p).hasFDerivAt.comp x (hasFDerivAt_prodMk_right u x))
    simp only [Function.comp_def] at hslice
    rw [hslice.differentiableAt.lineDeriv_eq_fderiv, hslice.fderiv]
    simp only [List.map_cons, paperCoordinatePartial]
    rw [lineDerivWithin_of_isOpen hO hx, hd.lineDeriv_eq_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearMap.inr_apply, sourceFirstCoordinates_spatial_single]

/-- A paired parameter basis vector is the corresponding second-block
coordinate direction, with no Euclidean/sup norm conversion. -/
theorem sourceFirstCoordinates_parameter_single (a : Fin p) :
    sourceFirstCoordinates n p (Pi.single a (1 : ℝ), 0) =
      Pi.single (Fin.natAdd n a) 1 := by
  ext j
  refine Fin.addCases (fun b => ?_) (fun b => ?_) j
  · have hne : Fin.castAdd p b ≠ Fin.natAdd n a := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    simp [Pi.single_apply, hne]
  · simp [Pi.single_apply, Fin.natAdd_inj]

/-- The actual parameter response of a component is the literal one-letter
parameter partial of that same joint field. -/
theorem actualRepairModel_parameter_component
    (f : (Fin (n+p) → ℝ) → Fin q → ℝ) (O : Set (Fin (n+p) → ℝ))
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (u : Fin p → ℝ) (x : Fin n → ℝ) (hx : x ∈ actualRepairModelSlice u O)
    (a : Fin p) (c : Fin q) :
    (fderiv ℝ (fun v => f (sourceFirstCoordinates n p (v,x))) u (Pi.single a 1)) c =
      paperCoordinatePartial [Fin.natAdd n a] (fun y => f y c) O
        (sourceFirstCoordinates n p (u,x)) := by
  have hd := (hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hcomp := hd.hasFDerivAt.comp u
    ((sourceFirstCoordinates n p).hasFDerivAt.comp u (hasFDerivAt_prodMk_left u x))
  simp only [Function.comp_def] at hcomp
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.inl_apply, sourceFirstCoordinates_parameter_single]
  let ev : (Fin q → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj c
  have hc := ev.hasFDerivAt.comp (sourceFirstCoordinates n p (u,x)) hd.hasFDerivAt
  change HasFDerivAt (fun y => f y c)
    (ev.comp (fderiv ℝ f (sourceFirstCoordinates n p (u,x))))
    (sourceFirstCoordinates n p (u,x)) at hc
  simp only [paperCoordinatePartial]
  rw [lineDerivWithin_of_isOpen hO hx, hc.differentiableAt.lineDeriv_eq_fderiv]
  exact (congrArg (fun L => L (Pi.single (Fin.natAdd n a) 1)) hc.fderiv).symm

/-- Actual coordinate partials on two open differentiation domains agree on
that intersection. Arbitrary values outside the domains play no role. -/
theorem actualRepairModel_partial_open_domain
    {k : ℕ} (l : List (Fin k)) (f : (Fin k → ℝ) → ℝ)
    {O O' : Set (Fin k → ℝ)} (hO : IsOpen O) (hO' : IsOpen O')
    (x : Fin k → ℝ) (hx : x ∈ O) (hx' : x ∈ O') :
    paperCoordinatePartial l f O x = paperCoordinatePartial l f O' x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    simp only [paperCoordinatePartial]
    rw [lineDerivWithin_of_isOpen hO hx, lineDerivWithin_of_isOpen hO' hx']
    have he : paperCoordinatePartial l f O =ᶠ[𝓝 x] paperCoordinatePartial l f O' := by
      filter_upwards [hO.mem_nhds hx, hO'.mem_nhds hx'] with y hy hy'
      exact ih y hy hy'
    exact he.lineDeriv_eq

/-- Concatenating genuine coordinate words means applying the outer word to
the genuine derivative field determined by the inner word. -/
theorem actualRepairModel_partial_append {k : ℕ}
    (l r : List (Fin k)) (f : (Fin k → ℝ) → ℝ) (O : Set (Fin k → ℝ)) :
    paperCoordinatePartial (l ++ r) f O =
      paperCoordinatePartial l (paperCoordinatePartial r f O) O := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    simp only [List.cons_append,paperCoordinatePartial,ih]

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_source_partial
#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_parameter_component
