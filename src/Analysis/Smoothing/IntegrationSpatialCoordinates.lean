import Smoothing.ParameterSpatialPackets
import Smoothing.ParameterJetIdentities
import GlobalEmbedding.Offline.ModelCoordinateNorms
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Original spatial-first coordinates for the genuine joint spatial jet

The native product is parameter × source, whereas the original coordinate
convention is source coordinates followed by parameter coordinates.  This file
keeps that permutation explicit.  Both the native first/second source derivatives
and the literal ordered spatial coordinate derivatives refer to the same map.
No pure parameter derivative is added to the base spatial two-jet.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Filter Set Function
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation

/-- Original coordinate order: source first, then parameters. -/
def sourceFirstCoordinatesLinear (n d : ℕ) :
    ((Fin d → ℝ) × (Fin n → ℝ)) ≃ₗ[ℝ] (Fin (n+d) → ℝ) where
  toFun z := Fin.append z.2 z.1
  invFun z := (fun j => z (Fin.natAdd n j), fun i => z (Fin.castAdd d i))
  left_inv := by intro z; ext <;> simp
  right_inv := by
    intro z
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp
  map_add' := by
    intro z w
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp
  map_smul' := by
    intro r z
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp

/-- The actual finite-dimensional model equivalence, retaining its operator
norm whenever it occurs in a derivative estimate. -/
def sourceFirstCoordinates (n d : ℕ) :
    ((Fin d → ℝ) × (Fin n → ℝ)) ≃L[ℝ] (Fin (n+d) → ℝ) :=
  (sourceFirstCoordinatesLinear n d).toContinuousLinearEquiv

@[simp] theorem sourceFirstCoordinates_apply_spatial (n d : ℕ)
    (z : (Fin d → ℝ) × (Fin n → ℝ)) (i : Fin n) :
    sourceFirstCoordinates n d z (Fin.castAdd d i) = z.2 i := by
  simp [sourceFirstCoordinates, sourceFirstCoordinatesLinear]

@[simp] theorem sourceFirstCoordinates_apply_parameter (n d : ℕ)
    (z : (Fin d → ℝ) × (Fin n → ℝ)) (i : Fin d) :
    sourceFirstCoordinates n d z (Fin.natAdd n i) = z.1 i := by
  simp [sourceFirstCoordinates, sourceFirstCoordinatesLinear]

@[simp] theorem sourceFirstCoordinates_symm_apply (n d : ℕ) (z : Fin (n+d) → ℝ) :
    (sourceFirstCoordinates n d).symm z =
      (fun j => z (Fin.natAdd n j), fun i => z (Fin.castAdd d i)) := rfl

/-- A native spatial basis direction has exactly zero parameter components. -/
theorem sourceFirstCoordinates_spatial_single (n d : ℕ) (i : Fin n) :
    sourceFirstCoordinates n d (0, Pi.single i (1 : ℝ)) =
      Pi.single (Fin.castAdd d i) 1 := by
  ext j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · simp [Pi.single_apply, Fin.castAdd_inj]
  · have hne : Fin.natAdd n b ≠ Fin.castAdd d i := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    simp [Pi.single_apply, hne]

/-- Three canonical spatial words used to reconstruct native derivative maps. -/
def spatialWordZero (n : ℕ) : ParameterSpatialWord n := ⟨0, Fin.elim0⟩
def spatialWordOne {n : ℕ} (i : Fin n) : ParameterSpatialWord n := ⟨1, fun _ => i⟩
def spatialWordTwo {n : ℕ} (i j : Fin n) : ParameterSpatialWord n :=
  ⟨2, fun a => if a.val = 0 then i else j⟩

variable {n d q : ℕ}

/-- Slice maps are the same original map composed with the actual affine
spatial inclusion after source-first coordinate conversion. -/
theorem native_spatial_first_source_coordinates
    {u : (Fin (n+d) → ℝ) → Fin q → ℝ}
    {z : (Fin d → ℝ) × (Fin n → ℝ)}
    (hu : DifferentiableAt ℝ u (sourceFirstCoordinates n d z)) :
    fderiv ℝ (fun x => u (sourceFirstCoordinates n d (z.1,x))) z.2 =
      (fderiv ℝ u (sourceFirstCoordinates n d z)).comp
        ((sourceFirstCoordinates n d).toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin n → ℝ))) := by
  exact (hu.hasFDerivAt.comp z.2
    ((sourceFirstCoordinates n d).hasFDerivAt.comp z.2
      (hasFDerivAt_prodMk_right z.1 z.2))).fderiv

/-- A literal first spatial packet entry is the corresponding genuine native
slice derivative, with source-first flattening made explicit. -/
theorem parameterSpatialJet_one_native
    {u : (Fin (n+d) → ℝ) → Fin q → ℝ}
    {z : (Fin d → ℝ) × (Fin n → ℝ)}
    (hu : DifferentiableAt ℝ u (sourceFirstCoordinates n d z)) (i : Fin n) :
    parameterSpatialJet u (spatialWordOne i) (sourceFirstCoordinates n d z) =
      (spatialNativeJet (u ∘ sourceFirstCoordinates n d) z).2.1 (Pi.single i 1) := by
  rw [show (spatialNativeJet (u ∘ sourceFirstCoordinates n d) z).2.1 =
      fderiv ℝ (fun x => u (sourceFirstCoordinates n d (z.1,x))) z.2 from rfl,
    native_spatial_first_source_coordinates hu]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.inr_apply, sourceFirstCoordinates_spatial_single]
  change iteratedFDeriv ℝ 1 u _ (fun _ => Pi.single (Fin.castAdd d i) 1) = _
  exact iteratedFDeriv_one_apply _

/-- The exact spatial Hessian under the fixed source-first coordinate map.
The affine inclusion has zero Hessian; both derivatives remain native fderiv. -/
theorem native_spatial_second_source_coordinates
    {u : (Fin (n+d) → ℝ) → Fin q → ℝ} {O : Set (Fin (n+d) → ℝ)}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    {z : (Fin d → ℝ) × (Fin n → ℝ)} (hz : sourceFirstCoordinates n d z ∈ O)
    (v w : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (fun x => u (sourceFirstCoordinates n d (z.1,x)))) z.2 v w =
      fderiv ℝ (fderiv ℝ u) (sourceFirstCoordinates n d z)
        (sourceFirstCoordinates n d (0,v)) (sourceFirstCoordinates n d (0,w)) := by
  let a : (Fin n → ℝ) → (Fin (n+d) → ℝ) := fun x => sourceFirstCoordinates n d (z.1,x)
  let L : (Fin n → ℝ) →L[ℝ] (Fin (n+d) → ℝ) :=
    (sourceFirstCoordinates n d).toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin n → ℝ))
  let T := (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n+d) → ℝ) (Fin q → ℝ)).flip L
  have ha (x : Fin n → ℝ) : HasFDerivAt a L x :=
    (sourceFirstCoordinates n d).hasFDerivAt.comp x (hasFDerivAt_prodMk_right z.1 x)
  have hOs : IsOpen (a ⁻¹' O) := hO.preimage
    ((sourceFirstCoordinates n d).continuous.comp (continuous_const.prodMk continuous_id))
  have he : fderiv ℝ (u ∘ a) =ᶠ[𝓝 z.2] (fun y => T (fderiv ℝ u (a y))) := by
    filter_upwards [hOs.mem_nhds hz] with y hy
    exact ((hu.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp) |>.hasFDerivAt.comp y (ha y)).fderiv
  have hdu := (hu.fderiv_of_isOpen hO (m := ∞) (by simp)).contDiffAt (hO.mem_nhds hz)
  have hd := T.hasFDerivAt.comp z.2
    ((hdu.differentiableAt (by simp)).hasFDerivAt.comp z.2 (ha z.2))
  change HasFDerivAt (fun y => T (fderiv ℝ u (a y))) _ z.2 at hd
  change fderiv ℝ (fderiv ℝ (u ∘ a)) z.2 v w = _
  rw [he.fderiv_eq, hd.fderiv]
  rfl

/-- The literal ordered second spatial packet entry agrees with the actual
native spatial Hessian in the original chart. -/
theorem parameterSpatialJet_two_native
    {u : (Fin (n+d) → ℝ) → Fin q → ℝ} {O : Set (Fin (n+d) → ℝ)}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    {z : (Fin d → ℝ) × (Fin n → ℝ)} (hz : sourceFirstCoordinates n d z ∈ O)
    (i j : Fin n) :
    parameterSpatialJet u (spatialWordTwo i j) (sourceFirstCoordinates n d z) =
      (spatialNativeJet (u ∘ sourceFirstCoordinates n d) z).2.2 (Pi.single i 1) (Pi.single j 1) := by
  change iteratedFDeriv ℝ 2 u _
    (fun a : Fin 2 => Pi.single (Fin.castAdd d (if a.val = 0 then i else j)) 1) =
    fderiv ℝ (fderiv ℝ (fun x => u (sourceFirstCoordinates n d (z.1,x)))) z.2 _ _
  rw [native_spatial_second_source_coordinates hO hu hz,
    sourceFirstCoordinates_spatial_single, sourceFirstCoordinates_spatial_single]
  rw [iteratedFDeriv_two_apply]
  simp

/-- The value entry carries no derivatives in either the source or parameter. -/
theorem parameterSpatialJet_zero_native
    (u : (Fin (n+d) → ℝ) → Fin q → ℝ) (z : (Fin d → ℝ) × (Fin n → ℝ)) :
    parameterSpatialJet u (spatialWordZero n) (sourceFirstCoordinates n d z) =
      (spatialNativeJet (u ∘ sourceFirstCoordinates n d) z).1 := by
  change iteratedFDeriv ℝ 0 u _ _ = u _
  exact iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := u) (x := sourceFirstCoordinates n d z) _

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceFirstCoordinates_spatial_single
#print axioms GlobalEmbedding.Continuation.parameterSpatialJet_one_native
#print axioms GlobalEmbedding.Continuation.parameterSpatialJet_two_native
