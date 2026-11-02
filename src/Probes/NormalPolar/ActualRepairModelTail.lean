import NormalPolar.ActualRepairModelPartial

/-!
# Original mixed tail norms give actual parameter-response norms

The output is the original cumulative spatial Cj norm of a native parameter
column of the same actual map. The input is the original mixed (j,1) norm of
that map on its original sample set. The exact comparison constant is one:
there is no atlas-count factor, parameter dimension factor, or change of
parameter ball. Both zero-dimensional coordinate cases are retained.
-/

noncomputable section
open Set Filter GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
variable {n p q : ℕ}

/-- Exact identity of every original source partial of an actual parameter
response with the corresponding original mixed word. -/
theorem actualRepairModel_response_partial
    (f : (Fin (n+p) → ℝ) → Fin q → ℝ) (O : Set (Fin (n+p) → ℝ))
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (u : Fin p → ℝ) (Ox : Set (Fin n → ℝ)) (hOx : IsOpen Ox)
    (hsource : Ox ⊆ actualRepairModelSlice u O)
    (l : List (Fin n)) (a : Fin p) (c : Fin q) (x : Fin n → ℝ) (hx : x ∈ Ox) :
    paperCoordinatePartial l
      (fun y => (fderiv ℝ (fun v => f (sourceFirstCoordinates n p (v,y))) u
        (Pi.single a 1)) c) Ox x =
      paperCoordinatePartial (l.map (Fin.castAdd p) ++ [Fin.natAdd n a])
        (fun y => f y c) O (sourceFirstCoordinates n p (u,x)) := by
  let g := paperCoordinatePartial [Fin.natAdd n a] (fun y => f y c) O
  have hg : ContDiffOn ℝ ∞ g O := paperCoordinatePartial_smooth _ _ O hO
    ((contDiffOn_pi.mp hf) c)
  have heq : EqOn
      (fun y => (fderiv ℝ (fun v => f (sourceFirstCoordinates n p (v,y))) u
        (Pi.single a 1)) c)
      (fun y => g (sourceFirstCoordinates n p (u,y))) Ox := by
    intro y hy
    exact actualRepairModel_parameter_component f O hO hf u y (hsource hy) a c
  rw [paperCoordinatePartial_congr l heq hx]
  rw [actualRepairModel_partial_open_domain l _ hOx (actualRepairModelSlice_open u hO)
    x hx (hsource hx)]
  rw [actualRepairModel_source_partial g O hO hg u l x (hsource hx)]
  exact (congrFun (actualRepairModel_partial_append (l.map (Fin.castAdd p))
    [Fin.natAdd n a] (fun y => f y c) O) (sourceFirstCoordinates n p (u,x))).symm

/-- The literal actual parameter response is bounded in the original spatial
norm by the original mixed joint norm, with exact constant one and original
norm sample set retained. -/
theorem actualRepairModel_parameter_Cj_le_mixed
    (j : ℕ) (f : (Fin (n+p) → ℝ) → Fin q → ℝ)
    (O S : Set (Fin (n+p) → ℝ)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O)
    (u : Fin p → ℝ) (Ox Sx : Set (Fin n → ℝ)) (hOx : IsOpen Ox)
    (hsource : Ox ⊆ actualRepairModelSlice u O) (hSx : Sx ⊆ Ox)
    (hsample : ∀ x ∈ Sx, sourceFirstCoordinates n p (u,x) ∈ S)
    (a : Fin p) :
    paperCoordinateCj j
      (fun x => fderiv ℝ (fun v => f (sourceFirstCoordinates n p (v,x))) u
        (Pi.single a 1)) Ox Sx ≤
      paperMixedCoordinateCj (nx := n) (np := p) j 1 f O S := by
  refine iSup_le fun l => iSup_le fun x => iSup_le fun c => ?_
  rw [actualRepairModel_response_partial f O hO hf u Ox hOx hsource l.val a c x (hSx x.property)]
  simpa only [List.map_singleton] using
    paper_mixed_partial_le f O S l.val [a] l.property.2 (by simp)
      ⟨sourceFirstCoordinates n p (u,x),hsample x x.property⟩ c

/-- The same exact comparison over a finite atlas. The parameter remains one
fixed actual coordinate value for all source charts. -/
theorem actualRepairModel_parameter_atlasCj_le_mixed
    {ι : Type*} [Fintype ι] (j : ℕ)
    (f : ι → (Fin (n+p) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+p) → ℝ)) (hO : ∀ i, IsOpen (O i))
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (u : Fin p → ℝ) (Ox Sx : ι → Set (Fin n → ℝ)) (hOx : ∀ i, IsOpen (Ox i))
    (hsource : ∀ i, Ox i ⊆ actualRepairModelSlice u (O i)) (hSx : ∀ i, Sx i ⊆ Ox i)
    (hsample : ∀ i x, x ∈ Sx i → sourceFirstCoordinates n p (u,x) ∈ S i)
    (a : Fin p) :
    paperAtlasCj j
      (fun i x => fderiv ℝ (fun v => f i (sourceFirstCoordinates n p (v,x))) u
        (Pi.single a 1)) Ox Sx ≤
      ⨆ i, paperMixedCoordinateCj (nx := n) (np := p) j 1 (f i) (O i) (S i) := by
  apply iSup_le
  intro i
  exact (actualRepairModel_parameter_Cj_le_mixed j (f i) (O i) (S i) (hO i) (hf i)
    u (Ox i) (Sx i) (hOx i) (hsource i) (hSx i) (hsample i) a).trans
      (le_iSup (fun k => paperMixedCoordinateCj (nx := n) (np := p) j 1 (f k) (O k) (S k)) i)

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_response_partial
#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_parameter_Cj_le_mixed
#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_parameter_atlasCj_le_mixed
