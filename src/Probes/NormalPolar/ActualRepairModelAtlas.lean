import NormalPolar.ActualRepairModelTail
import NormalPolar.NativeProbeValueTail

/-!
# Actual joint tail coordinates supply the original probe-atlas norm

A genuine coordinate identity for the one global family transfers the exact
mixed-norm estimate to the original probe Cj norm of its native parameter
column. The target Euclidean-coordinate map is commuted with the actual
derivative by its native chain rule, not by a false norm isometry.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {n N p : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

/-- The supplied original joint coordinates represent the same actual global
family on the original open parameter set. Its true parameter response then
has the original Cj bound, without an extra geometry or dimension factor. -/
theorem actualRepairModel_probeAtlasCj_le_mixed
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    {U : Set (Fin p → ℝ)} (hU : IsOpen U)
    (F : (Fin p → ℝ) → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ,Fin p → ℝ)).prod IM) 𝓘(ℝ,V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (f : Fin A.count → (Fin (n+p) → ℝ) → Fin N → ℝ)
    (O S : Fin A.count → Set (Fin (n+p) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (heq : ∀ i v, v ∈ U → ∀ x, x ∈ (EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target →
      f i (sourceFirstCoordinates n p (v,x)) =
        (EuclideanSpace.equiv (Fin N) ℝ) (F v ((A.chart i).symm
          ((EuclideanSpace.equiv (Fin n) ℝ).symm x))))
    (u : Fin p → ℝ) (hu : u ∈ U)
    (hsource : ∀ i, (EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target ⊆
      actualRepairModelSlice u (O i))
    (hsample : ∀ i x,
      x ∈ (EuclideanSpace.equiv (Fin n) ℝ) '' ((A.chart i) '' A.support i) →
      sourceFirstCoordinates n p (u,x) ∈ S i)
    (j : ℕ) (a : Fin p) :
    probeAtlasCj A j (fun x => fderiv ℝ (fun v => F v x) u (Pi.single a 1)) ≤
      ⨆ i, paperMixedCoordinateCj (nx := n) (np := p) j 1 (f i) (O i) (S i) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  let Ox := fun i => e '' (A.chart i).target
  let Sx := fun i => e '' ((A.chart i) '' A.support i)
  have hOx (i : Fin A.count) : IsOpen (Ox i) :=
    e.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSx (i : Fin A.count) : Sx i ⊆ Ox i := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨A.chart i y,(A.chart i).map_source (hA.support_subset i hy),rfl⟩
  have hcoord (i : Fin A.count) : EqOn
      (fun x => v (fderiv ℝ (fun w => F w ((A.chart i).symm (e.symm x))) u (Pi.single a 1)))
      (fun x => fderiv ℝ (fun w => f i (sourceFirstCoordinates n p (w,x))) u (Pi.single a 1))
      (Ox i) := by
    intro x hx
    let y := (A.chart i).symm (e.symm x)
    have hd := actual_parameter_value_differentiableAt_of_joint A hA hcover hU F hF u hu y
    have hchain := v.hasFDerivAt.comp u hd.hasFDerivAt
    simp only [Function.comp_def] at hchain
    have hevent : (fun w => f i (sourceFirstCoordinates n p (w,x))) =ᶠ[𝓝 u]
        (fun w => v (F w y)) := by
      filter_upwards [hU.mem_nhds hu] with w hw
      exact heq i w hw x hx
    change v (fderiv ℝ (fun w => F w y) u (Pi.single a 1)) =
      fderiv ℝ (fun w => f i (sourceFirstCoordinates n p (w,x))) u (Pi.single a 1)
    rw [hevent.fderiv_eq,hchain.fderiv]
    rfl
  have hnorm : probeAtlasCj A j
      (fun x => fderiv ℝ (fun w => F w x) u (Pi.single a 1)) =
      paperAtlasCj j (fun i x => fderiv ℝ
        (fun w => f i (sourceFirstCoordinates n p (w,x))) u (Pi.single a 1)) Ox Sx := by
    change paperAtlasCj j
      (fun i x => v (fderiv ℝ (fun w => F w ((A.chart i).symm (e.symm x))) u
        (Pi.single a 1))) Ox Sx = _
    unfold paperAtlasCj paperCoordinateCj
    apply iSup_congr
    intro i
    apply iSup_congr
    intro l
    apply iSup_congr
    intro x
    apply iSup_congr
    intro c
    congr 2
    exact paperCoordinatePartial_congr l.val (fun y hy => congrFun (hcoord i hy) c)
      (hSx i x.property)
  rw [hnorm]
  exact actualRepairModel_parameter_atlasCj_le_mixed j f O S hO hf u Ox Sx hOx
    hsource hSx hsample a

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_probeAtlasCj_le_mixed
