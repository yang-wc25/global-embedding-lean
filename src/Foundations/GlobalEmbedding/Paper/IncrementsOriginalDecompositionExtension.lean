import GlobalEmbedding.Paper.IncrementsOriginalDecompositionInputs
import GlobalEmbedding.Paper.IncrementsPositiveDecompositionLinearExtension
import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.Topology.Algebra.Module.Basic

/-!
# SAME original symmetric-fiber identification and decomposition extension

Source: main.tex594–601,638–672. Normal-import the formally accepted actual
native input definitions and positive-decomposition extension. Only the SAME
bilinear forms are identified with their native equalizer; all tensor values
remain unchanged. No norm, basis, alternate carrier or final result field is
introduced. Uniform reserve, original coordinate topology equivalence and
chosen-phase conditioning remain separate original input/proof obligations.
DAG: increments-original-symmetric-fiber-extension. Exclusive worker W3.
-/

noncomputable section
open Manifold
open scoped BigOperators

namespace GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- Use the native pointwise additive group coherently on the SAME form space.
No carrier or operation changes; this names the existing LinearMap instance so
native equalizer/module constructions share its additive-monoid projection.
Source: original real symmetric-fiber identification. -/
local instance incrementsOriginalSymmetricRawAddCommGroup (x : M) :
    AddCommGroup (LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :=
  LinearMap.addCommGroup

/-- The SAME native symmetric tensor subtype is the native equalizer of flip and identity.
This only packages the native isSymm_iff_flip equivalence; underlying forms and
all point evaluations stay literally unchanged. Source: original symmetric fiber. -/
def incrementsOriginalSymmetricFiberEqLocusEquiv (x : M) :
    {A : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) //
      A.IsSymm} ≃
    LinearMap.eqLocus (LinearMap.BilinForm.flipHom (R := ℝ)
      (M := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toLinearMap
      (LinearMap.id :
        LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) →ₗ[ℝ]
          LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :=
  Equiv.subtypeEquivRight fun A ↦ by
    rw [LinearMap.mem_eqLocus]
    exact LinearMap.BilinForm.isSymm_iff_flip

/-- The SAME point-evaluation topology on the native equalizer representation.
There is no new tensor norm, basis or carrier in the original input datum.
Source: original symmetric-fiber topology, represented by its exact native equalizer. -/
@[instance_reducible]
def incrementsOriginalSymmetricEqLocusTopology (x : M) :
    TopologicalSpace (LinearMap.eqLocus (LinearMap.BilinForm.flipHom (R := ℝ)
      (M := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toLinearMap
      (LinearMap.id :
        LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) →ₗ[ℝ]
          LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))) :=
  TopologicalSpace.induced (fun A ↦ fun v w ↦ A.val v w) inferInstance

/-- The literal same-form identification is a homeomorphism for the SAME
point-evaluation topologies, by native induced-topology continuity in both
ways. Source: original open symmetric neighborhood, not all bilinear forms. -/
def incrementsOriginalSymmetricFiberEqLocusHomeomorph (x : M) :
    let _ := incrementsOriginalSymmetricFiberTopology (n := n) x
    let _ := incrementsOriginalSymmetricEqLocusTopology (n := n) x
    {A : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) //
      A.IsSymm} ≃ₜ
    LinearMap.eqLocus (LinearMap.BilinForm.flipHom (R := ℝ)
      (M := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toLinearMap
      (LinearMap.id :
        LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) →ₗ[ℝ]
          LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) := by
  let _ := incrementsOriginalSymmetricFiberTopology (n := n) x
  let _ := incrementsOriginalSymmetricEqLocusTopology (n := n) x
  exact
    { toEquiv := incrementsOriginalSymmetricFiberEqLocusEquiv x
      continuous_toFun := continuous_induced_rng.mpr continuous_induced_dom
      continuous_invFun := continuous_induced_rng.mpr continuous_induced_dom }

/-- The original symmetric fiber, in its native same-form equalizer representation,
has continuous addition and real scalar multiplication in the SAME evaluation
topology. Reuse native induced-module theorems, without a norm or quantitative
hypothesis. Source: original linear tensor decomposition, main.tex594–598. -/
theorem incrementsOriginal_symmetricEqLocus_continuousModule (x : M) :
    let _ := incrementsOriginalSymmetricEqLocusTopology (n := n) x
    ContinuousAdd (LinearMap.eqLocus (LinearMap.BilinForm.flipHom (R := ℝ)
      (M := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toLinearMap
      (LinearMap.id :
        LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) →ₗ[ℝ]
          LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))) ∧
    ContinuousSMul ℝ (LinearMap.eqLocus (LinearMap.BilinForm.flipHom (R := ℝ)
      (M := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toLinearMap
      (LinearMap.id :
        LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) →ₗ[ℝ]
          LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))) := by
  let K := LinearMap.eqLocus (LinearMap.BilinForm.flipHom (R := ℝ)
      (M := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toLinearMap
    (LinearMap.id :
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) →ₗ[ℝ]
        LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
  let ev : K →ₗ[ℝ]
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x → ℝ :=
    { toFun := fun A v w ↦ A.val v w
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact ⟨continuousAdd_induced ev.toAddMonoidHom, continuousSMul_induced ev⟩

end GlobalEmbedding.Paper

namespace GlobalEmbedding.Paper

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]

attribute [local instance] incrementsOriginalSymmetricRawAddCommGroup

/-- The actual ORIGINAL given tensor decomposition extends on the SAME native
symmetric fiber. The first conclusion is its linear identity everywhere; the
second is the SAME sqrt formula on actual nonnegative arguments at nonzero
cutoffs. Use the native equalizer only inside the proof, the exact same-form
homeomorphism, and the ACCEPTED linear-extension provider. No new final bound,
carrier or norm is assumed. Source: original positive-reserve checks659–662. -/
theorem incrementsOriginal_decomposition_extension
    (D : IncrementsOriginalNativeData n d N M P)
    (hD : IncrementsOriginalQualitativeDecompositionInputs D)
    (p : P) (hp : p ∈ D.parameterOpen) (x : M) :
    (∀ A : {A : LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) // A.IsSymm},
      A.val = ∑ ν, (D.cutoff ν (p, x) ^ 2 * D.linearArgument ν p x A.val) •
        incrementsOriginalPhaseSquare D ν p x) ∧
    (∀ A : {A : LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) // A.IsSymm},
      (∀ ν, D.cutoff ν (p, x) ≠ 0 → 0 ≤ D.linearArgument ν p x A.val) →
        A.val = incrementsOriginalDecompositionTensor D p x A.val) := by
  let K := LinearMap.eqLocus (LinearMap.BilinForm.flipHom (R := ℝ)
    (M := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toLinearMap
    (LinearMap.id : Module.End ℝ
      (LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)))
  let _ : AddCommGroup K := Submodule.addCommGroup K
  let _ := incrementsOriginalSymmetricFiberTopology (n := n) x
  let _ : TopologicalSpace K := incrementsOriginalSymmetricEqLocusTopology (n := n) x
  have hcont := incrementsOriginal_symmetricEqLocus_continuousModule (n := n) x
  let _ : ContinuousAdd K := hcont.1
  let _ : ContinuousSMul ℝ K := hcont.2
  let e := incrementsOriginalSymmetricFiberEqLocusEquiv (n := n) x
  let L (ν : Fin D.primaryCount) : K →ₗ[ℝ] ℝ :=
    { toFun := fun A ↦ D.linearArgument ν p x A.val
      map_add' := fun A B ↦ (D.linearArgument ν p x).map_add A.val B.val
      map_smul' := fun r A ↦ (D.linearArgument ν p x).map_smul r A.val }
  let chi (ν : Fin D.primaryCount) := D.cutoff ν (p, x)
  let Q (ν : Fin D.primaryCount) : K :=
    ⟨incrementsOriginalPhaseSquare D ν p x,
      LinearMap.BilinForm.isSymm_iff_flip.mp ⟨fun v w ↦ mul_comm _ _⟩⟩
  have hL (ν : Fin D.primaryCount) (A : K) : L ν A = D.linearArgument ν p x A.val := rfl
  have hQ (ν : Fin D.primaryCount) : (Q ν).val = incrementsOriginalPhaseSquare D ν p x := rfl
  have heval (A) : (e A).val = A.val := rfl
  let U : Set K := e.symm ⁻¹' D.tensorNeighborhood p x
  have hU : IsOpen U := (hD.fiber_open p hp x).preimage
    (incrementsOriginalSymmetricFiberEqLocusHomeomorph (n := n) x).symm.continuous
  have hne : U.Nonempty :=
    ⟨e ⟨D.H p x, hD.H_symmetric p hp x⟩, by
      simpa only [U, Set.mem_preimage, e.symm_apply_apply] using hD.H_mem p hp x⟩
  have hpos : ∀ A ∈ U, ∀ ν, chi ν ≠ 0 → 0 ≤ L ν A := by
    intro A hA ν hc
    exact (hD.argument_positive p hp x ν hc (e.symm A) hA).le
  have hdec : ∀ A ∈ U, A = ∑ ν, (chi ν * Real.sqrt (L ν A)) ^ 2 • Q ν := by
    intro A hA
    apply Subtype.ext
    have hd := hD.decomposition p hp x (e.symm A) hA
    change A.val = ∑ ν,
      (D.cutoff ν (p, x) * Real.sqrt (D.linearArgument ν p x A.val)) ^ 2 •
        incrementsOriginalPhaseSquare D ν p x at hd
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hL, hQ, chi] using hd
  have hlin : ∀ A : K, A = ∑ ν, (chi ν ^ 2 * L ν A) • Q ν :=
    increments_positive_decomposition_linear_extension (E := K) L chi Q U hU hne hpos hdec
  constructor
  · intro A
    have h := congrArg Subtype.val (hlin (e A))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hL, hQ, heval, chi] using h
  · intro A hA
    have h := increments_positive_decomposition_on_reserve L chi Q U hU hne hpos hdec
      (e A) (by
        intro ν hν
        simpa only [hL, heval] using hA ν hν)
    have hv := congrArg Subtype.val h
    change A.val = ∑ ν,
      (D.cutoff ν (p, x) * Real.sqrt (D.linearArgument ν p x A.val)) ^ 2 •
        incrementsOriginalPhaseSquare D ν p x
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hL, hQ, heval, chi] using hv

end GlobalEmbedding.Paper
