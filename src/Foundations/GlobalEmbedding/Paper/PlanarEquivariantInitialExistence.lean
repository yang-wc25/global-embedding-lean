import GlobalEmbedding.Paper.PlanarProjectiveMapLift
import GlobalEmbedding.Paper.PlanarProjectiveHopfCovector
import GlobalEmbedding.Paper.OpenAmpleMapExistence
import GlobalEmbedding.Paper.FramedPartialImmersionFormal
import GlobalEmbedding.Paper.PlanarProjectiveMapLiftDerivative

/-!
# The genuine initial reflection-equivariant Hopf map

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines 256–260.
The maps reduction uses the actual projective rank-one projector. Principal slices below
use the real upstream `DualPair.update`, rather than an independent slice operation.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- The actual normalized covector gives a zero-valued formal derivative into the first
coordinate of the target. Its target tangent is identified canonically at the actual zero. -/
def planarInitialFormalDerivative {C : ℕ} [Fact (0 < C)] (x : PlanarRealProjective C) :
    TangentSpace (planarHopfModel C) x →L[ℝ]
      TangentSpace 𝓘(ℝ, ℝ × PlanarHopfAmbient C) (0 : ℝ × PlanarHopfAmbient C) :=
  (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ × PlanarHopfAmbient C)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inl ℝ ℝ (PlanarHopfAmbient C)).comp (planarProjectiveHopfCovector x))

/-- The actual zero-value formal jet is native smooth.

Proof: the actual cotangent section is native smooth. In source tangent coordinates its
coefficient map is therefore native smooth. Postcompose with the fixed continuous linear
inclusion into the first target coordinate. The actual target is zero in every fiber, so its
normed tangent trivialization is the canonical identity; source tangent coordinates are the
same ones as for the cotangent section. The genuine one-jet smoothness criterion now applies.
Source: the actual zero section and beta tensor e-one formal solution in `lem:planar`. -/
theorem planarInitialFormalJet_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C)
      (((planarHopfModel C).prod 𝓘(ℝ, ℝ × PlanarHopfAmbient C)).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * C - 1)) →L[ℝ] ℝ × PlanarHopfAmbient C)) ∞
      (fun x : PlanarRealProjective C ↦
        OneJetBundle.mk x (0 : ℝ × PlanarHopfAmbient C) (planarInitialFormalDerivative x)) := by
  exact contMDiff_zeroJet_postcompose_smoothHom (planarProjectiveHopfCovectorSection C)
    (ContinuousLinearMap.inl ℝ ℝ (PlanarHopfAmbient C))

/-- The genuine smooth zero-valued formal one-jet section, using the proved native regularity. -/
def planarInitialFormalJet (C : ℕ) [Fact (0 < C)] :
    OneJetSec (planarHopfModel C) (PlanarRealProjective C)
      𝓘(ℝ, ℝ × PlanarHopfAmbient C) (ℝ × PlanarHopfAmbient C) where
  bs := fun _ ↦ 0
  ϕ := planarInitialFormalDerivative
  contMDiff' := planarInitialFormalJet_contMDiff C

/-- The actual smooth formal jet solves the actual native relation: its first derivative
coordinate is the actual beta(X)=1, so the literal projector pair cannot vanish.
Source: the formal zero section and beta tensor e-one in the original planar proof. -/
theorem planarInitialFormalJet_isSol (C : ℕ) [Fact (0 < C)] (x : PlanarRealProjective C) :
    planarInitialFormalJet C x ∈ planarInitialProjectiveRelation C := by
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  change planarProjectiveHopfCovector x (planarProjectiveHopfGenerator x) = 0 at hfirst
  rw [planarProjectiveHopfCovector_generator] at hfirst
  exact one_ne_zero hfirst

/-- A genuinely constructed smooth formal solution, with zero value and actual beta
derivative, to the true native projective maps relation. -/
def planarInitialFormalSolution (C : ℕ) [Fact (0 < C)] :
    FormalSol (planarInitialProjectiveRelation C) where
  toOneJetSec := planarInitialFormalJet C
  is_sol' := planarInitialFormalJet_isSol C

/-- The actual maps h-principle applied to the genuinely constructed formal solution produces
an ordinary smooth projective map satisfying the actual projector relation at its true jet.
No proposed map, formal solution, openness or ampleness is an input to this existence theorem.
Source: the initial nonvanishing equivariant-map existence step in `lem:planar`. -/
theorem planarInitialProjectiveMap_exists (C : ℕ) [Fact (0 < C)] :
    ∃ F : PlanarRealProjective C → ℝ × PlanarHopfAmbient C,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ × PlanarHopfAmbient C) ∞ F ∧
      ∀ x, oneJetExt (planarHopfModel C) 𝓘(ℝ, ℝ × PlanarHopfAmbient C) F x ∈
        planarInitialProjectiveRelation C :=
  openAmpleMap_exists_smooth_solution (planarInitialProjectiveRelation C)
    (planarInitialProjectiveRelation_isOpen C) (planarInitialProjectiveRelation_ample C)
    (planarInitialFormalSolution C)

/-- For every original Hopf sphere, a genuinely constructed smooth planar map has the original
antipodal reflection and nowhere-zero actual period-one Hopf derivative.

Proof: construct the actual beta-normalized zero-valued formal solution of the actual open
ample native projective relation. The accepted maps h-principle produces a genuine smooth
ordinary projective map satisfying the relation at its true first jet. Lift it by the actual
formula (a([z]),inner(w([z]),z)). Actual projection smoothness gives smoothness of the lift,
the genuine antipodal quotient gives reflection, and the proved actual projector derivative
identity converts relation nonvanishing into nonzero actual sphere Hopf derivative.
Source: the initial equivariant-g existence step in `lem:planar`, lines 258–260. -/
theorem planar_equivariant_initial_map (C : ℕ) (hC : 2 ≤ C) :
    letI : Fact (0 < C) := ⟨by omega⟩
    ∃ g : PlanarHopfSphere C → Planar,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ g ∧
      (∀ z, g (-z) = planarReflection (g z)) ∧
      ∀ z, orbitDeriv planarHopfFlow g z ≠ 0 := by
  let _ : Fact (0 < C) := ⟨by omega⟩
  obtain ⟨F, hF, hsol⟩ := planarInitialProjectiveMap_exists C
  exact ⟨planarProjectiveMapLift F, planarProjectiveMapLift_contMDiff F hF,
    planarProjectiveMapLift_reflection F, planarProjectiveMapLift_deriv_ne_zero F hF hsol⟩

#print axioms planarInitialFormalJet_contMDiff
#print axioms planarInitialFormalJet_isSol
#print axioms planarInitialFormalSolution
#print axioms planarInitialProjectiveMap_exists
#print axioms planar_equivariant_initial_map

end GlobalEmbedding.Paper
