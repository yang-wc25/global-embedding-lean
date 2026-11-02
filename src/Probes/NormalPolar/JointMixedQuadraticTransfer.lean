import NormalPolar.ActualRepairModelFirstDefectQuadraticTransfer

/-! Covariance of the actual signed forcing for an arbitrary joint parameter
space. Spatial derivatives see a fixed parameter slice, so the already proved
zero-dimensional slice theorem applies literally. No joint regularity is
assumed to establish this algebraic coordinate identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
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

theorem jointMixed_quadratic_forcing_chart_transfer
    (phase : Label → Ep × M → ℝ) (R Q : Label → Ep × M → V) (tau : ℝ)
    (e1 e2 : OpenPartialHomeomorph M D)
    (he1 : e1 ∈ maximalAtlas IM ∞ M) (he2 : e2 ∈ maximalAtlas IM ∞ M)
    (z : X) (hz : z.2 ∈ e2.target) (h12 : e2.symm z.2 ∈ e1.source)
    (nu mu : Label) (q : Fin 4) :
    let Hobs := fun (e : OpenPartialHomeomorph M D) (y : X) =>
      incrementsSecondaryQuadraticForcing (fun l b x => phase l (b,e.symm x)) tau
        (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
        (fun l b (_ : Unit) x => R l (b,e.symm x))
        (fun l b (_ : Unit) x => Q l (b,e.symm x))
        (fun i _ => EuclideanSpace.single i 1) nu mu q y
    let Phi := fun y : X => (y.1,e1 (e2.symm y.2))
    let J := fderiv ℝ (e1 ∘ e2.symm) z.2
    actualRealTensorAssembly (Hobs e2 z) =
      (actualRealTensorAssembly (Hobs e1 (Phi z))).bilinearComp J J ∧
    actualImaginaryTensorAssembly (Hobs e2 z) =
      (actualImaginaryTensorAssembly (Hobs e1 (Phi z))).bilinearComp J J := by
  exact actualRepairModelFirstDefect_quadratic_forcing_chart_transfer (d := 0)
    (fun l y => phase l (z.1,y.2)) (fun l y => R l (z.1,y.2))
    (fun l y => Q l (z.1,y.2)) tau e1 e2 he1 he2 (0,z.2) hz h12 nu mu q

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_quadratic_forcing_chart_transfer
