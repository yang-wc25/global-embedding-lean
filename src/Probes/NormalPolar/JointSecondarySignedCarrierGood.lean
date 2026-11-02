import NormalPolar.JointSecondarySignedCarrierNeighborhood
import NormalPolar.JointSecondarySignedSeed

/-! The original Good condition is needed only on the closed interaction
carrier. The true phase first constructs an adapted finite cover; compact
active carriers then produce open Good neighborhoods by the actual frame
reserve and its converse. Their union contains the original carrier. A
second actual partition is made inside this produced open set, so its full
cutoff supports satisfy the raw seed construction without a Good-open input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

theorem jointSecondary_signed_good_open_of_carrier
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (phase : M → ℝ) (K O : Set M) (hK : IsClosed K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hphase : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ phase O)
    (hgood : ∀ x ∈ K, GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) phase x)) :
    ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ U ⊆ O ∧
      ∀ x ∈ U, GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) phase x) := by
  obtain ⟨d⟩ := jointSecondary_exists_signed_refinement phase K O hK hO hKO hphase
    (fun x hx => (hgood x hx).1)
  choose U hU hCU hUe hUG using (fun i : Fin d.count =>
    jointSecondary_good_open_on_adapted_carrier F hF hImm phase O hO hphase
      (d.chart i) (d.maximal i) (d.source_domain i) (d.inverse_phase i)
      (K ∩ tsupport (d.cutoff i)) (hK.isCompact.inter_right (isClosed_tsupport _))
      (fun _ hx => d.cutoff_support i hx.2) (fun x hx => hgood x hx.1))
  refine ⟨⋃ i, U i,isOpen_iUnion hU,?_,?_,?_⟩
  · intro x hx
    have hsome : ∃ i : Fin d.count, d.cutoff i x ≠ 0 := by
      by_contra! hz
      have hsum := d.partition x hx
      simp only [hz,Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    obtain ⟨i,hi⟩ := hsome
    exact mem_iUnion.mpr ⟨i,hCU i ⟨hx,subset_tsupport (d.cutoff i) (Function.mem_support.mpr hi)⟩⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact d.source_domain i (hUe i hi)
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact hUG i x hi

/-- Actual scale-uniform secondary seeds now require only the original
carrier Good predicate. The open domain and every later primitive budget
are produced internally, before all contraction factors and jet orders. -/
theorem jointSecondary_exists_signed_seed_of_carrier_good
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (phase : M → ℝ) (K O : Set M) (hK : IsClosed K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hphase : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ phase O)
    (hgood : ∀ x ∈ K, GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) phase x)) :
    ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ U ⊆ O ∧
      Nonempty (JointSecondarySignedSeed (Ep := Ep) F hF phase K U) := by
  obtain ⟨U,hU,hKU,hUO,hGU⟩ :=
    jointSecondary_signed_good_open_of_carrier F hF hImm phase K O hK hO hKO hphase hgood
  exact ⟨U,hU,hKU,hUO,jointSecondary_exists_signed_seed F hF hImm phase K U hK hU hKU
    (hphase.mono hUO) hGU⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_signed_good_open_of_carrier
#print axioms GlobalEmbedding.Continuation.jointSecondary_exists_signed_seed_of_carrier_good
