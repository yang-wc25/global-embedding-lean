import Upgrade.RankQFixedPacketWeights

/-!
# The fixed local packet supplies the actual joint normal principal rank

This specializes the accepted duplicated-principal proof to the fixed packet
selected BEFORE probes. The ambient columns are exactly its global wave
`tensors` and `values`; their projection is computed, not supplied by a rank
hypothesis. The same packet works for every positive unequal returned weight.
-/

noncomputable section
open Manifold Module Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Upgrade
open Paper Paper.SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The normal of each fixed legal wave lies in the actual one-dimensional
perpendicular range of the original true form. -/
theorem RankQLocalWavePacket.normal_mem_range_orthogonal
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket F hF x y)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm F hF x).range = n * (n - 1) / 2)
    (i : Fin n) :
    (p.waves i).normal x ∈ (rankQActualReference F hF x).rangeᗮ := by
  have hx : x ∈ (p.waves i).domain :=
    (congrArg (fun z ↦ z ∈ (p.waves i).domain) (p.center_eq i)).mp
      (p.waves i).center_mem
  have hlegal := (p.waves i).legal x hx
  have h := (rankQActual_dims_and_legal F hF x himm hphase hn hN hrank).2.2
    (mfderiv IM 𝓘(ℝ, ℝ) (p.waves i).phase x) hlegal.1
  exact h ▸ hlegal.2

/-- Full joint projected span of the same fixed actual tensor/value packet.
The only rank assumption is the original stratum rank of `trueSecondForm`;
no rank of a perturbation or incidence derivative is an input. -/
theorem RankQLocalWavePacket.normal_coordinates_span
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket F hF x y)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm F hF x).range = n * (n - 1) / 2)
    (lambda : Fin n → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    let B := rankQActualReference F hF x
    let PN : V →L[ℝ] normalSpace (I := IM) F x :=
    (normalSpace (I := IM) F x).orthogonalProjectionOnto
    ∃ ell : Fin n → B.rangeᗮ,
      (∀ i, (ell i : normalSpace (I := IM) F x) = (p.waves i).normal x) ∧
      let J (ij : Fin n × Fin 2) :=
        (rankQNormalBlock B (PN.comp ((p.waves ij.1).tensor x)),
          -((lambda ij.1 ij.2 ^ 2)⁻¹) • ell ij.1)
      Submodule.span ℝ (Set.range J) = ⊤ ∧
        finrank ℝ (Submodule.span ℝ (Set.range J)) = n + 1 := by
  classical
  let : NormedAddCommGroup (SymmetricSquare E) := operatorSquareNormed
  let : NormedSpace ℝ (SymmetricSquare E) := squareNS _
  let : NormedAddCommGroup (normalSpace (I := IM) F x) := Submodule.normedAddCommGroup _
  let : InnerProductSpace ℝ (normalSpace (I := IM) F x) := inferInstance
  let B := rankQActualReference F hF x
  let K := B.ker
  let L := B.rangeᗮ
  let : NormedAddCommGroup K := inferInstance
  let : NormedSpace ℝ K := inferInstance
  let : NormedAddCommGroup L := inferInstance
  let : NormedSpace ℝ L := inferInstance
  let : NormedAddCommGroup (K →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (K →L[ℝ] L) := inferInstance
  let PN : V →L[ℝ] normalSpace (I := IM) F x :=
    (normalSpace (I := IM) F x).orthogonalProjectionOnto
  let PL : normalSpace (I := IM) F x →L[ℝ] L := L.orthogonalProjectionOnto
  let Q : V →L[ℝ] L := PL.comp PN
  let ell (i : Fin n) : L :=
    ⟨(p.waves i).normal x, p.normal_mem_range_orthogonal himm hphase hn hN hrank i⟩
  let D (i : Fin n) : K →L[ℝ] L := rankQNormalBlock B (PN.comp ((p.waves i).tensor x))
  have hdim := rankQActual_dims_and_legal F hF x himm hphase hn hN hrank
  have hDkill (i : Fin n) (hi : ell i = 0) : D i = 0 := by
    have hnormal : (p.waves i).normal x = 0 := congrArg Subtype.val hi
    have hvalue : ((p.waves i).normal x : V) = 0 := congrArg Subtype.val hnormal
    have htensor : (p.waves i).tensor x = 0 := by
      apply ContinuousLinearMap.ext
      intro s
      change (p.waves i).cutoff x •
        (supportedRankCovectorSquare
          (mfderiv IM 𝓘(ℝ, ℝ) (p.waves i).phase x).toLinearMap s •
            ((p.waves i).normal x : V)) = 0
      rw [hvalue, smul_zero, smul_zero]
    apply ContinuousLinearMap.ext
    intro k
    change PL (PN ((p.waves i).tensor x k.val)) = 0
    rw [htensor]
    exact (congrArg PL PN.map_zero).trans PL.map_zero
  have hRform (t : Fin n → ℝ) :
      rankQWaveNormalBlock F hF x p.waves t = ∑ i, t i • D i :=
    rankQWaveNormalBlock_eq_sum F hF x p.waves t
  have hp := rankQFixedPacket_duplicated_span (by omega : 0 < n)
    K L D ell (rankQWaveNormalBlock F hF x p.waves)
    hdim.1 hdim.2.1 hDkill hRform p.normalBlock_onto lambda hlambda hne
  exact ⟨ell, fun _ ↦ rfl, hp.1, hp.2⟩


/-- The literal cutoff-one global value has exactly its true normal
coordinate, after both actual orthogonal projections. -/
theorem RankQLocalWavePacket.projected_value_coordinates
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket F hF x y)
    (ell : Fin n → (rankQActualReference F hF x).rangeᗮ)
    (hell : ∀ i, (ell i : normalSpace (I := IM) F x) = (p.waves i).normal x) :
    ∀ i, (rankQActualReference F hF x).rangeᗮ.orthogonalProjectionOnto
      ((normalSpace (I := IM) F x).orthogonalProjectionOnto ((p.waves i).value x)) = ell i := by
  let L := (rankQActualReference F hF x).rangeᗮ
  let PN : V →L[ℝ] normalSpace (I := IM) F x :=
    (normalSpace (I := IM) F x).orthogonalProjectionOnto
  let PL : normalSpace (I := IM) F x →L[ℝ] L := L.orthogonalProjectionOnto
  let Q : V →L[ℝ] L := PL.comp PN
  intro i
  have hone : (p.waves i).cutoff x = 1 := p.one_near.self_of_nhds i
  have hv : (p.waves i).value x = ((p.waves i).normal x : V) := by
    simp only [LocalLegalWave.value, hone, one_smul]
  have hn : PN ((p.waves i).normal x : V) = (p.waves i).normal x :=
    (normalSpace (I := IM) F x).orthogonalProjectionOnto_mem_subspace_eq_self _
  have hl : PL ((p.waves i).normal x) = ell i :=
    (congrArg PL (hell i).symm).trans
      (L.orthogonalProjectionOnto_mem_subspace_eq_self (ell i))
  exact (congrArg Q hv).trans ((congrArg PL hn).trans hl)

end GlobalEmbedding.Upgrade
