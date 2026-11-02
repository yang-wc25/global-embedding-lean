import Upgrade.ProbeInterface
import Upgrade.SupportedLocalWaves
import Upgrade.SupportedValueDirections
import Upgrade.SupportedActualLocus

/-!
# Actual supported and value wave packets in the probes ABI

This packages the constructed original legal waves for the single finite-list
probe call. The normal columns come from the accepted strong supported-rank
chart; the value columns come from the accepted saturation theorem. No new
rank classification, probes construction, or incidence-rank hypothesis is used.
-/

noncomputable section
open Bundle Filter Manifold Module Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The supported-normal part of one actual finite probes list. -/
structure SupportedLocalWavePacket
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (x y : M) where
  chart : SupportedLocusLocalEquations
    {B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F x |
      Function.Surjective B ∧ LinearSecondFormPhaseRegular B.toLinearMap}
    {B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F x |
      HasSupportedKernel B.toLinearMap}
    (LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x))
  waves : Fin (n * (n - 1) / 2) → LocalLegalWave F hF
  center_eq : ∀ i, (waves i).center = x
  away : ∀ i, y ∉ tsupport ((waves i).cutoff : M → ℝ)
  one_near : ∀ᶠ z in 𝓝 x, ∀ i, (waves i).cutoff z = 1
  zero_near : ∀ᶠ z in 𝓝 y, ∀ i, (waves i).cutoff z = 0
  normal_columns : LinearIndependent ℝ (fun i ↦
    (fderiv ℝ chart.equation
      (LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)))
      ((normalSpace (I := IM) F x).orthogonalProjectionOnto.comp ((waves i).tensor x)))

/-- The already constructed actual q waves become the stable probe input
type with their SAME supported defining chart and pointwise columns. -/
theorem exists_supported_localLegalWave_packet [T2Space M]
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    (x y : M) (hxy : x ≠ y)
    (honto : Function.Surjective (trueSecondForm F hF x))
    (hsupported : HasSupportedKernel (trueSecondForm F hF x)) :
    Nonempty (SupportedLocalWavePacket F hF x y) := by
  classical
  obtain ⟨chart, xi, nu, U, psi, v, chi, hfields, hone, hzero, _, _, hli⟩ :=
    exists_supported_finite_local_legal_waves F hF himm hphase hn hN x y hxy honto hsupported
  let waves : Fin (n * (n - 1) / 2) → LocalLegalWave F hF := fun i ↦ {
    center := x
    domain := U i
    phase := psi i
    normal := v i
    cutoff := chi i
    domain_open := (hfields i).2.2.1
    center_mem := (hfields i).2.2.2.1
    domain_chart := (hfields i).2.2.2.2.1
    support_subset := (hfields i).2.2.2.2.2.1
    phase_smooth := (hfields i).2.2.2.2.2.2.2.1
    normal_smooth := (hfields i).2.2.2.2.2.2.2.2.2.2.1
    legal := (hfields i).2.2.2.2.2.2.2.2.2.2.2 }
  exact ⟨{
    chart := chart
    waves := waves
    center_eq := fun _ ↦ rfl
    away := fun i ↦ (hfields i).2.2.2.2.2.2.1
    one_near := hone
    zero_near := hzero
    normal_columns := hli }⟩

/-- The value-normal part of a finite probe list. Its independent values
belong to the actual normal space at the first endpoint. -/
structure LegalValueWavePacket
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (x y : M) (r : ℕ) where
  waves : Fin r → LocalLegalWave F hF
  center_eq : ∀ i, (waves i).center = x
  away : ∀ i, y ∉ tsupport ((waves i).cutoff : M → ℝ)
  one_near : ∀ᶠ z in 𝓝 x, ∀ i, (waves i).cutoff z = 1
  zero_near : ∀ᶠ z in 𝓝 y, ∀ i, (waves i).cutoff z = 0
  value_columns : LinearIndependent ℝ (fun i ↦
    (normalSpace (I := IM) F x).orthogonalProjectionOnto ((waves i).value x))

/-- Extend the finite actual legal generators selected from saturation.
The original local-wave theorem supplies each phase, normal field and cutoff. -/
theorem exists_legalValue_localLegalWave_packet [T2Space M]
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (x y : M) (hxy : x ≠ y) {r : ℕ}
    (xi : Fin r → E →L[ℝ] ℝ) (nu : Fin r → normalSpace (I := IM) F x)
    (hxi : ∀ i, GoodCovector F hF x (xi i))
    (hnu : ∀ i, nu i ∈ supportedRankLegalValueSpace (trueSecondForm F hF x) (xi i).toLinearMap)
    (hli : LinearIndependent ℝ nu) :
    Nonempty (LegalValueWavePacket F hF x y r) := by
  classical
  have hw (i : Fin r) :=
    upgrade_exists_local_legal_wave F hF himm x y hxy (xi i) (hxi i) (nu i) (hnu i)
  choose U psi v chi hU hxU hUsub hchi hy hpsi hpsix hvx hv hlegal hglob hcol using hw
  let waves : Fin r → LocalLegalWave F hF := fun i ↦ {
    center := x
    domain := U i
    phase := psi i
    normal := v i
    cutoff := chi i
    domain_open := hU i
    center_mem := hxU i
    domain_chart := hUsub i
    support_subset := hchi i
    phase_smooth := hpsi i
    normal_smooth := hv i
    legal := hlegal i }
  have hvalues (i : Fin r) : (normalSpace (I := IM) F x).orthogonalProjectionOnto
      ((waves i).value x) = nu i := by
    change (normalSpace (I := IM) F x).orthogonalProjectionOnto
      (chi i x • (v i x : V)) = nu i
    rw [(chi i).eq_one, one_smul, hvx i]
    exact (normalSpace (I := IM) F x).orthogonalProjectionOnto_mem_subspace_eq_self _
  refine ⟨{
    waves := waves
    center_eq := fun _ ↦ rfl
    away := hy
    one_near := Filter.eventually_all.mpr fun i ↦ (chi i).eventuallyEq_one
    zero_near := ?_
    value_columns := ?_ }⟩
  · apply Filter.eventually_all.mpr
    intro i
    filter_upwards [(isClosed_tsupport (chi i : M → ℝ)).isOpen_compl.mem_nhds (hy i)]
      with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  · simpa only [hvalues] using hli

omit [IsManifold IM ∞ M] [BoundarylessManifold IM M] in
private theorem supportedProbe_normal_dimension
    (F : M → V) (x : M)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1) :
    finrank ℝ (normalSpace (I := IM) F x) = n * (n - 1) / 2 + 1 := by
  rw [immersion_normal_rank F x himm, finrank_euclideanSpace_fin, hN]
  have heq : n * (n + 1) = n * (n - 1) + 2 * n := by
    calc
      n * (n + 1) = n * ((n - 1) + 2) := by congr 1; omega
      _ = n * (n - 1) + 2 * n := by ring
  omega

/-- At an actual supported full-rank point, saturation and local legal
extension supply n actual value waves. In n=3 these are precisely the three
value-normal columns used together with the three supported-normal columns. -/
theorem exists_supported_value_localLegalWave_packet [T2Space M]
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    (x y : M) (hxy : x ≠ y)
    (honto : Function.Surjective (trueSecondForm F hF x))
    (hsupported : HasSupportedKernel (trueSecondForm F hF x)) :
    Nonempty (LegalValueWavePacket F hF x y n) := by
  let B : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x := trueSecondForm F hF x
  have hdim := supportedProbe_normal_dimension F x (himm x) hn hN
  have hp := exists_supported_legal_value_frame B
    (trueSecondForm_linearPhaseRegular F hF hphase x) honto
    (by simpa only [finrank_euclideanSpace_fin] using hn)
    (by simpa only [finrank_euclideanSpace_fin] using hdim) hsupported
  rw [finrank_euclideanSpace_fin] at hp
  obtain ⟨xi, nu, hlegal, hli⟩ := hp
  apply exists_legalValue_localLegalWave_packet F hF himm x y hxy xi nu
  · intro i
    refine ⟨?_, (hlegal i).1.2⟩
    intro hz
    exact (hlegal i).1.1 (congrArg ContinuousLinearMap.toLinearMap hz)
  · exact fun i ↦ (hlegal i).2
  · exact hli

/-- At an actual nonsupported full-rank point, the accepted saturation lower
bound supplies n+1 actual value waves for the final coincidence operation. -/
theorem exists_nonsupported_value_localLegalWave_packet [T2Space M]
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    (x y : M) (hxy : x ≠ y)
    (honto : Function.Surjective (trueSecondForm F hF x))
    (hnonsupported : ¬ HasSupportedKernel (trueSecondForm F hF x)) :
    Nonempty (LegalValueWavePacket F hF x y (n + 1)) := by
  let B : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x := trueSecondForm F hF x
  have hdim := supportedProbe_normal_dimension F x (himm x) hn hN
  have hp := exists_nonsupported_legal_value_frame B
    (trueSecondForm_linearPhaseRegular F hF hphase x) honto
    (by simpa only [finrank_euclideanSpace_fin] using hn)
    (by simpa only [finrank_euclideanSpace_fin] using hdim) hnonsupported
  rw [finrank_euclideanSpace_fin] at hp
  obtain ⟨xi, nu, hlegal, hli⟩ := hp
  apply exists_legalValue_localLegalWave_packet F hF himm x y hxy xi nu
  · intro i
    refine ⟨?_, (hlegal i).1.2⟩
    intro hz
    exact (hlegal i).1.1 (congrArg ContinuousLinearMap.toLinearMap hz)
  · exact fun i ↦ (hlegal i).2
  · exact hli

/-- The common actual wave list for supported-coincidence incidence. The
first q labels are the support-normal waves and the next n labels are the
value-normal waves. These remain distinct labels even if wave data coincide. -/
structure SupportedJointWavePacket
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (x y : M) where
  chart : SupportedLocusLocalEquations
    {B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F x |
      Function.Surjective B ∧ LinearSecondFormPhaseRegular B.toLinearMap}
    {B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F x |
      HasSupportedKernel B.toLinearMap}
    (LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x))
  waves : Fin (n * (n - 1) / 2 + n) → LocalLegalWave F hF
  center_eq : ∀ i, (waves i).center = x
  away : ∀ i, y ∉ tsupport ((waves i).cutoff : M → ℝ)
  one_near : ∀ᶠ z in 𝓝 x, ∀ i, (waves i).cutoff z = 1
  zero_near : ∀ᶠ z in 𝓝 y, ∀ i, (waves i).cutoff z = 0
  normal_columns : LinearIndependent ℝ (fun i : Fin (n * (n - 1) / 2) ↦
    (fderiv ℝ chart.equation
      (LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)))
      ((normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
        ((waves (Fin.castAdd n i)).tensor x)))
  value_columns : LinearIndependent ℝ (fun i : Fin n ↦
    (normalSpace (I := IM) F x).orthogonalProjectionOnto
      ((waves (Fin.natAdd (n * (n - 1) / 2) i)).value x))

/-- Both rank inputs for the joint incidence come from ONE actual finite
legal wave list. No desired incidence rank, independent normal frame, or
surrogate defining equation is assumed. In n=3 the list has six waves and
supplies the literal 3 support-normal plus 3 value-normal inputs. -/
theorem exists_supported_joint_localLegalWave_packet [T2Space M]
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    (x y : M) (hxy : x ≠ y)
    (honto : Function.Surjective (trueSecondForm F hF x))
    (hsupported : HasSupportedKernel (trueSecondForm F hF x)) :
    Nonempty (SupportedJointWavePacket F hF x y) := by
  obtain ⟨p⟩ := exists_supported_localLegalWave_packet F hF himm hphase hn hN x y hxy honto hsupported
  obtain ⟨v⟩ := exists_supported_value_localLegalWave_packet F hF himm hphase hn hN x y hxy honto hsupported
  let waves : Fin (n * (n - 1) / 2 + n) → LocalLegalWave F hF :=
    Fin.addCases p.waves v.waves
  have hcutL (j : Fin (n * (n - 1) / 2)) :
      ((waves (Fin.castAdd n j)).cutoff : M → ℝ) = ((p.waves j).cutoff : M → ℝ) := by
    apply congrArg (fun w : LocalLegalWave F hF ↦ (w.cutoff : M → ℝ))
    exact Fin.addCases_left j
  have hcutR (j : Fin n) :
      ((waves (Fin.natAdd (n * (n - 1) / 2) j)).cutoff : M → ℝ) =
        ((v.waves j).cutoff : M → ℝ) := by
    apply congrArg (fun w : LocalLegalWave F hF ↦ (w.cutoff : M → ℝ))
    exact Fin.addCases_right j
  refine ⟨{
    chart := p.chart
    waves := waves
    center_eq := ?_
    away := ?_
    one_near := ?_
    zero_near := ?_
    normal_columns := ?_
    value_columns := ?_ }⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [waves, Fin.addCases_left] using p.center_eq j
    · intro j
      simpa only [waves, Fin.addCases_right] using v.center_eq j
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [hcutL] using p.away j
    · intro j
      simpa only [hcutR] using v.away j
  · filter_upwards [p.one_near, v.one_near] with z hzP hzV
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [hcutL] using hzP j
    · intro j
      simpa only [hcutR] using hzV j
  · filter_upwards [p.zero_near, v.zero_near] with z hzP hzV
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [hcutL] using hzP j
    · intro j
      simpa only [hcutR] using hzV j
  · simpa only [waves, Fin.addCases_left] using p.normal_columns
  · simpa only [waves, Fin.addCases_right] using v.value_columns

#print axioms SupportedLocalWavePacket
#print axioms exists_supported_localLegalWave_packet
#print axioms LegalValueWavePacket
#print axioms exists_legalValue_localLegalWave_packet
#print axioms exists_supported_value_localLegalWave_packet
#print axioms exists_nonsupported_value_localLegalWave_packet
#print axioms SupportedJointWavePacket
#print axioms exists_supported_joint_localLegalWave_packet

end GlobalEmbedding.Upgrade
