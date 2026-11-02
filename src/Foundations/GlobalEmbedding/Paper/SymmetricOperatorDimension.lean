import GlobalEmbedding.Paper.QuadraticSpaceKernelSupport
import Mathlib.Data.Sym.Card

/-! Sharp dimension upper bound for actual supported selfadjoint operators.
`Sym2` is used ONLY to index unordered matrix coefficients, never as a replacement
for the original binary symmetric tensor quotient. Source: revised1810–1814. -/

noncomputable section
open Module
namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Symmetric coefficients on a spanning basis determine the whole actual
supported operator, including its values away from the supporting subspace. -/
theorem quadraticSpace_eq_zero_of_supported_coefficients
    (U : Submodule ℝ V) {ι : Type*} (b : Basis ι ℝ U)
    (Q : V →L[ℝ] V) (hQ : Q.toLinearMap.IsSymmetric)
    (hr : ∀ v, Q v ∈ U)
    (hcoeff : ∀ i j, inner ℝ (Q (b i)) (b j) = 0) : Q = 0 := by
  have hbi (i : ι) : Q (b i) = 0 := by
    let L : U →L[ℝ] ℝ := (innerSL ℝ (Q (b i))).comp U.subtypeL
    have hLlin : L.toLinearMap = 0 := b.ext (fun j ↦ hcoeff i j)
    have hL : L = 0 := by
      ext u
      exact LinearMap.congr_fun hLlin u
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact congrArg (fun l : U →L[ℝ] ℝ ↦ l ⟨Q (b i), hr (b i)⟩) hL
  have hres : Q.toLinearMap.comp U.subtype = 0 := by
    apply b.ext
    exact hbi
  ext v
  have hkill : Q (Q v) = 0 := LinearMap.congr_fun hres ⟨Q v, hr v⟩
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  calc
    inner ℝ (Q v) (Q v) = inner ℝ v (Q (Q v)) := hQ v (Q v)
    _ = 0 := by rw [hkill, inner_zero_right]

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The literal symmetric matrix coefficients of a linear operator family,
indexed by unordered pairs of basis indices. -/
def quadraticSpaceSymmetricCoefficients
    (F : M →ₗ[ℝ] V →L[ℝ] V) (hF : ∀ a, (F a).toLinearMap.IsSymmetric)
    (U : Submodule ℝ V) {ι : Type*} (b : Basis ι ℝ U) :
    M →ₗ[ℝ] (Sym2 ι → ℝ) where
  toFun a := Sym2.lift ⟨fun i j ↦ inner ℝ (F a (b i)) (b j), fun i j ↦ by
    calc
      inner ℝ (F a (b i)) (b j) = inner ℝ (b i : V) (F a (b j)) := hF a (b i) (b j)
      _ = inner ℝ (F a (b j)) (b i) := real_inner_comm _ _⟩
  map_add' a c := by
    funext z
    induction z using Sym2.inductionOn with
    | _ i j => simp [inner_add_left]
  map_smul' t a := by
    funext z
    induction z using Sym2.inductionOn with
    | _ i j => simp [inner_smul_left]

/-- No coefficient information is lost for an injective family with actual
range in U. -/
theorem quadraticSpaceSymmetricCoefficients_injective
    (F : M →ₗ[ℝ] V →L[ℝ] V) (hinj : Function.Injective F)
    (hF : ∀ a, (F a).toLinearMap.IsSymmetric)
    (U : Submodule ℝ V) (hr : ∀ a v, F a v ∈ U)
    {ι : Type*} (b : Basis ι ℝ U) :
    Function.Injective (quadraticSpaceSymmetricCoefficients F hF U b) := by
  intro a c hac
  have hz : F (a - c) = 0 :=
    quadraticSpace_eq_zero_of_supported_coefficients U b (F (a - c)) (hF (a - c))
      (hr (a - c)) (fun i j ↦ by
        have hh := congrFun hac s(i, j)
        change inner ℝ (F a (b i)) (b j) = inner ℝ (F c (b i)) (b j) at hh
        simpa [map_sub, inner_sub_left] using sub_eq_zero.mpr hh)
  exact hinj (sub_eq_zero.mp (by simpa only [map_sub] using hz))

/-- Sharp triangular upper bound for any injective real linear family of
selfadjoint operators supported on the same actual finite-dimensional U.
Source: revised1810–1814. The unordered index count is native Mathlib. -/
theorem quadraticSpace_finrank_le_of_supported [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ M]
    (F : M →ₗ[ℝ] V →L[ℝ] V) (hinj : Function.Injective F)
    (hF : ∀ a, (F a).toLinearMap.IsSymmetric)
    (U : Submodule ℝ V) (hr : ∀ a v, F a v ∈ U) :
    finrank ℝ M ≤ finrank ℝ U * (finrank ℝ U + 1) / 2 := by
  let b := Module.finBasis ℝ U
  have hd := LinearMap.finrank_le_finrank_of_injective
    (quadraticSpaceSymmetricCoefficients_injective F hinj hF U hr b)
  simpa [Module.finrank_fintype_fun_eq_card, Sym2.card, Nat.choose_two_right,
    Nat.mul_comm] using hd

#print axioms quadraticSpace_eq_zero_of_supported_coefficients
#print axioms quadraticSpaceSymmetricCoefficients
#print axioms quadraticSpaceSymmetricCoefficients_injective
#print axioms quadraticSpace_finrank_le_of_supported

end GlobalEmbedding.Paper
