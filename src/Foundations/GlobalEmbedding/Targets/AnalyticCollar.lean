import GlobalEmbedding.Paper.HopfCollarProperties
import GlobalEmbedding.Targets.FreeSelectors
import GlobalEmbedding.Paper.CollarHopfInitialNormalDerivative
import GlobalEmbedding.Paper.CollarHopfLocalCKRHS
import GlobalEmbedding.Paper.CollarHopfGlobalCKAssembly
import GlobalEmbedding.Paper.HopfCollarMetricPropagation
import GlobalEmbedding.Paper.HopfCollarSquareColumnsIndependent

/-!
# Exact jointly real-analytic collars on the whole original Hopf product

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:collar,
lines508–515, with setup:partial at lines216–220.
DAG: `prop-collar`. Stage2 full original statement; proof not supplied in this draft.
-/

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- For every original positive number of factors and every C_i≥2, one real-analytic
map on the entire product and one common open real interval have exactly the collar
metric and full square-column independence in the paper. Analyticity is joint in
all native source coordinates and the real parameter. The parameter is written first;
this is the ordinary product swap of the paper's X_m × (-r0,r0). The map is defined
on all real parameters only to allow arbitrary extension outside that open collar;
no regularity or metric condition is imposed outside it or at its endpoints.

Complete source proof plan, not a replacement analytic-seed or Cauchy-solver hypothesis:

Start with the actual smooth free selector H₀ and its global complement supplied by
thm:free on this same compact Hopf product and in the exact same Euclidean dimension.
Extend H₀ to a product annulus in the actual ambient Euclidean sphere-product space
by radial projection. Multiply by a compactly supported smooth cutoff equal to one
near the product. Convolve this genuine compactly supported extension with normalized
Gaussians. The convolutions converge in every prescribed finite smooth norm. Their
complex extensions are entire: integration is over the same fixed compact support,
and all complex Gaussian derivatives are uniformly bounded on compact complex sets,
so differentiation under the integral is valid. Restriction to the native analytic
sphere product gives actual analytic approximations of H₀.

Choose one such F sufficiently C⁵-close. Its complete old first/symmetric-second
column family stays independent on the compact product. Its pairing map T_F has the
actual analytic right inverse C_F = T_Fᵀ (T_F T_Fᵀ)⁻¹. Compactness and C⁵-closeness
bound the associated multiplication operator uniformly in the original vertical
little c^{2,1/2} norm, while h = γ_D(F) - I is arbitrarily small in that same norm.
The derivative-balanced contraction therefore gives the unique small solution of
u = C_F(0,h/2) + C_F Q(u,u), with the actual fixed quadratic operator of lem:balanced.
The genuine pairing equations and metric-cancellation identity imply γ_D(F+u) = I.
The small norm bound also retains all old free columns.

Joint real analyticity requires more than smooth parameter dependence or analyticity
along each Hopf orbit. Use actual analytic local Hopf sections, giving local source
coordinates (p,y) with y in the original period-one torus. Their changes are analytic
translations in y. On a smaller compact base chart, the actual coefficients C_F and h
extend to a common complex neighborhood. The complex inverse formula uses bilinear
transpose, not conjugate transpose, and its determinant remains nonzero after shrinking.
For small complex α, replace coefficients by their values at (p,y+α), leaving y real.
On smaller complex strips their Taylor series converge with three y-derivatives;
hence they are holomorphic in (p,α) with values in the same little c^{2,1/2} space.
The complexified bilinear Q is fixed. Shrink the complex parameter neighborhood so
the original small ball is invariant and the contraction constant is below 3/4.
Iteration from zero converges uniformly to a holomorphic Banach-valued fixed point;
the Cauchy integral identities pass to this limit.

For real p and α, translation invariance and uniqueness identify that fixed point
by u(p,α)(y) = u(p,0)(y+α). Evaluation at any real y₀ is continuous, so evaluation
of the holomorphic family makes the actual correction jointly analytic near (p,y₀).
Uniqueness glues these actual local corrections on overlaps. Thus H = F+u is one
global analytic exact free map. Its ordered free columns have codimension one in
this target. Their actual oriented cofactor is analytic and never zero; dividing
by its positive norm gives one global analytic unit normal ν, perpendicular to
all first and sorted second columns of this same H.

Prescribe G(0,x) = H(x) and G_r(0,x) = ν(x). The actual square pairing map is
T_G(w) = (inner(w,G_r), inner(w,Y_iG), inner(w,Y_iY_jG)) for the original i≤j.
Its initial matrix is invertible by freeness and the unit complement. Impose the
actual second-order system G_rr = T_G⁻¹(0,0,(inner(Y_iG_r,Y_jG_r))_{i≤j}).
In analytic source coordinates, including all transverse sphere coordinates as
spatial variables, this right side is analytic wherever the square matrix is
invertible. It has total differential order at most two and no second r-derivative.
The analytic Cauchy theorem of the paper applies to this actual system and these
actual analytic initial data. Local uniqueness identifies solutions on chart overlaps.
A finite cover of the compact entire product gives one common positive interval;
shrink it once more to retain square-matrix invertibility at every collar point.

Finally propagate all three constraints for this same solution, not just at r=0.
The equation gives ∂r ‖G_r‖² = 2 inner(G_rr,G_r) = 0, so the squared speed stays one.
Next ∂r inner(G_r,Y_iG) = inner(G_rr,Y_iG) + Y_i(‖G_r‖²)/2 = 0, so each mixed
term stays zero from its initial normal orthogonality. The commuting derivatives give
∂r² inner(Y_iG,Y_jG) = 2 inner(Y_iG_r,Y_jG_r)
  + Y_i inner(G_rr,Y_jG) + Y_j inner(G_rr,Y_iG)
  - 2 inner(G_rr,Y_iY_jG) = 0.
The old Gram initially is I and its initial first r-derivative is
-2 inner(ν,Y_iY_jH) = 0, by the actual complementary normal. Hence the old Gram
remains I throughout the same interval. The retained square-matrix invertibility
is exactly independence of G_r and the complete original first and sorted second
columns, including diagonals. All conclusions hold at every source and interval point.

The target supplies no analytic seed, inverse, Cauchy solver, chosen common radius,
local solution, normalization, rank hypothesis or desired metric identity. It retains
one jointly analytic map, one positive common radius, the original native whole
product and flows, and the exact original s_m+m+1 dimension.
Source: prop:collar, statement508–515 and complete proof516–562. -/
theorem exact_analytic_hopf_collar (m : ℕ) (hm : 1 ≤ m)
    (C : Fin m → ℕ) (hC : ∀ i, 2 ≤ C i) :
    letI : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have := hC i; omega⟩
    ∃ r0 : ℝ, 0 < r0 ∧
      ∃ G : ℝ × FreeHopfProduct C →
          EuclideanSpace ℝ (Fin (freeSymmetricColumnCount m + m + 1)),
        AnalyticHopfCollarProperties C r0 G := by
  classical
  let _ : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have := hC i; omega⟩
  obtain ⟨H, ν, hH, hν, hGram, _, _, hunit, hperp, hsquare, _⟩ :=
    collarHopf_analytic_cauchy_normal_data m hm C hC
  obtain ⟨U, r, g, hU, hr, hcenter, hlocal, hjoint, hinitial, hPDE⟩ :=
    collarHopf_local_cauchy_family C H ν hH hν hsquare
  obtain ⟨δ, hδ, G, hG, htrace, hglobalPDE⟩ :=
    collarHopf_global_cauchy_solution_of_local C H ν U hU r hr g
      (fun x ↦ ⟨x, hcenter x⟩) hlocal hjoint hinitial hPDE
  have hT : ∀ t ∈ Set.Ioo (-δ) δ, ∀ x,
      (hopfCollarSquarePairing C G t x).IsInvertible :=
    fun t ht x ↦ (hglobalPDE t ht x).1
  have hmetric := hopfCollar_square_pde_metric_propagation C δ hδ H ν
    hH hν hGram hunit hperp G hG (fun x ↦ (htrace x).1) (fun x ↦ (htrace x).2)
    hT (fun t ht x ↦ (hglobalPDE t ht x).2)
  refine ⟨δ, hδ, G, hG, ?_⟩
  intro t ht x
  exact ⟨(hmetric t ht x).1, (hmetric t ht x).2.1, (hmetric t ht x).2.2,
    hopfCollar_square_columns_linearIndependent C G t x (hT t ht x)⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.exact_analytic_hopf_collar
