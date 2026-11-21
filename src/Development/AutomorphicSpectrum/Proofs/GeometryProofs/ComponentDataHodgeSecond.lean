module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundleStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameDomainInSegreChartStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairLatticeSumComapStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BlockSumFrame

theorem isVB_comap_of_range {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E'] (A : Lat ξ E')
    (S : Submodule Ω E') (i : E →ₗ[Ω] E') (hinj : Function.Injective i) (hrange : LinearMap.range i = S) {r : ℕ}
    (h : (Lat.comap A S.subtype).IsVB r ⊤) : (Lat.comap A i).IsVB r ⊤ := by
  have hmem : ∀ x, i x ∈ S := fun x => hrange ▸ LinearMap.mem_range_self i x
  let e : E →ₗ[Ω] S := i.codRestrict S hmem
  have hei : ∀ x, ((e x : S) : E') = i x := fun x => rfl
  have he_inj : Function.Injective e := fun x y hxy => hinj (by rw [← hei, ← hei, hxy])
  have he_surj : Function.Surjective e := fun s => by
    have : (s : E') ∈ LinearMap.range i := hrange ▸ s.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Subtype.ext hx⟩
  let eq : E ≃ₗ[Ω] S := LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩
  have heq : ∀ x, ((eq x : S) : E') = i x := fun x => rfl
  intro p hp
  obtain ⟨U, hpU, b, hspan, hfr⟩ := h p hp
  refine ⟨U, hpU, fun k => eq.symm (b k), ?_, fun q hq hqU => ?_⟩
  · have : Set.range (fun k => eq.symm (b k)) = eq.symm '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, ← LinearEquiv.coe_coe, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨hli, hst⟩ := hfr q hq hqU
    refine ⟨hli.map' eq.symm.toLinearMap (LinearEquiv.ker _), ?_⟩
    ext x
    have h1 : x ∈ Lat.comap A i q ↔ eq x ∈ Lat.comap A S.subtype q := Iff.rfl
    rw [h1, hst]
    let eR : E ≃ₗ[regAt ξ q] S := eq.restrictScalars (regAt ξ q)
    have hrng : Set.range b = eR '' Set.range (fun k => eq.symm (b k)) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun k => (eq.apply_symm_apply (b k)).symm)
    rw [hrng, ← LinearEquiv.coe_coe, ← Submodule.map_span]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := eR.injective hyx
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩

theorem frame_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (cc : (k : K) → J k) (f : Ω) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), CoordsAt Or.𝔐.ξ Dc.y z w → IsFrameOver Dc.y (Dc.W τ) cc f b → InFrameDomain Dc.y cc f w → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w τ cc f b h hw hfr hd
  have hT : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  have hrk : labelRk D (Or.bg τ) + labelRk D (Or.sm τ) = Dc.N := by
    rw [Or.rk_bg, Or.rk_sm]
    exact Nat.add_sub_cancel' Dc.j_le_N
  have hsum : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p)
      (Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ)).subtype).IsVB
      (labelRk D (Or.bg τ) + labelRk D (Or.sm τ)) ⊤ := by
    have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
    obtain ⟨-, -, -, -, -, -, hind, -⟩ :=
      GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S₀ Ω K J Dc.y Or.𝔐 hβ
    have hdisj : Disjoint (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) := hind.pairwiseDisjoint (Or.bg_ne_sm τ τ)
    intro p _
    obtain ⟨Ua, hpa, f, hfs, hff⟩ := Or.𝔐.vb (Or.bg τ) p (Set.mem_univ _)
    obtain ⟨Ub, hpb, g, hgs, hgf⟩ := Or.𝔐.vb (Or.sm τ) p (Set.mem_univ _)
    have hfs' : Submodule.span Ω (Set.range f) = Or.𝔐.Vgen (Or.bg τ) := hfs
    have hgs' : Submodule.span Ω (Set.range g) = Or.𝔐.Vgen (Or.sm τ) := hgs
    have hspan : Submodule.span Ω (Set.range (Fin.append f g)) = Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := by
      rw [GlobalTheory.CompanionTheory.Ar.HodgeSum.range_append, Submodule.span_union, hfs', hgs']
    have hmem : ∀ k, Fin.append f g k ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := fun k => by
      rw [← hspan]
      exact Submodule.subset_span (Set.mem_range_self k)
    have hli : LinearIndependent Ω (Fin.append f g) :=
      GlobalTheory.CompanionTheory.Ar.HodgeSum.linearIndependent_append (hff p (Set.mem_univ _) hpa).1 (hgf p (Set.mem_univ _) hpb).1
        (by rw [hfs', hgs']; exact hdisj)
    refine ⟨Ua ⊓ Ub, ⟨hpa, hpb⟩, fun k => ⟨Fin.append f g k, hmem k⟩,
      GlobalTheory.CompanionTheory.Ar.HodgeSum.span_lift_eq_top (fun _ => rfl) hspan, fun q _ hq => ⟨?_, ?_⟩⟩
    · exact LinearIndependent.of_comp (Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ)).subtype hli
    · have h1 : Or.𝔐.V (Or.bg τ) q = Submodule.span (regAt Or.𝔐.ξ q) (Set.range f) := (hff q (Set.mem_univ _) hq.1).2
      have h2 : Or.𝔐.V (Or.sm τ) q = Submodule.span (regAt Or.𝔐.ξ q) (Set.range g) := (hgf q (Set.mem_univ _) hq.2).2
      show (Or.𝔐.V (Or.bg τ) q ⊔ Or.𝔐.V (Or.sm τ) q).comap ((Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ)).subtype.restrictScalars (regAt Or.𝔐.ξ q)) = _
      rw [h1, h2]
      exact GlobalTheory.CompanionTheory.Ar.HodgeSum.comap_sup_span (regAt Or.𝔐.ξ q) fun _ => rfl
  rw [hrk] at hsum
  have hvb : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsVB Dc.N ⊤ :=
    isVB_comap_of_range _ _ (Or.i τ) (Or.i_inj τ) (Or.i_range τ) hsum
  obtain ⟨c1, c2⟩ := GlobalTheory.T.frame_domain_in_segre_chart Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y hT z w cc f h hw hd
  exact (GlobalTheory.T.segre_chart_bundle Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y (W τ) Dc.N (Dc.W τ) _ hT hvb (Or.lat τ) cc f b hfr.1 hfr.2.1
    hfr.2.2.1).1 hfr _ c1 c2

end GlobalTheory.CompanionTheory.Ar.BlockSumFrame
