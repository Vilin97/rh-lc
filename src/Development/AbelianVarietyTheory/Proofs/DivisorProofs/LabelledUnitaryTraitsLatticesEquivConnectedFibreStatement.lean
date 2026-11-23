module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstOfSpecialisationInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtIffOfSpecializes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeUnitaryClassicalTraitCentreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupOfPointEqAlongModelHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRankEqRankThetaGroupOfPointPerpStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEndomorphismsTorsionExtendSemiAbelianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernel
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreConstPreconnected

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.GFib

theorem latAt_const_on_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y : RatModel o Ω) (G : Over Y.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Z : Scheme.{0}) (q : Y.Z ⟶ Z) (z : Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → (∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt G w r₀) → ∀ (I T : Type) (f : I → (G ⟶ G)), (∀ e, IsMonHom (f e)) → ∀ (gγ : T → (Over.mk Y.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ t, gγ t ^ L = 1) → (∀ t w, q.base w = z → ExtNear (gγ t) w) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (w w' : Y.Z), q.base w = z → q.base w' = z → LatAt f gγ ζ L m c w → LatAt f gγ ζ L m c w' := by
  intro o Ω _ _ _ _ Y G _ _ hG Z q z hpre hrk I T f hf gγ ζ L hL hζ hu hγ hext X _ _ _ m c w w' hw hw'
  obtain ⟨r₀, hr⟩ := hrk
  haveI : IsNoetherianRing o := by
    haveI := ArithBase.ded (o := o) (Ω := Ω)
    infer_instance
  haveI := Y.lft
  haveI := Y.qc
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.Z := QuasiCompact.compactSpace_of_compactSpace Y.s
  haveI : IsNoetherian Y.Z := {}
  exact GlobalTheory.fibre_const_of_specializes_invariant Y.Z Z q.base q.continuous z hpre
    (fun v => LatAt f gγ ζ L m c v)
    (fun a b ha hb hab => latAt_iff_of_specializes hG hL hζ hu hf hγ m c hab (hr a ha) (hr b hb)
      (fun t => hext t b hb)) w w' hw hw'

end GlobalTheory.UPoinc.GFib
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreConstPreconnectedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.characterLatticeAtFibre_const_preconnected : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y : RatModel o Ω) (G : Over Y.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Z : Scheme.{0}) (q : Y.Z ⟶ Z) (z : Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → (∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt G w r₀) → ∀ (I T : Type) (f : I → (G ⟶ G)), (∀ e, IsMonHom (f e)) → ∀ (gγ : T → (Over.mk Y.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ t, gγ t ^ L = 1) → (∀ t w, q.base w = z → ExtNear (gγ t) w) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (w w' : Y.Z), q.base w = z → q.base w' = z → LatAt f gγ ζ L m c w → LatAt f gγ ζ L m c w' := by
  first | exact @GlobalTheory.UPoinc.GFib.latAt_const_on_fibre | exact GlobalTheory.UPoinc.GFib.latAt_const_on_fibre | (intros; apply GlobalTheory.UPoinc.GFib.latAt_const_on_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreUniqueUpToIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GFibUniq

theorem isPrimitiveRoot_map {o : Type} [CommRing o] [IsDomain o] {ζ : o} {L : ℕ} (hL : 0 < L)
    (hζ : IsPrimitiveRoot ζ L) (hu : IsUnit (L : o)) (κ : Type) [Field κ] (a : o →+* κ) : IsPrimitiveRoot (a ζ) L := by
  haveI : NeZero (L : κ) := ⟨by simpa using (hu.map a).ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have hr := (hζ.isRoot_cyclotomic hL).map (f := a)
  simpa [Polynomial.map_cyclotomic] using hr

theorem latAt_unique : ∀ (o Ω : Type) [CommRing o] [IsDomain o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → IsPrimitiveRoot (ζ : o) L → IsUnit (L : o) → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (m : I → X →+ X) (c : T → X →+ ZMod L) (m' : I → X' →+ X') (c' : T → X' →+ ZMod L) (w : M.Z), LatAt f gγ ζ L m c w → LatAt f gγ ζ L m' c' w → ∃ e : X ≃+ X', (∀ i x, e (m i x) = m' i (e x)) ∧ ∀ t x, c' t (e x) = c t x := by
  intro o Ω _ _ _ _ M G _ _ hG I T f gγ ζ L hL hζ hu X X' _ _ _ _ _ _ m c m' c' w h h'
  haveI : IsSeparated G.hom := hG.separated
  exact LatAt.unique hL (fun κ _ a => isPrimitiveRoot_map hL hζ hu κ a) h h'

end GlobalTheory.UPoinc.GFibUniq
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreUniqueUpToIsoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.characterLatticeAtFibre_unique_up_to_iso : ∀ (o Ω : Type) [CommRing o] [IsDomain o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → IsPrimitiveRoot (ζ : o) L → IsUnit (L : o) → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (m : I → X →+ X) (c : T → X →+ ZMod L) (m' : I → X' →+ X') (c' : T → X' →+ ZMod L) (w : M.Z), LatAt f gγ ζ L m c w → LatAt f gγ ζ L m' c' w → ∃ e : X ≃+ X', (∀ i x, e (m i x) = m' i (e x)) ∧ ∀ t x, c' t (e x) = c t x := by
  first | exact @GlobalTheory.UPoinc.GFibUniq.latAt_unique | exact GlobalTheory.UPoinc.GFibUniq.latAt_unique | (intros; apply GlobalTheory.UPoinc.GFibUniq.latAt_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitaryTraitLabels_surjective_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → Function.Surjective yy ∧ yy.ker = X.S.HH X.M z := by
  first | exact @GlobalTheory.UPoinc.uIsLab_onto_and_ker | exact GlobalTheory.UPoinc.uIsLab_onto_and_ker | (intros; apply GlobalTheory.UPoinc.uIsLab_onto_and_ker <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledUnitaryTraitsLatticesEquivConnectedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.Poinc.FibLat

namespace GlobalTheory.UPoinc.GFib

theorem TT_le_HH_of_uIsLab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf} (X : USetup C) {p : ℕ} [Fact p.Prime]
    {z : X.M.Z} (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (h : UIsLab X ct yy)
    (hker : yy.ker = X.S.HH X.M z) : X.S.TT X.M z ≤ X.S.HH X.M z := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, -, G, _, α, β, -, -, -, y₀, -, u, lb, j, -, hlab, -⟩ := h
  have hk : lb.yy.ker ≤ yy.ker := fun a ha => by
    have h0 : lb.yy a = QuotientAddGroup.mk 0 := by rw [AddMonoidHom.mem_ker.1 ha]; rfl
    have := hlab a 0 h0
    rw [map_zero] at this
    exact AddMonoidHom.mem_ker.2 this
  intro t ht
  rw [← hker]
  refine hk ?_
  have h1 : t ∈ (X.S.rechart c₀ hc R' fg frac hth hev).perp lb.yy.ker := fun h hh => ht h (hker ▸ hk hh)
  have h2 := lb.isoFree.1 h1
  rwa [ThetaSys.perp_perp] at h2

end GlobalTheory.UPoinc.GFib

theorem GlobalTheory.UPoinc.GFib.labelled_lattices_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (_ : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → ∀ (ct ct' : UCTrait X p z) (y y' : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → y' ≫ q = ct'.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct'.T.P.D.toPre.X), UIsLabW X wi ct yy → UIsLabW X wi ct' yy' → ∃ θ : ct.T.P.D.toPre.X ≃+ ct'.T.P.D.toPre.X, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (θ μ)) ∧ ∀ (a : 𝓞 E) v, θ (a • v) = a • θ v := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO hE hP hpt p _ z hz ct ct' y y' hy hy' yy yy' hl hl'
  have hker := GlobalTheory.T.unitaryTraitLabels_surjective_kernel E H Dw hpq l Xo cf C X p z ct yy hl.uIsLab
  have hker' := GlobalTheory.T.unitaryTraitLabels_surjective_kernel E H Dw hpq l Xo cf C X p z ct' yy' hl'.uIsLab
  have hTH := GlobalTheory.UPoinc.GFib.TT_le_HH_of_uIsLab X ct yy hl.uIsLab hker.2
  obtain ⟨f, gγ, hf, hg⟩ := GlobalTheory.T.unitaryEndomorphisms_torsion_extend_semiAbelian E H Dw l Xo cf C X wi Y U₀ EE FinalForm q hO hE hpt z hTH
  have hL : 0 < X.S.r * X.S.N := Nat.mul_pos (by have := X.S.r_pos; omega) (by have := X.S.N_ge; omega)
  have hprim : IsPrimitiveRoot (X.S.ζ ^ (X.S.r * X.S.N)) (X.S.r * X.S.N) :=
    X.S.prim.pow (by positivity) (by ring)
  let ζ : X.o₁ˣ := (hprim.isUnit hL.ne').unit
  have hζ : IsPrimitiveRoot (ζ : X.o₁) (X.S.r * X.S.N) := hprim
  obtain ⟨s, σ, hs, hσ, hc⟩ :=
    GlobalTheory.T.characterLattice_unitaryClassicalTrait_centre E H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO hE hP hpt p z f gγ hf hg ζ hζ
  obtain ⟨c, hc1, hc2⟩ := hc ct y hy yy hl
  obtain ⟨c', hc1', hc2'⟩ := hc ct' y' hy' yy' hl'
  have hx : q.base (y (cPt p)) = z := by
    rw [← Scheme.Hom.comp_apply, hy, ct.cen]
  have hx' : q.base (y' (cPt p)) = z := by
    rw [← Scheme.Hom.comp_apply, hy', ct'.cen]

  have hrk : ∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt FinalForm.G w r₀ := by
    obtain ⟨r₀, -, ⟨e₀⟩⟩ := GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp X.o₁ X.Ω₁ X.S X.ρ Y U₀ EE FinalForm X.big hO hE (y (cPt p))
    refine ⟨r₀, fun w hw => ?_⟩
    obtain ⟨r, hr, ⟨e⟩⟩ := GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp X.o₁ X.Ω₁ X.S X.ρ Y U₀ EE FinalForm X.big hO hE w
    have hT : X.S.TT Y w = X.S.TT Y (y (cPt p)) := by
      simp only [ThetaSys.TT]
      rw [GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom X.o₁ X.Ω₁ X.S X.M Y q hpt X.hasDiv w,
        GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom X.o₁ X.Ω₁ X.S X.M Y q hpt X.hasDiv (y (cPt p))]
      simp only [hw, hx]
    have e₁ : (Fin r → ZMod (X.S.r * X.S.N)) ≃ (Fin r₀ → ZMod (X.S.r * X.S.N)) :=
      (e.symm.toEquiv.trans (by rw [hT])).trans
        e₀.toEquiv
    haveI : NeZero (X.S.r * X.S.N) := ⟨hL.ne'⟩
    have hcard := Fintype.card_congr e₁
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
    have h2 : 2 ≤ X.S.r * X.S.N := by
      have := X.S.r_pos; have := X.S.N_ge; nlinarith
    rwa [Nat.pow_right_injective h2 hcard] at hr
  have hmove := GlobalTheory.T.characterLatticeAtFibre_const_preconnected X.o₁ X.Ω₁ Y FinalForm.G FinalForm.semi _ q z hz hrk (𝓞 E) _ f (fun a => (hf a).1) gγ ζ
    (X.S.r * X.S.N) hL (Units.ext (by simpa using hζ.pow_eq_one)) X.S.unit (fun t => (hg t).1)
    (fun t w hw => (hg t).2.2 w hw) ct.T.P.D.toPre.X _ c _ _ hx hx' hc1
  haveI : IsDomain X.o₁ := (inferInstance : GlobalTheory.ZH.ArithBase X.o₁ X.Ω₁).ded.toIsDomain
  obtain ⟨θ, hθm, hθc⟩ := GlobalTheory.T.characterLatticeAtFibre_unique_up_to_iso X.o₁ X.Ω₁ Y FinalForm.G FinalForm.semi (𝓞 E) _ f gγ ζ (X.S.r * X.S.N) hL hζ
    X.S.unit ct.T.P.D.toPre.X ct'.T.P.D.toPre.X _ c _ c' _ hmove hc1'
  refine ⟨θ, fun a v hv => ?_, fun a v => ?_⟩
  · obtain ⟨a', ha'⟩ := hker'.1 (QuotientAddGroup.mk (θ v))
    have hd : a' - a ∈ X.S.HH X.M z := by
      rw [← ThetaSys.perp_TT]
      refine ThetaSys.mem_perp'.2 fun t ht => ?_
      have e1 := hc2' a' (θ v) ⟨t, ht⟩ ha'
      rw [hθc, hc2 a v ⟨t, ht⟩ hv] at e1
      have e2 := hs.mul_left_cancel e1
      rw [sub_eq_add_neg, eStd_add_right, eStd_neg_right, ← e2]
      exact add_neg_cancel _
    rw [← hker'.2, AddMonoidHom.mem_ker, map_sub, sub_eq_zero] at hd
    rw [← hd, ha']
  · obtain ⟨b, rfl⟩ := hσ a
    exact hθm b v
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledUnitaryTraitsLatticesEquivConnectedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.labelledUnitaryTraits_lattices_equiv_connectedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (_ : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → ∀ (ct ct' : UCTrait X p z) (y y' : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → y' ≫ q = ct'.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct'.T.P.D.toPre.X), UIsLabW X wi ct yy → UIsLabW X wi ct' yy' → ∃ θ : ct.T.P.D.toPre.X ≃+ ct'.T.P.D.toPre.X, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (θ μ)) ∧ ∀ (a : 𝓞 E) v, θ (a • v) = a • θ v := by
  first | exact @GlobalTheory.UPoinc.GFib.labelled_lattices_equiv | exact GlobalTheory.UPoinc.GFib.labelled_lattices_equiv | (intros; apply GlobalTheory.UPoinc.GFib.labelled_lattices_equiv <;> assumption)
end
end
