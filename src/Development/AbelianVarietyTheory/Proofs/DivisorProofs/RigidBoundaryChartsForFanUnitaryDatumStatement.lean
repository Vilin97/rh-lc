module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VanishingIdealComapOfIsOpenImmersion
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationSmoothSncBoundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationIsModelOfChartsStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToroidalSeparationOfBaseStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionCompIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.Member

theorem isEtaleCompletion_comp_bijective' {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion φ) : IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

theorem isEtaleCompletion_stalkClosedPointTo_comp_iso : ∀ {R : Type} [CommRing R] [IsLocalRing R] {X Y : Scheme.{0}} (ξ : Spec (CommRingCat.of R) ⟶ X) (g : X ⟶ Y) [IsIso g], IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → IsEtaleCompletion (Scheme.stalkClosedPointTo (ξ ≫ g)).hom := by
  intro R _ _ X Y ξ g _ h
  have hb : Function.Bijective (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp]
  exact isEtaleCompletion_comp_bijective' _ hb _ h

end GlobalTheory.Member
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartsOfUpre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem inv_apply_self {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) : inv f (f x) = x := by
  rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl

theorem chart_of_data {φ : InvFun (𝓞 E)} (Y : Model Xo c (RingHom.id c.F)) (BD' : EffCartierData Y.X) (d : ℕ)
    (x : gen Y) {k : Type} [Field k] {m e : ℕ} (ξ' : Sp (ChartRing k m e) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m e)))
    (P : PELUnif (maximalIdeal (ChartRing k m e)) t) (n : ℕ) (h : n = m) (s : Fin n → ChartRing k m e)
    (hs : ∀ i, s i = bdParam k m e (Fin.cast h i)) (δ : Fin n → LinearMap.BilinForm ℤ P.D.toPre.X) (a : Fin n → ℕ)
    (hx : ξ' (closedPoint _) = x) (het : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom)
    (hid : idlAlong (genBdIdeal Y) ξ' = Ideal.span {∏ i, s i})
    (hset : ∀ p : Sp (ChartRing k m e), ξ' p ∈ genBd Y ↔ ∏ i, s i ∈ p.asIdeal)
    (hsab : Nonempty (SABMap t Y.t (ξ' ≫ genι Y)))
    (hmono : IsMonomial P.D.toPre s (fun i => (l.M' : ℤ) • δ i))
    (hrank : Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q) (hcone : IsCone H.bar φ δ)
    (ha : ∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • δ i))
    (hBD : idlAlong BD'.idealSheaf (ξ' ≫ genι Y) = Ideal.span {∏ i, s i ^ a i})
    (hrig : GlobalTheory.RigChart.IsRigid P.D.toPre s (fun i => (l.M' : ℤ) • δ i)) :
    GlobalTheory.MumfordChart.HasChartOf φ Y BD' d x ∧ GlobalTheory.RigChart.HasRigidChart Y x := by
  subst h
  obtain rfl : s = bdParam k n e := funext fun i => by simpa using hs i
  have hmem : ∀ i, (l.M' : ℤ) • δ i ∈ levelForms H l.M' P.D.toPre.X := fun i =>
    (mem_levelForms_iff_smul (GlobalTheory.MumfordChart.level_ne_zero l)).2
      ⟨δ i, (balForms_eq_levelForms H P.D.toPre.X) ▸ hcone.mem i, rfl⟩
  let gam : Fin n → levelForms H l.M' P.D.toPre.X := fun i => ⟨(l.M' : ℤ) • δ i, hmem i⟩
  have hgam : ∀ i, (gam i : LinearMap.BilinForm ℤ P.D.toPre.X) = (l.M' : ℤ) • δ i := fun _ => rfl
  have hpb : IsPartOfBasis gam := hcone.isPartOfBasis_level (GlobalTheory.MumfordChart.level_ne_zero l) hgam
  exact ⟨⟨k, _, n, e, ξ', t, P, gam, δ, a, hx, het, hid, fun p => (hset p).trans Iff.rfl, hsab, hmono, hrank, hcone, hgam,
      ha, hBD⟩,
    ⟨k, _, n, e, ξ', t, P, gam, hx, het, hid, hset, hsab, hmono, hpb, hrig⟩⟩

end GlobalTheory.UChartOf

namespace GlobalTheory.UChartOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem charts_of_upre {φ : InvFun (𝓞 E)} {S : Scheme.{0}} {j : Xo.XF c ⟶ S} [IsOpenImmersion j]
    {BD : EffCartierData S} {d : ℕ} (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S) (hj : Y.j ≫ ε.hom = j)
    (hsab : ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C →
      ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)))
    (hpre : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) (x : gen Y) (hx : x ∈ genBd Y) :
    GlobalTheory.MumfordChart.HasChartOf φ Y (BD.pull ε.hom (BD.keepsRegular_of_flat _)) d x ∧
      GlobalTheory.RigChart.HasRigidChart Y x := by
  let π : gen Y ⟶ S := genι Y ≫ ε.hom
  have hjQ : Y.jQ ≫ π = j := by
    simp only [π, ← Category.assoc]
    exact hj
  have hrange : ∀ w : gen Y, w ∈ Set.range Y.jQ ↔ π w ∈ Set.range j := by
    intro w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← hjQ]; rfl⟩
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have : π (Y.jQ z) = π w := by rw [← hz, ← hjQ]; rfl
      rw [← inv_apply_self π (Y.jQ z), this, inv_apply_self]
  have hx' : π x ∉ Set.range j := fun h => hx ((hrange x).2 h)
  obtain ⟨k, _, m, e, C, ξ, a, htaut, hy, hcl, het, hbd, hset, ha, hBD⟩ := hpre (π x) hx'
  obtain ⟨hm, hs, -, -, hrig, -, -⟩ := id htaut
  let ξ' : Sp (ChartRing k m e) ⟶ gen Y := ξ ≫ inv π
  have hξ : ξ' ≫ π = ξ := by simp [ξ']
  have hξg : ξ' ≫ genι Y = ξ ≫ ε.inv := by
    simp only [ξ', π, IsIso.inv_comp, IsIso.Iso.inv_hom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hvan : (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl).comap π = genBdIdeal Y :=
    GlobalTheory.vanishingIdeal_comap_of_isOpenImmersion (gen Y) S π _ (genBd Y) fun w =>
      (not_congr (hrange w)).trans Iff.rfl
  refine chart_of_data Y _ d x ξ' C.t C.P C.m hm C.s hs C.δ a ?_ ?_ ?_ ?_ ?_ C.mono C.rank C.cone ha ?_ hrig.1
  · change inv π (ξ (closedPoint _)) = x
    rw [hcl, inv_apply_self]
  · exact GlobalTheory.Member.isEtaleCompletion_stalkClosedPointTo_comp_iso ξ (inv π) het
  · rw [← hvan, GlobalTheory.TorRef.idlAlong_comap, hξ]
    exact hbd
  · intro p
    rw [mem_genBd, hrange, ← Scheme.Hom.comp_apply, hξ, hset p, not_not]
  · rw [hξg]
    exact hsab C htaut ξ hy
  · rw [EffCartierData.idealSheaf_pull, GlobalTheory.TorRef.idlAlong_comap, hξg, Category.assoc, ε.inv_hom_id,
      Category.comp_id]
    exact hBD

end GlobalTheory.UChartOf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationSmoothSncBoundaryStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.toroidalCompactification_smooth_snc_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → SmoothOfRelativeDimension Dw.dim (π ≫ zs) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) := by
  first | exact @GlobalTheory.UChartSmooth.smooth_and_snc | exact GlobalTheory.UChartSmooth.smooth_and_snc | (intros; apply GlobalTheory.UChartSmooth.smooth_and_snc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanOfUnitarySeparation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartJoin

theorem rigidForFan_of_uStB : UStB → GlobalTheory.RigChart.RigidForFan := by
  intro hU E _ _ _ H Dw hpq φ hpol hnsi l Xo c
  obtain ⟨Z, zs, i, OZ, N, d, J, S, π, j, BD, hUP, hSep⟩ := hU E H Dw hpq φ hpol hnsi l Xo c
  obtain ⟨⟨-, -, -, -, -, hOZ, -⟩, ⟨hN, hdet⟩, -, ⟨hd, hJ, -⟩, ⟨-, -, hj, -, hji, -, hBD, -⟩, k₀, hamp⟩ := id hUP
  haveI := hj
  have hpre := GlobalTheory.T.exists_tripleChart_unitary_boundary_point Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep
  obtain ⟨Y, ε, hYj, hYs, hsab⟩ := GlobalTheory.T.unitary_compactification_isModel_of_charts Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep hpre
  obtain ⟨hsm, hsnc⟩ := GlobalTheory.T.toroidalCompactification_smooth_snc_boundary Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep hpre
  have hch := fun x hx => GlobalTheory.UChartOf.charts_of_upre Y ε hYj hsab hpre x hx
  have hYi : Y.j ≫ ε.hom ≫ π = i := by rw [← Category.assoc, hYj, hji]
  refine ⟨Y, BD.pull ε.hom (BD.keepsRegular_of_flat _), d, N * max k₀ 1, hd, ?_, ?_, ?_, ?_, fun x hx => (hch x hx).1, ?_,
    fun x hx _ => (hch x hx).2⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  ·
    have h2 : genStr Y ≫ spMap (RingHom.id c.F) = genStr Y := by
      rw [show spMap (RingHom.id c.F) = 𝟙 (Sp c.F) by simp [spMap]]
      exact Category.comp_id _
    have e : genStr Y = (genι Y ≫ ε.hom) ≫ (π ≫ zs) := by
      rw [← h2, ← pullback.condition]
      exact (congrArg (genι Y ≫ ·) hYs).trans (by simp only [Category.assoc])
    rw [e]
    have := smoothOfRelativeDimension_comp (n := 0) (m := Dw.dim) (genι Y ≫ ε.hom) (π ≫ zs)
    rwa [zero_add] at this
  ·
    refine GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso (genι Y ≫ ε.hom) j.opensRange.compl (genBd Y) (fun a => ?_) hsnc
    rw [mem_genBd]
    show a ∉ Set.range Y.jQ ↔ (genι Y ≫ ε.hom) a ∉ Set.range j
    refine not_congr ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← hYj]; rfl⟩
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have h1 : (genι Y ≫ ε.hom) (Y.jQ z) = (genι Y ≫ ε.hom) a := by
        rw [← hz, ← hYj]; rfl
      rw [← GlobalTheory.UChartOf.inv_apply_self (genι Y ≫ ε.hom) (Y.jQ z), h1, GlobalTheory.UChartOf.inv_apply_self]
  ·
    intro x hx hab
    rw [EffCartierData.idealSheaf_pull, hBD, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.support_comap] at hx
    obtain ⟨g, rfl⟩ : ∃ g : gen Y, genι Y g = x := ⟨inv (genι Y) x, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have hg : g ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hab
    obtain ⟨z, rfl⟩ := hg
    refine hJ _ hx ⟨z, ?_⟩
    rw [← hYi]
    rfl
  ·
    intro hL
    have hk : k₀ ≤ max k₀ 1 := le_max_left _ _
    have isLB {X : Scheme} (D : EffCartierData X) : D.lb.IsLB := by
      refine { cover := D.cover, g_self := ?_, cocycle := ?_ }
      · intro i
        exact Units.ext (D.eq_trans_on i i le_rfl le_rfl (c := 1) (_root_.one_mul _).symm).symm
      · intro i j k
        have hi : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i := inf_le_left.trans inf_le_left
        have hj : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j := inf_le_left.trans inf_le_right
        have hk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U k := inf_le_right
        refine Units.ext (D.eq_trans_on i k hi hk ?_)
        rw [D.trans_spec_on i j hi hj, D.trans_spec_on j k hj hk, ← _root_.mul_assoc]
        rfl
    have hBL := isLB BD
    have hL' := isLB (BD.pull ε.hom (BD.keepsRegular_of_flat _))
    have hA := (hamp _ hk).pull_of_isAffineHom ε.hom
    have hAS : (CechPic.tens (lbPow (OZ.pull π) (max k₀ 1)) (CechPic.dual BD.lb)).IsLB :=
      CechPic.isLB_tens (isLB_lbPow (LB.isLB_pull hOZ π) _) (CechPic.isLB_dual hBL)
    have hP : (GlobalTheory.TorRef.polOf Y (N * max k₀ 1) (BD.pull ε.hom (BD.keepsRegular_of_flat _))).IsLB :=
      CechPic.isLB_tens (isLB_lbPow hL _) (CechPic.isLB_dual hL')
    refine hA.of_lbIso hP ((CechPic.cls_eq_iff hP (LB.isLB_pull hAS ε.hom)).1 ?_)
    have e1 : CechPic.cls _ (LB.isLB_pull hOZ (ε.hom ≫ π)) = N • CechPic.cls _ hL := by
      rw [(CechPic.cls_eq_iff _ (isLB_lbPow hL N)).2 (hdet Y (ε.hom ≫ π) hYi hL), CechPic.cls_lbPow hL]
    have e2 : CechPic.cls _ hL' = CechPic.pull ε.hom (CechPic.cls _ hBL) := by
      rw [(CechPic.cls_eq_iff _ (LB.isLB_pull hBL _)).2 (BD.lbIso_pull _ _), CechPic.cls_pull hBL]
    rw [CechPic.cls_pull hOZ, CechPic.pull_comp] at e1
    refine (CechPic.cls_tens (isLB_lbPow hL _) (CechPic.isLB_dual hL') hP).trans ?_
    rw [CechPic.cls_pull hAS ε.hom,
      CechPic.cls_tens (isLB_lbPow (LB.isLB_pull hOZ π) _) (CechPic.isLB_dual hBL),
      CechPic.cls_lbPow hL, CechPic.cls_lbPow (LB.isLB_pull hOZ π), CechPic.cls_dual hL', CechPic.cls_dual hBL,
      CechPic.cls_pull hOZ π, e2, map_add, map_nsmul, map_neg, e1, mul_nsmul]

end GlobalTheory.UChartJoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanOfUnitarySeparationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rigidBoundaryChartsForFan_of_unitarySeparation : UStB → GlobalTheory.RigChart.RigidForFan := by
  first | exact @GlobalTheory.UChartJoin.rigidForFan_of_uStB | exact GlobalTheory.UChartJoin.rigidForFan_of_uStB | (intros; apply GlobalTheory.UChartJoin.rigidForFan_of_uStB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanUnitaryDatum

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigChart

theorem rigidForFan_holds : GlobalTheory.RigChart.RigidForFan :=
  GlobalTheory.T.rigidBoundaryChartsForFan_of_unitarySeparation GlobalTheory.T.unitaryToroidalSeparation_of_base

end GlobalTheory.RigChart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanUnitaryDatumStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rigidBoundaryChartsForFan_unitaryDatum : GlobalTheory.RigChart.RigidForFan := by
  first | exact @GlobalTheory.RigChart.rigidForFan_holds | exact GlobalTheory.RigChart.rigidForFan_holds | (intros; apply GlobalTheory.RigChart.rigidForFan_holds <;> assumption)
end
end
