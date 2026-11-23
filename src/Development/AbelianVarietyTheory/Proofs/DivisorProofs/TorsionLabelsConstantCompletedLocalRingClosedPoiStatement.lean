module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NsmulEqZeroOfCast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionLabelClosedPointStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelEqWeilPairingToricTorsionPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

namespace GlobalTheory.Poinc.UTestLabel

theorem char_eq_weil_of_label : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ∃ sg : ℤˣ, ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (b : S.Gam), τ' ^ (S.r * S.N) = 1 → (∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left) → ∀ (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β → ((τ' (Multiplicative.ofAdd β) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * ((sg : ℤ) • eStd S.g _ b a).val))) := by
  intro o Ω _ _ _ S ρ
  refine ⟨1, ?_⟩
  intro p _ y₀ u l τ' b hτ hb a β hβ
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hk : 1 ≤ S.r * S.N :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  haveI : CharZero u.V := CharZero.mk (fun m n hmn => by
    have e0 := congrArg ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))) hmn
    simpa only [map_natCast, Nat.cast_inj] using e0)
  obtain ⟨f, hf1, -, -, -, hfW⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hk
  obtain ⟨pk, x, hpkx, hxo⟩ := GlobalTheory.Poinc.exists_qkPt_of_utest o Ω S ρ p y₀ u a
  obtain ⟨q, hqy, hqt⟩ := exists_qkPt_tor u.D.tau_bimult τ' hτ
  have hqx : QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (f q) := (hf1 q (f q)).2 rfl
  have hqo := hb q (f q) hqy hqt hqx
  have hpk : x = f pk := (hf1 pk x).1 hpkx
  have W₁ := weilQkIs_tor hG q pk hqy hqt
  have W₂ := (hfW q pk (τ' (Multiplicative.ofAdd pk.y))).1 W₁
  have := ρ.P.isAb.comm
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    have e1 : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK =
        spMap ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp u.yK) := (spMap_comp _ _).symm
    rw [e1, u.fac]
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) :=
    S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h
    (ρ.weil b a (c₀ ^ (eStd S.g _ b a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb
    (TFK (R := u.V) (PadicAlgCl p)) _ (f q) (f pk) (h ≫ ρ.pt b) (h ≫ ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB W₂ W₃)
    have e' := congrArg Units.val e
    simp only [MonoidHom.coe_coe, Units.coe_map, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec,
      RingHom.toMonoidHom_eq_coe] at e'
    have hq : (QuotientAddGroup.mk β : u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range) =
        QuotientAddGroup.mk pk.y := hβ.symm.trans (l.yy_eq a pk x hpkx hxo)
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 (QuotientAddGroup.eq.1 hq)
    have hpy : pk.y = β + (S.r * S.N) • m := by
      rw [nsmulAddMonoidHom_apply] at hm
      rw [hm]; abel
    have hτm : τ' (Multiplicative.ofAdd ((S.r * S.N) • m)) = 1 := by
      rw [ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    rw [hpy, ofAdd_add, map_mul, hτm, _root_.mul_one] at e'
    rw [e', Units.val_one, one_smul, ← map_pow, ← pow_mul]
  · show h.left ≫ (ρ.pt b).left = _
    rw [hh, hqo]
  · show h.left ≫ (ρ.pt a).left = _
    rw [hh, ← hxo, hpk]

end GlobalTheory.Poinc.UTestLabel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelEqWeilPairingToricTorsionPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.torsionLabel_eq_weilPairing_toricTorsionPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ∃ sg : ℤˣ, ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (b : S.Gam), τ' ^ (S.r * S.N) = 1 → (∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left) → ∀ (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β → ((τ' (Multiplicative.ofAdd β) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * ((sg : ℤ) • eStd S.g _ b a).val))) := by
  first | exact @GlobalTheory.Poinc.UTestLabel.char_eq_weil_of_label | exact GlobalTheory.Poinc.UTestLabel.char_eq_weil_of_label | (intros; apply GlobalTheory.Poinc.UTestLabel.char_eq_weil_of_label <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsConstantCompletedLocalRingClosedPoi

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.LabConst

theorem mk_eq_of_forall_char {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ) (β₁ β₂ : X)
    (h : ∀ lam : X →+ ZMod k, lam β₁ = lam β₂) :
    (QuotientAddGroup.mk β₁ : X ⧸ (nsmulAddMonoidHom k : X →+ X).range) = QuotientAddGroup.mk β₂ := by
  let b := Module.Free.chooseBasis ℤ X
  rw [QuotientAddGroup.eq]
  have hc : ∀ i, (k : ℤ) ∣ b.repr (-β₁ + β₂) i := by
    intro i
    have h1 := h ((Int.castAddHom (ZMod k)).comp (b.coord i).toAddMonoidHom)
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply, Int.coe_castAddHom] at h1
    simp only [map_add (f := _), map_neg, Finsupp.add_apply, Finsupp.neg_apply, Int.cast_add, Int.cast_neg, h1, neg_add_cancel]
  choose c hc using hc
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [nsmulAddMonoidHom_apply]
  conv_rhs => rw [← b.sum_repr (-β₁ + β₂)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, natCast_zsmul]

def qmap {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) :
    X ⧸ (nsmulAddMonoidHom k : X →+ X).range →+ Y ⧸ (nsmulAddMonoidHom k : Y →+ Y).range :=
  QuotientAddGroup.map _ _ e.toAddMonoidHom (by
    rintro _ ⟨z, rfl⟩
    exact ⟨e z, by simp⟩)

theorem qmap_mk {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (β : X) :
    qmap k e (QuotientAddGroup.mk β) = QuotientAddGroup.mk (e β) := rfl

theorem mk_symm_eq_iff {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (β : Y) (α : X) :
    (QuotientAddGroup.mk (e.symm β) : X ⧸ (nsmulAddMonoidHom k : X →+ X).range) = QuotientAddGroup.mk α ↔
      (QuotientAddGroup.mk β : Y ⧸ (nsmulAddMonoidHom k : Y →+ Y).range) = QuotientAddGroup.mk (e α) := by
  rw [QuotientAddGroup.eq, QuotientAddGroup.eq]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨e z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← map_nsmul, hz, map_add (f := _), map_neg, AddEquiv.apply_symm_apply]
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← map_nsmul, hz, map_add (f := _), map_neg, AddEquiv.symm_apply_apply]

end GlobalTheory.Poinc.LabConst

namespace GlobalTheory.Poinc.LabConst

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) a α, yy a = QuotientAddGroup.mk α ↔ l.yy a = QuotientAddGroup.mk (ε α) := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨sg, hread⟩ := GlobalTheory.T.torsionLabel_eq_weilPairing_toricTorsionPoint o' Ω S ρ
  have hglob := GlobalTheory.T.exists_toricTorsion_label_closed_point o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  choose bOf hbOf using hglob
  have hk0 : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have hζk : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (by positivity) (by ring)
  have key : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y →
      spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ →
      ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε →
      ∀ (l : u.Lab) (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β →
      ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), lam (ε.symm β) = ((sg : ℤ) • eStd S.g _ (bOf lam) a) := by
    intro p _ y ev hCen hev y₀ hAt u ε hbc l a β hβ lam
    haveI : IsDomain o' := (ArithBase.ded (o := o') (Ω := Ω)).toIsDomain
    set f : o' →+* PadicAlgCl p := y₀.comp (algebraMap o' S.R) with hf
    have hω : IsPrimitiveRoot (f (S.ζ ^ (S.r * S.N))) (S.r * S.N) := by
      have h1 := hζk.isRoot_cyclotomic hk0
      have h2 := h1.map (f := f)
      rw [Polynomial.map_cyclotomic] at h2
      exact (Polynomial.isRoot_cyclotomic_iff_charZero hk0).1 h2
    set ω : (PadicAlgCl p)ˣ := (hω.isUnit hk0.ne').unit with hωdef
    have hωk : ω ^ (S.r * S.N) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hωdef, IsUnit.unit_spec, hω.pow_eq_one, Units.val_one])
    let ψ : ZMod (S.r * S.N) →+ Additive (PadicAlgCl p)ˣ :=
      ZMod.lift (S.r * S.N) ⟨zmultiplesHom (Additive (PadicAlgCl p)ˣ) (Additive.ofMul ω), by
        rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hωk, ofMul_one]⟩
    have hψ : ∀ z : ZMod (S.r * S.N), ((Additive.toMul (ψ z) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = f (S.ζ ^ (S.r * S.N)) ^ z.val := by
      intro z
      haveI : NeZero (S.r * S.N) := NeZero.of_pos hk0
      conv_lhs => rw [← ZMod.intCast_zmod_cast z]
      rw [ZMod.lift_coe]
      simp only [Subtype.coe_mk, zmultiplesHom_apply, toMul_zsmul, toMul_ofMul, ZMod.cast_eq_val, zpow_natCast]
      rw [Units.val_pow_eq_pow_val, hωdef, IsUnit.unit_spec]
    let τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
      AddMonoidHom.toMultiplicativeLeft (ψ.comp (lam.comp ε.symm.toAddMonoidHom))
    have hτ : ∀ χ' : u.D.toPre.X, ((τ' (Multiplicative.ofAdd χ') : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
        f (S.ζ ^ (S.r * S.N)) ^ (lam (ε.symm χ')).val := fun χ' => hψ _
    have hτk : τ' ^ (S.r * S.N) = 1 := by
      refine MonoidHom.ext fun χ' => Units.ext ?_
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one]
      obtain ⟨χ, rfl⟩ : ∃ χ, Multiplicative.ofAdd χ = χ' := ⟨Multiplicative.toAdd χ', rfl⟩
      rw [hτ, ← pow_mul, Nat.mul_comm _ (S.r * S.N), pow_mul, hω.pow_eq_one, one_pow]
    have hglobτ : ∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
        y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val) := by
      intro χ
      rw [hτ, AddEquiv.symm_apply_apply]
      simp only [hf, RingHom.comp_apply, map_pow, pow_mul]
    have hpt := hbOf lam p y ev hCen hev y₀ hAt u ε hbc τ' hglobτ
    have hv := hread p y₀ u l τ' (bOf lam) hτk hpt a β hβ
    have hv' : f (S.ζ ^ (S.r * S.N)) ^ (lam (ε.symm β)).val =
        f (S.ζ ^ (S.r * S.N)) ^ (((sg : ℤ) • eStd S.g _ (bOf lam) a).val) := by
      rw [← hτ, hv]
      simp only [hf, RingHom.comp_apply, map_pow, pow_mul]
    exact ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hv')
  have hconst : ∀ (p₁ : ℕ) [Fact p₁.Prime] (y₁ : Sp (OO p₁) ⟶ M.Z) (ev₁ : R →+* OO p₁), M.Cen U₀ x y₁ →
      spMap ev₁ ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y₁ → ∀ y₀₁ : S.R →+* PadicAlgCl p₁, S.At M y₁ y₀₁ →
      ∀ (u₁ : ρ.UTest p₁ y₀₁) (ε₁ : D.toPre.X ≃+ u₁.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev₁ u₁ ε₁ →
      ∀ (l₁ : u₁.Lab) (p₂ : ℕ) [Fact p₂.Prime] (y₂ : Sp (OO p₂) ⟶ M.Z) (ev₂ : R →+* OO p₂), M.Cen U₀ x y₂ →
      spMap ev₂ ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y₂ → ∀ y₀₂ : S.R →+* PadicAlgCl p₂, S.At M y₂ y₀₂ →
      ∀ (u₂ : ρ.UTest p₂ y₀₂) (ε₂ : D.toPre.X ≃+ u₂.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev₂ u₂ ε₂ →
      ∀ (l₂ : u₂.Lab) (a : S.Gam), qmap (S.r * S.N) ε₁.symm (l₁.yy a) = qmap (S.r * S.N) ε₂.symm (l₂.yy a) := by
    intro p₁ _ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ p₂ _ y₂ ev₂ hCen₂ hev₂ y₀₂ hAt₂ u₂ ε₂ hbc₂ l₂ a
    obtain ⟨β₁, hβ₁⟩ := QuotientAddGroup.mk_surjective (l₁.yy a)
    obtain ⟨β₂, hβ₂⟩ := QuotientAddGroup.mk_surjective (l₂.yy a)
    rw [← hβ₁, ← hβ₂, qmap_mk, qmap_mk]
    refine mk_eq_of_forall_char _ _ _ fun lam => ?_
    rw [key p₁ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ a β₁ hβ₁.symm lam,
      key p₂ y₂ ev₂ hCen₂ hev₂ y₀₂ hAt₂ u₂ ε₂ hbc₂ l₂ a β₂ hβ₂.symm lam]
  by_cases hex : ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p) (_ : M.Cen U₀ x y)
      (_ : spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y) (y₀ : S.R →+* PadicAlgCl p) (_ : S.At M y y₀)
      (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X) (_ : GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε), Nonempty u.Lab
  · obtain ⟨p₁, hp₁, y₁, ev₁, hCen₁, hev₁, y₀₁, hAt₁, u₁, ε₁, hbc₁, ⟨l₁⟩⟩ := hex
    refine ⟨(qmap (S.r * S.N) ε₁.symm).comp l₁.yy, ?_⟩
    intro p _ y ev hCen hev y₀ hAt u ε hbc l a α
    rw [AddMonoidHom.comp_apply, hconst p₁ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ p y ev hCen hev y₀ hAt u ε hbc l a]
    obtain ⟨β, hβ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [← hβ, qmap_mk]
    exact mk_symm_eq_iff _ ε β α
  · refine ⟨0, ?_⟩
    intro p _ y ev hCen hev y₀ hAt u ε hbc l
    exact absurd ⟨p, inferInstance, y, ev, hCen, hev, y₀, hAt, u, ε, hbc, ⟨l⟩⟩ hex

end GlobalTheory.Poinc.LabConst

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsConstantCompletedLocalRingClosedPoiStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.torsionLabels_constant_completedLocalRing_closedPoint : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) a α, yy a = QuotientAddGroup.mk α ↔ l.yy a = QuotientAddGroup.mk (ε α) := by
  first | exact @GlobalTheory.Poinc.LabConst.main | exact GlobalTheory.Poinc.LabConst.main | (intros; apply GlobalTheory.Poinc.LabConst.main <;> assumption)
end
end
