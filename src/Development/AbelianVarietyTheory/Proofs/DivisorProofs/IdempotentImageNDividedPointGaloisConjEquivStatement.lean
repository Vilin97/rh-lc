module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointCharactersGaloisFixedOfRationalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageBasePointRationalFractionField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatBase

theorem nsmul_b' {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, rfl⟩ := H
  have : ∀ i : Fin (k + 1), (gs i).b = g.b ^ (i : ℕ) := fun i => by
    induction i using Fin.induction with
    | zero => rw [Fin.val_zero, pow_zero]; exact h0.1
    | succ i ih => rw [(hs i).1, ih, Fin.val_succ, pow_succ]; rfl
  exact this _

theorem pow_comp' {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem ratBase : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → ∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ ζ _ Q e hD hT D' F p₀ p hy hg
  haveI := F.inc_hom
  haveI := F.pr_hom
  set L := AlgebraicClosure (FractionRing R)
  set a := F.xp p₀.y
  let b₀ : TF (R := R) L ⟶ Q.B := p₀.g.b ≫ F.pr
  have hpb : p.g.b = b₀ ≫ F.inc := by rw [hg.1, ← F.pr_inc, Category.assoc]
  obtain ⟨h, h1, h2⟩ := p₀.eq
  have hn1 : p₀.g.b ^ n = toUnit _ ≫ D'.toPre.c p₀.y := (nsmul_b' h1).symm.trans h2.1
  have hcpr : D'.toPre.c p₀.y ≫ F.pr = Q.c a := by
    have h3 : D'.toPre.c p₀.y ≫ F.pr ≫ F.inc = Q.c a ≫ F.inc := by
      rw [F.pr_inc, ← F.o.c_lin, ← F.xi_xp, F.c_xi]
    have h4 := congrArg (· ≫ F.pr) h3
    simpa only [Category.assoc, F.inc_pr, Category.comp_id] using h4
  have hb₀ : b₀ ^ n = toUnit _ ≫ Q.c a := by
    rw [← pow_comp', hn1, Category.assoc, hcpr]
  obtain ⟨β, β₂, w, hpb', hsq, hw, hc, htau⟩ := hD

  have hcomm : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 (Sp R) ≫ spMap iw := by
    rw [Category.assoc, Over.w (T.c₀ (e a))]; simp
  let d : 𝟙_ (Over (Sp R)) ⟶ Q.B := Over.homMk (hpb'.1.lift _ _ hcomm) (by simpa using hpb'.1.lift_snd _ _ hcomm)
  have hd : d.left ≫ β = spMap iw ≫ (T.c₀ (e a)).left := hpb'.1.lift_fst _ _ hcomm
  have hdn : d ^ n = Q.c a := by
    refine Over.OverMorphism.ext (hpb'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [GlobalTheory.FrameMove.pow_comm hpb' hd n, hc a]
    congr 2
    have key : ∀ k : ℕ, T.c₀ ((k : ℤ) • e a) = T.c₀ (e a) ^ k := fun k => by
      induction k with
      | zero => rw [Nat.cast_zero, zero_smul, pow_zero, T.c₀_zero]
      | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, T.c₀_add, ih, pow_succ]
    exact (key n).symm

  let κ := algebraMap (FractionRing R) L
  let x : TF (R := R) L ⟶ Q.B := b₀ * (toUnit _ ≫ d)⁻¹
  have hx : x ^ n = 1 := by
    simp only [x]
    rw [mul_pow, inv_pow, hb₀, ← GlobalTheory.FrameMove.comp_pow, hdn, mul_inv_cancel]
  obtain ⟨x₀, hx₀⟩ := hT L κ x hx
  let ρ : TF (R := R) L ⟶ TK R := Over.homMk (spMap κ) rfl
  have hxρ : x = ρ ≫ x₀ := Over.OverMorphism.ext hx₀
  have hb₀' : b₀ = ρ ≫ (x₀ * (toUnit _ ≫ d)) := by
    rw [MonObj.comp_mul, ← hxρ, ← Category.assoc, toUnit_unique (ρ ≫ toUnit _) (toUnit _)]
    simp only [x, inv_mul_cancel_right]
  let σ : TF (R := R) (FractionRing R) ⟶ TK R := Over.homMk (jFK (R := R) (FractionRing R)) rfl
  refine ⟨σ ≫ (x₀ * (toUnit _ ≫ d)) ≫ F.inc, ?_⟩
  rw [hpb, hb₀']
  simp only [Over.comp_left]

  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    simp only [jFK, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hσ : σ.left = 𝟙 _ := hj
  rw [hσ, Category.id_comp, Category.assoc]
  rfl

end GlobalTheory.Mum.RatBase
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageBasePointRationalFractionFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.idempotent_image_base_point_rational_fractionField : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → ∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left := by
  first | exact @GlobalTheory.Mum.RatBase.ratBase | exact GlobalTheory.Mum.RatBase.ratBase | (intros; apply GlobalTheory.Mum.RatBase.ratBase <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageNDividedPointGaloisConjEquiv

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalFixQ

theorem eImage_equiv_conj : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p p' : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F A' G' _ _ U' oA oG hSA hOL σ p₀ p p' hy hg hext
  have hB := D'.tau_bimult
  obtain ⟨b, hb⟩ := GlobalTheory.T.idempotent_image_base_point_rational_fractionField T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F p₀ p hy hg
  have hc := GlobalTheory.T.divisionPoint_characters_galoisFixed_of_rational_basePoint T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ p₀ p hy hg ⟨b, hb⟩
  have hσ : σ.toAlgHom.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) =
      algebraMap _ _ := σ.toAlgHom.comp_algebraMap
  have hpp : QkExt σ.toAlgHom.toRingHom p p := by
    refine ⟨rfl, ?_, hc⟩
    rw [hb, ← Category.assoc]
    congr 1
    rw [spMap, spMap, ← Spec.map_comp]
    congr 1
    ext x
    exact (RingHom.congr_fun hσ x).symm
  have hg' : p.g = p'.g :=
    GlobalTheory.TorusExt.gt_ext_val (Over.OverMorphism.ext (hpp.2.1.trans hext.2.1.symm)) fun χ y J hJ =>
      (val_corr hJ (hpp.2.2 χ) _).trans (val_corr hJ (hext.2.2 χ) _).symm
  have hy' : p.y = p'.y := hpp.1.trans hext.1.symm
  have hp : p = p' := by
    obtain ⟨y, g, e⟩ := p
    obtain ⟨y', g', e'⟩ := p'
    obtain rfl : y = y' := hy'
    obtain rfl : g = g' := hg'
    rfl
  rw [← hp]
  exact qk_equiv_refl hB p

end GlobalTheory.Mum.GalFixQ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageNDividedPointGaloisConjEquivStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.idempotent_image_nDividedPoint_galoisConj_equiv : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p p' : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  first | exact @GlobalTheory.Mum.GalFixQ.eImage_equiv_conj | exact GlobalTheory.Mum.GalFixQ.eImage_equiv_conj | (intros; apply GlobalTheory.Mum.GalFixQ.eImage_equiv_conj <;> assumption)
end
end
