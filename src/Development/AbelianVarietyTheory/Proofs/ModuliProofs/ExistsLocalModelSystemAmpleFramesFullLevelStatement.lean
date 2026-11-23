module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseModelSemiAbelianStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbedStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCoverStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDescentCoefficientField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelRaises

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LocalModelExists

theorem exists_model_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (b : RZ H (n * l₀.M) 1 →+* O), 0 < n → l₀.Dvd l → IsDedFrac β → IsInc (RZ H (n * l₀.M) 1).subtype (c.F.val.toRingHom.comp β) b → ∃ Y : Model (Xo l) c β, Raises B Y := by
  intro L1 L2 L3 E _ _ _ H D Xo n N T hN l₀ l B c O _ β b hn hd hβ hb
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ _ (Xo l).s
    (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s)
    (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) rfl rfl
    (by simp [spMap]) (Xo l).univ
  obtain ⟨k, r, ν, hr, hk, hlev, hfin, -, -⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L1 L2 L3 E H D Xo hN l₀ l c o m0 hd
  have hpos : 0 < n * l₀.M := Nat.mul_pos hn (by have := l₀.three_le; omega)
  have hB : IsDedFrac B.β := by
    have aux : ∀ a : ℕ, l₀.A = a → a = 1 → ∀ β₀ : RZ H (n * l₀.M) a →+* KA l₀,
        IsInc (RZ H (n * l₀.M) a).subtype (KA l₀).val.toRingHom β₀ → IsDedFrac β₀ := by
      intro a ha h1
      subst ha
      exact (GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l₀ (n * l₀.M) 0 hpos (by simp [h1])).2.2
    exact aux 1 B.A_one rfl B.β B.β_inc
  have hcomp : β.comp b = k.comp B.β := by
    refine RingHom.ext fun x => Subtype.ext ?_
    exact (hb x).trans ((hk (B.β x)).trans (B.β_inc x)).symm
  have hsm : Smooth (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    infer_instance
  have hnorm := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ (Xo l₀).s (Xo l₀).univ.t B.β _ _ _
    (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) o.t β B.C b k r hr ν hB hβ hcomp
    hnorm hfin
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, o, m0, C.m, C.ab_gen⟩,
    b, r, ν, hb, hlev, hC⟩

end GlobalTheory.LocalModelExists
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.SystemAmple

theorem exists_system_ampFrames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∃ S : System Xo, ∀ i, ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames (S.T i).t.G (S.T i).t.PP.L ((S.n i ^ k) ^ 2)) := by
  intro hx h1 h2 h3 htop E _ _ _ H D Xo hpq hN
  classical
  obtain ⟨⟨n₀, n₁, a₀, a₁, hne⟩, -⟩ := GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level E H
  let n : Bool → ℕ := fun i => cond i n₁ n₀
  have aux : ∀ i, AuxiliaryInertOddPrime H (n i) := fun i => by cases i <;> assumption
  choose J k T hJ hamp using fun i => htop E H D hpq Xo (n i) (aux i)
  let B : ∀ i (l₀ : Level H), l₀.A = 1 → BaseModel (T i) l₀ := fun i l₀ h =>
    (GlobalTheory.T.exists_base_model_semiAbelian hx h1 h2 h3 E H D Xo hpq hN (n i) (J i) (T i) l₀ (aux i) (hJ i) h).some
  let ch : ℕ → Bool := fun p => decide (n₀ = p)
  have ch_ne : ∀ p, n (ch p) ≠ p := by
    intro p
    by_cases h : n₀ = p
    · have : ch p = true := by simp [ch, h]
      rw [this]
      exact fun h' => hne (h.trans h'.symm)
    · have : ch p = false := by simp [ch, h]
      rw [this]
      exact h
  have key : ∀ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (i : Idx H p),
      ∃ Y : Model (Xo i.l) i.c (i.c.V W).subtype, ∃ (l₀ : Level H) (h : IsPrimeToPart l₀ i.l p),
        Raises (B (ch p) l₀ h.1) Y := by
    intro p W hp hW i
    obtain ⟨hex, hsp, -⟩ := GlobalTheory.Models.primeToPart_spec E H p hp
    obtain ⟨l₀, h⟩ := hex i.l i.good
    obtain ⟨hdvd, hcop, -⟩ := hsp i.l l₀ h
    obtain ⟨hded, -, hb⟩ := (GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW
    have hnp : (n (ch p)).Coprime p := (Nat.coprime_primes (aux _).1 hp).2 (ch_ne p)
    have hz : zeta 1 ∈ i.c.F := by
      have : zeta 1 = 1 := by simp [zeta]
      rw [this]; exact one_mem _
    obtain ⟨b, hbi⟩ := hb (n (ch p) * l₀.M) 1 (Nat.Coprime.mul_left hnp hcop) one_pos hz
    obtain ⟨Y, hY⟩ := GlobalTheory.LocalModelExists.exists_model_raises h1 h2 h3 E H D Xo _ _ (T (ch p)) hN l₀ i.l
      (B (ch p) l₀ h.1) i.c _ (i.c.V W).subtype b (aux _).1.pos hdvd hded hbi
    exact ⟨Y, l₀, h, hY⟩
  choose Y hY using key
  exact ⟨⟨n, J, aux, hJ, T, B, ch, ch_ne, Y, hY⟩, fun i => ⟨k i, hamp i⟩⟩

end GlobalTheory.SystemAmple
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∃ S : System Xo, ∀ i, ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames (S.T i).t.G (S.T i).t.PP.L ((S.n i ^ k) ^ 2)) := by
  first | exact @GlobalTheory.SystemAmple.exists_system_ampFrames | exact GlobalTheory.SystemAmple.exists_system_ampFrames | (intros; apply GlobalTheory.SystemAmple.exists_system_ampFrames <;> assumption)
end
end
