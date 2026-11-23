module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloSimple
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EqZeroOfBlockSumEqZero
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.MapEvalRingHomOfPiFamily
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PiSeries
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCycloStatement
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCoprimeDvdSub
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.RhoUnit

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.AlgHomPowerSeriesCoeEqAeval

section

@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem algHom_powerSeries_coe_eq_aeval {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (ρ : PowerSeries O →ₐ[O] PowerSeries S) (r : Polynomial O) :
    ρ (r : PowerSeries O) = Polynomial.aeval (ρ X) r := by
  have h : ρ.comp (Polynomial.coeToPowerSeries.algHom O) = Polynomial.aeval (ρ X) := by
    apply Polynomial.algHom_ext
    simp [Polynomial.coeToPowerSeries.algHom_apply]
  have h2 := congrArg (fun f => f r) h
  simpa [Polynomial.coeToPowerSeries.algHom_apply] using h2

theorem exists_pow_mul_add_polynomial {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    (P : Polynomial O) (hP : P.IsDistinguishedAt (maximalIdeal O)) (k : ℕ) (a : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), a = (P : PowerSeries O) ^ k * q + (r : PowerSeries O) := by
  have hm : (P ^ k).Monic := hP.monic.pow k
  have hne : PowerSeries.map (residue O) ((P ^ k : Polynomial O) : PowerSeries O) ≠ 0 := by
    rw [← Polynomial.polynomial_map_coe, Ne, Polynomial.coe_eq_zero_iff]
    exact (hm.map (residue O)).ne_zero
  obtain ⟨q, r, h⟩ := PowerSeries.exists_isWeierstrassDivision a hne
  refine ⟨q, r, ?_⟩
  rw [← Polynomial.coe_pow]
  exact h.2

theorem rhoUnique : RhoUniqueStatement := by
  intro O S _ _ _ _ _ P hP ρ ρ' hX h0
  have hpoly : ∀ r : Polynomial O, ρ (r : PowerSeries O) = ρ' (r : PowerSeries O) := by
    intro r
    rw [algHom_powerSeries_coe_eq_aeval, algHom_powerSeries_coe_eq_aeval, hX]
  have hdvd : X ∣ ρ (P : PowerSeries O) := by
    rw [PowerSeries.X_dvd_iff, algHom_powerSeries_coe_eq_aeval]
    exact h0
  apply AlgHom.ext
  intro a
  ext n
  obtain ⟨q, r, hqr⟩ := exists_pow_mul_add_polynomial P hP (n + 1) a
  have hd : ρ a - ρ' a = ρ (P : PowerSeries O) ^ (n + 1) * (ρ q - ρ' q) := by
    rw [hqr, map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, hpoly r, ← hpoly P]
    ring
  have hX' : X ^ (n + 1) ∣ ρ a - ρ' a := by
    rw [hd]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hdvd _) _
  have h1 := (PowerSeries.X_pow_dvd_iff.mp hX') n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at h1
  exact h1

end LevelStatements.Lv
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PolynomialCoePowerSeriesEqAevalX

section

@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries

theorem polynomial_coe_powerSeries_eq_aeval_X {O : Type*} [CommRing O] (P : Polynomial O) :
    (P : PowerSeries O) = Polynomial.aeval (X : PowerSeries O) P := by
  rw [Polynomial.aeval_def]
  exact Polynomial.eval₂_C_X_eq_coe.symm

theorem psCyclo_algHom_coe {O : Type*} [CommRing O] (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (P : Polynomial O) : φ (P : PowerSeries O) = Polynomial.aeval (φ X) P := by
  rw [polynomial_coe_powerSeries_eq_aeval_X P]
  exact (Polynomial.aeval_algHom_apply φ X P).symm

theorem psCyclo_step {O : Type*} [CommRing O] (l : ℕ) (hl : l.Prime)
    (φ : PowerSeries O →ₐ[O] PowerSeries O) (hφ : φ X = (1 + X) ^ l - 1) (m : ℕ) (hm : l ∣ m) :
    φ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
      (((Polynomial.cyclotomic (m * l) O).comp (Polynomial.X + 1) : Polynomial O) :
        PowerSeries O) := by
  rw [psCyclo_algHom_coe, polynomial_coe_powerSeries_eq_aeval_X,
    ← Polynomial.cyclotomic_expand_eq_cyclotomic hl hm]
  simp only [Polynomial.aeval_comp, Polynomial.expand_aeval, hφ, map_add (f := _), Polynomial.aeval_X,
    map_one]
  exact congrArg (fun y => Polynomial.aeval y (Polynomial.cyclotomic m O)) (by ring)

theorem psCyclo : PsCycloStatement := by
  unfold PsCycloStatement
  intro O _ l hl φ hφ q w hq s
  induction s with
  | zero => exact ⟨w, by rw [Function.iterate_zero_apply, zero_add, pow_one]; exact hq⟩
  | succ s ih =>
    obtain ⟨w', hw'⟩ := ih
    refine ⟨Units.map (φ : PowerSeries O →* PowerSeries O) w', ?_⟩
    rw [Function.iterate_succ_apply', hw', map_mul,
      psCyclo_step l hl φ hφ (l ^ (s + 1)) (dvd_pow_self l (Nat.succ_ne_zero s)),
      ← pow_succ]
    all_goals simp

end LevelStatements.Lv
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.RingStepsOf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G PowerSeries IsLocalRing

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem ringSteps_of [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {Λ κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (f' : PowerSeries O) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (η : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (hℓ2 : PD.p ≠ 2) (hℓm : (PD.p : O) ∈ maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n0))
    (G1 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι X = (w : PowerSeries O) * X ^ (PD.p - 1))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ X = (1 + X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL, 1 + rhoZ W c ζ X = PowerSeries.C ζ * exp LL)
    (huZ : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a) :
    (lvModel Hy f' kind b η).K1b ∧ (lvModel Hy f' kind b η).HasU (W.χΓ W.gam) ∧
      (∀ s < ell, ((lvModel Hy f' kind b η).lev s).FiniteOrderFixed (baseIdOf hR).Bs.ℓ s ∧
        ((lvModel Hy f' kind b η).lev s).PhiGammaCommute) ∧
      (lvModel Hy f' kind b η).UnitsAt ∧ (lvModel Hy f' kind b η).Compl ϖ := by
  obtain ⟨w, hw⟩ := G1
  exact LevelStatements.Link.linkRing LevelStatements.Lv.rhoUnique LevelStatements.Lv.splitCompl LevelStatements.Lv.cycloSimple
    LevelStatements.Lv.psCoprime LevelStatements.Lv.rhoUnit LevelStatements.Lv.descendDvd LevelStatements.Lv.piSeries ϖ hϖ
    (lvData Hy f' kind b η) (hℓ := ⟨PD.hp⟩) hℓ2 hℓm n0 hn0 hroot (baseIdOf hR).ι w hw W.φ₀ hφ
    (baseIdOf hR).ι_φ LevelStatements.Lv.psCyclo G2 (rhoZ W c) hρζ (lvModel Hy f' kind b η)
    (fun s _ a ζ => map_eval_rhoL hR c s a ζ) (W.χΓ W.gam) (uZ : ℤ_[PD.p]) huZ ιZ hutie
    (fun _ _ => rfl)
    (fun s _ f ζ ζ' h => by
      change f (powR LL PD.p s _ ζ) = f ζ'
      congr 1
      apply Subtype.ext
      rw [h]
      rfl)
    (fun j => (j.1 : ℤ_[PD.p]))
    (fun j => (by simpa using congrArg (fun x : ℤ_[PD.p]ˣ => (x : ℤ_[PD.p])) j.2 :
      ((j.1 : ℤ_[PD.p])) ^ (PD.p - 1) = 1))
    hom'
    (fun s _ j f ζ ζ' h => by
      change f (powR LL PD.p s _ ζ) = f ζ'
      congr 1
      apply Subtype.ext
      rw [h]
      rfl)

end Formalism.MainNotions.N.Ln03
end
end
end
