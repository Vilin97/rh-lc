module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacter
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
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaConstantOfThetaGroup
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingTwistedPullback
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaConstSymmetricSquareEqOne
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaConstantPowEqOneOfPowerTrivial
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacterStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.appellHumbert_frame_semicharacter : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, ∀ b ∈ Φ.lat, (∃ k : ℤ, (hermForm Φ.Hm a b).im = k) ∧ Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ))) ∧ Φ.χ 0 = 1 ∧ ((∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ a ∈ Φ.lat, Φ.χ ((2 : ℂ) • a) = 1) := by
  first | exact @GlobalTheory.AnVal.anFr_semichar | exact GlobalTheory.AnVal.anFr_semichar | (intros; apply GlobalTheory.AnVal.anFr_semichar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaConstantOfThetaGroupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaConstant_of_thetaGroup : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ), U.pt = Φ.e x → ∃ c : ℂ, c ≠ 0 ∧ Φ.ThConst k U x c := by
  first | exact @GlobalTheory.AnVal.exists_thConst | exact GlobalTheory.AnVal.exists_thConst | (intros; apply GlobalTheory.AnVal.exists_thConst <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingTwistedPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.reading_twisted_pullback : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A) (m : Over.mk x0 ⊗ A ⟶ A) (hm : ψ ≫ snd (Over.mk x0) A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L.L b (Over.mk x0))) (s' : LB.Sec (LPow A L.L a (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) (p : (Fin g → ℂ) → Fin g → ℂ) (v : (Fin g → ℂ) → ℂ), ψ ≫ fst (Over.mk x0) A = fst (Over.mk x0) A → IsTwistPull A L.L ψ m hm a b α s s' → Φ.Rd b s θ → (∀ z, (ptSecT A (Φ.e z)).left ≫ m.left = (Φ.e (p z)).left ∧ ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j ∧ valAt' (ptSecT A (Φ.e z)).left (LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j) (α.s j).val = v z * (Φ.fr (j 0) z ^ a * Φ.fr (j 1) (p z) ^ (-b))) → Φ.Rd a s' (fun z => v z * θ (p z)) := by
  first | exact @GlobalTheory.AnVal.AnFr.rd_twistPull | exact GlobalTheory.AnVal.AnFr.rd_twistPull | (intros; apply GlobalTheory.AnVal.AnFr.rd_twistPull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingOfThetaGroupAction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem exists_wchart_complexPt {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Z ⟶ X)) (q : Sp ℂ ⟶ Z) : ∃ j : K → L.ι, ⊤ ≤ q ⁻¹ᵁ LB.wchart L φ j := by
  obtain ⟨hcov, -, -⟩ := hL
  have hmem : ∀ y : X, ∃ i, y ∈ L.U i := by
    intro y
    have hy : y ∈ (⨆ i, L.U i) := by rw [hcov]; trivial
    exact (TopologicalSpace.Opens.mem_iSup).1 hy
  have hsub : Subsingleton (Sp ℂ) := by
    change Subsingleton (PrimeSpectrum ℂ)
    infer_instance
  have p0 : Sp ℂ := by
    change PrimeSpectrum ℂ
    exact default
  choose j hj using fun k => hmem (φ k (q p0))
  refine ⟨j, fun y _ => ?_⟩
  rw [Subsingleton.elim y p0]
  show q p0 ∈ L.wchart φ j
  unfold LB.wchart
  exact Set.mem_iInter.2 fun k => hj k

theorem AnFr.rd_of_isActOf : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Φ.ThConst k U x c → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fun z => c * fock Φ.Hm k x θ z) := by
  intro S A _ _ L x0 g Φ k U x c s s' θ hc ha hr
  obtain ⟨-, hz⟩ := hc
  have hfst : translT A U.pt ≫ fst (Over.mk x0) A = fst (Over.mk x0) A := by
    unfold translT
    exact lift_fst _ _
  have hsnd : translT A U.pt ≫ snd (Over.mk x0) A = translPt A U.pt := by
    unfold translT
    exact lift_snd _ _
  have htw : IsTwistPull A L.L (translT A U.pt) (translPt A U.pt) hsnd k k U.φ s s' := by
    unfold IsActOf at ha
    exact ha
  have hcond : ∀ z, (ptSecT A (Φ.e z)).left ≫ (translPt A U.pt).left = (Φ.e (x + z)).left ∧
      ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ
          LB.wchart L.L ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] j ∧
        valAt' (ptSecT A (Φ.e z)).left
            (LB.wchart L.L ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] j) (U.φ.s j).val =
          c * fock Φ.Hm k x (fun _ => 1) z * (Φ.fr (j 0) z ^ k * Φ.fr (j 1) (x + z) ^ (-k)) := by
    intro z
    obtain ⟨hmaps, hval⟩ := hz z
    refine ⟨by simpa using hmaps 1, ?_⟩
    obtain ⟨j, hj⟩ := exists_wchart_complexPt L.L L.isLB
      ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] (ptSecT A (Φ.e z)).left
    refine ⟨j, hj, ?_⟩
    rw [hval j hj, Fin.prod_univ_two]
    simp
  have key := GlobalTheory.T.reading_twisted_pullback S A L x0 g Φ (translT A U.pt) (translPt A U.pt) hsnd k k U.φ s s' θ
    (fun z => x + z) (fun z => c * fock Φ.Hm k x (fun _ => 1) z) hfst htw hr hcond
  have hfun : (fun z => c * fock Φ.Hm k x (fun _ => 1) z * θ (x + z)) = fun z => c * fock Φ.Hm k x θ z := by
    funext z
    simp only [fock]
    rw [add_comm x z]
    ring
  rw [← hfun]
  exact key

end GlobalTheory.AnVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingOfThetaGroupActionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.reading_of_thetaGroup_action : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Φ.ThConst k U x c → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fun z => c * fock Φ.Hm k x θ z) := by
  first | exact @GlobalTheory.AnVal.AnFr.rd_of_isActOf | exact GlobalTheory.AnVal.AnFr.rd_of_isActOf | (intros; apply GlobalTheory.AnVal.AnFr.rd_of_isActOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaConstSymmetricSquareEqOneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConst_symmetric_square_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ), Φ.ThConst k U x c → (∃ nu : LB.Gen (negLB A L.L k (Over.mk x0)), nu.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (symGen A L.L k U nu) (LB.oneGen L.L)) → c ^ 2 = 1 := by
  first | exact @GlobalTheory.AnValSym.sq_const_eq_one | exact GlobalTheory.AnValSym.sq_const_eq_one | (intros; apply GlobalTheory.AnValSym.sq_const_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaConstantPowEqOneOfPowerTrivialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstant_pow_eq_one_of_power_trivial : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ), Φ.ThConst k U x c → (n : ℂ) • x ∈ Φ.lat → LB.Gen.Corr L.L _ _ _ _ (powGen A L.L k U n) (LB.oneGen L.L) → c ^ n * Φ.χ ((n : ℂ) • x) ^ k = 1 := by
  first | exact @GlobalTheory.AnValThPow.thConst_pow | exact GlobalTheory.AnValThPow.thConst_pow | (intros; apply GlobalTheory.AnValThPow.thConst_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SymmetricLiftOddOrderActsAsTranslation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem rd_fock_of_symLift : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x δ : Fin g → ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Odd n → δ ∈ Φ.lat → (n : ℂ) • x = (2 : ℂ) • δ → SymLift A L.L k n (Φ.e x) U → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fock Φ.Hm k x θ) := by
  intro S A _ _ L x0 g Φ hχ k n U x δ s s' θ hn hδ hnx hU hact hrd

  obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_thetaConstant_of_thetaGroup S A L x0 g Φ k U x hU.1
  have hread := GlobalTheory.T.reading_of_thetaGroup_action S A L x0 g Φ k U x c s s' θ hc hact hrd

  have hsq : c ^ 2 = 1 := GlobalTheory.T.thetaConst_symmetric_square_eq_one S A L x0 g Φ k U x c hc hU.3

  have hmem : (n : ℂ) • x ∈ Φ.lat := by
    rw [hnx, two_smul]
    exact add_mem hδ hδ
  have hχδ : Φ.χ ((2 : ℂ) • δ) = 1 := (GlobalTheory.T.appellHumbert_frame_semicharacter S A L x0 g Φ).2.2 hχ δ hδ
  have hpow := GlobalTheory.T.thetaConstant_pow_eq_one_of_power_trivial S A L x0 g Φ k n U x c hc hmem hU.2
  rw [hnx, hχδ, one_zpow, _root_.mul_one] at hpow

  have hc1 : c = 1 := by
    obtain ⟨m, rfl⟩ := hn
    rw [pow_succ, pow_mul, hsq, one_pow, _root_.one_mul] at hpow
    exact hpow
  subst hc1
  simpa only [_root_.one_mul] using hread

end GlobalTheory.AnVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SymmetricLiftOddOrderActsAsTranslationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x δ : Fin g → ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Odd n → δ ∈ Φ.lat → (n : ℂ) • x = (2 : ℂ) • δ → SymLift A L.L k n (Φ.e x) U → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fock Φ.Hm k x θ) := by
  first | exact @GlobalTheory.AnVal.rd_fock_of_symLift | exact GlobalTheory.AnVal.rd_fock_of_symLift | (intros; apply GlobalTheory.AnVal.rd_fock_of_symLift <;> assumption)
end
end
