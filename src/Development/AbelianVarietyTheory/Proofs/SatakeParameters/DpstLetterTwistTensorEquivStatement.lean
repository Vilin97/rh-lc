module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBalancedBilinearTensorProductMapStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvertibleDPstPotSemistableCharacter
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacter
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvertibleDPstPotSemistableCharacterStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

theorem _root_.GlobalTheory.T.exists_invertible_dPst_potSemistableCharacter : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ {K L : FinExt l} (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1), (∀ g v, ρm g v = χ g • v) → IsPst P ρm → ∃ y ∈ Dpst P ρm, ∃ y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P, GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' y = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) := by
  first | exact @GlobalTheory.Pst.UnitLetter.exists_unit_Dpst | exact GlobalTheory.Pst.UnitLetter.exists_unit_Dpst | (intros; apply GlobalTheory.Pst.UnitLetter.exists_unit_Dpst <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacterStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

theorem _root_.GlobalTheory.T.exists_periodProduct_eq_of_invertible_character : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (y : ↥(Dpst P ρm)) (y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P), GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) → ∀ z : ↥(Dpst P ρt), ∃ x : ↥(Dpst P ρs), GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y = z := by
  first | exact @GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv | exact GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv | (intros; apply GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodProductCommutesFrobeniusZpow

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

namespace GlobalTheory.Pst.TwistLetters

theorem units_zpow_bilin_comm {R M₁ M₂ M₃ : Type} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (B : M₁ →ₗ[R] M₂ →ₗ[R] M₃) (u₁ : (Module.End R M₁)ˣ) (u₂ : (Module.End R M₂)ˣ) (u₃ : (Module.End R M₃)ˣ)
    (h : ∀ x y, (u₃ : Module.End R M₃) (B x y) = B ((u₁ : Module.End R M₁) x) ((u₂ : Module.End R M₂) y))
    (n : ℤ) (x : M₁) (y : M₂) :
    ((u₃ ^ n : (Module.End R M₃)ˣ) : Module.End R M₃) (B x y) =
      B (((u₁ ^ n : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂ ^ n : (Module.End R M₂)ˣ) : Module.End R M₂) y) := by
  have hinv : ∀ x y, ((u₃⁻¹ : (Module.End R M₃)ˣ) : Module.End R M₃) (B x y) =
      B (((u₁⁻¹ : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂⁻¹ : (Module.End R M₂)ˣ) : Module.End R M₂) y) := by
    intro x y
    have e₁ := LinearMap.congr_fun (Units.mul_inv u₁) x
    have e₂ := LinearMap.congr_fun (Units.mul_inv u₂) y
    rw [Module.End.mul_apply, Module.End.one_apply] at e₁ e₂
    conv_lhs => rw [← e₁, ← e₂, ← h]
    have e₃ := LinearMap.congr_fun (Units.inv_mul u₃) (B (((u₁⁻¹ : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂⁻¹ : (Module.End R M₂)ˣ) : Module.End R M₂) y))
    rw [Module.End.mul_apply, Module.End.one_apply] at e₃
    exact e₃
  induction n using Int.induction_on generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, Units.val_mul,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, h, ih]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, Units.val_mul,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hinv, ih]

end GlobalTheory.Pst.TwistLetters

namespace GlobalTheory.Pst.TwistLetters

theorem phiU_zpow_dmul : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρs)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρm)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρt)] (n : ℤ) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)), ((phiU P ρt ^ n : (Module.End ↥L.1 ↥(Dpst P ρt))ˣ) : Module.End ↥L.1 ↥(Dpst P ρt)) (GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y) = GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht (((phiU P ρs ^ n : (Module.End ↥L.1 ↥(Dpst P ρs))ˣ) : Module.End ↥L.1 ↥(Dpst P ρs)) x) (((phiU P ρm ^ n : (Module.End ↥L.1 ↥(Dpst P ρm))ˣ) : Module.End ↥L.1 ↥(Dpst P ρm)) y) := by
  intro l _ P K L V _ _ _ _ ρs ρt ρm χ hm ht _ _ _ n x y
  exact units_zpow_bilin_comm (dmul P ρs ρt ρm χ hm ht) (phiU P ρs) (phiU P ρm) (phiU P ρt)
    (fun x y => phiD_dmul P ρs ρt ρm χ hm ht x y) n x y

end GlobalTheory.Pst.TwistLetters
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodProductCommutesFrobeniusZpowStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

theorem _root_.GlobalTheory.T.periodProduct_commutes_frobenius_zpow : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρs)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρm)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρt)] (n : ℤ) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)), ((phiU P ρt ^ n : (Module.End ↥L.1 ↥(Dpst P ρt))ˣ) : Module.End ↥L.1 ↥(Dpst P ρt)) (GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y) = GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht (((phiU P ρs ^ n : (Module.End ↥L.1 ↥(Dpst P ρs))ˣ) : Module.End ↥L.1 ↥(Dpst P ρs)) x) (((phiU P ρm ^ n : (Module.End ↥L.1 ↥(Dpst P ρm))ˣ) : Module.End ↥L.1 ↥(Dpst P ρm)) y) := by
  first | exact @GlobalTheory.Pst.TwistLetters.phiU_zpow_dmul | exact GlobalTheory.Pst.TwistLetters.phiU_zpow_dmul | (intros; apply GlobalTheory.Pst.TwistLetters.phiU_zpow_dmul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstLetterTwistTensorEquiv

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Pst.TwistLetters



theorem wdSpace_twist_equiv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (m : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L s))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L m))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))], IsPst P (Bw.repE L s) → IsPst P (Bw.repE L m) → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) → ∃ e : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) ≃ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), (∀ (σ : ↥(Weil h)) x, e (TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) x) = wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ (e x)) ∧ ∀ x, e (((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) + (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s)) : Module.End ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m))) x) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (e x) := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj L a s m _ _ _ hs hm ht
  let χ : ↥(GK Bw.Kw) → ↥L.1 := fun g => ((GlobalTheory.TwistAbove.chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)
  have hχm : ∀ g v, Bw.repE L m g v = χ g • v := fun g v => GlobalTheory.TwistAbove.repE_rank_one Bw m g v
  have hχt : ∀ g v, Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) g v = χ g • Bw.repE L s g v := by
    intro g v
    rw [GlobalTheory.TwistBridgeDR.twGL_eq]
    exact GlobalTheory.TwistBridgeDR.repE_twGL' Bw _ s g v
  clear_value χ
  have hl := dmul_mulD_left P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt
  have hr := dmul_mulD_right P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt
  have hL1 := @GlobalTheory.T.exists_balancedBilinear_tensorProduct_map _ _ _ _ _ _ _ _ _ _ _ _ _ (mulD P (Bw.repE L s)) (mulD P (Bw.repE L m)) (mulD P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))) ℂ _ (algC ι L) (urC ι) _ hl hr
  obtain ⟨Φ, hΦ'⟩ : ∃ Φ : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) →ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), ∀ x y, Φ (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y) = wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) ((dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) x y) := hL1
  have hsurj : Function.Surjective Φ := by
    have h2b := GlobalTheory.T.exists_invertible_dPst_potSemistableCharacter P AI hT (Bw.repE L m) χ hχm hm
    obtain ⟨y, hy, y', hyy'⟩ := h2b
    let y₀ : ↥(Dpst P (Bw.repE L m)) := ⟨y, hy⟩
    have h2 := GlobalTheory.T.exists_periodProduct_eq_of_invertible_character P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt y₀ y' hyy'
    have hspan : Submodule.span ℂ (Set.range (wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))) = ⊤ := span_wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))
    have hle : Submodule.span ℂ (Set.range (wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))) ≤ LinearMap.range Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := h2 z
      exact ⟨_, (hΦ' x y₀).trans (by rw [hx])⟩
    intro z
    exact LinearMap.mem_range.mp (hle (Submodule.eq_top_iff'.mp hspan z))
  have hdim : Module.finrank ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m)) =
      Module.finrank ℂ (WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))) := by
    rw [Module.finrank_tensorProduct, GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ hs,
      GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ hm, GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ ht]
    simp
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  have key : ∀ {f g : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) →ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))},
      (∀ x y, f (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y) =
        g (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y)) → f = g := by
    intro f g H
    apply TensorProduct.ext
    apply LinearMap.ext_on_range (span_wdMk P ι (Bw.repE L s))
    intro x
    apply LinearMap.ext_on_range (span_wdMk P ι (Bw.repE L m))
    intro y
    exact H x y
  have hW : ∀ σ x y, weilD Bw h P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ ((dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) x y) =
      (dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) (weilD Bw h P (Bw.repE L s) σ x) (weilD Bw h P (Bw.repE L m) σ y) := by
    intro σ x y
    simp only [weilD_apply, Module.End.mul_apply, GlobalTheory.T.periodProduct_commutes_frobenius_zpow P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt, actD_dmul]
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun σ x => ?_, fun x => ?_⟩
  · have e : Φ ∘ₗ TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) =
        wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ ∘ₗ Φ := by
      apply key
      intro x y
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, wdRho_mk, hΦ', hW]
    exact LinearMap.congr_fun e x
  · have e : Φ ∘ₗ ((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) +
        (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s))) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) ∘ₗ Φ := by
      apply key
      intro x y
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        wdN_mk, map_add, hΦ', monD_dmul, wdMk_add]
    exact LinearMap.congr_fun e x

end GlobalTheory.Pst.TwistLetters
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstLetterTwistTensorEquivStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

theorem _root_.GlobalTheory.T.dpstLetter_twist_tensor_equiv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (m : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L s))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L m))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))], IsPst P (Bw.repE L s) → IsPst P (Bw.repE L m) → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) → ∃ e : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) ≃ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), (∀ (σ : ↥(Weil h)) x, e (TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) x) = wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ (e x)) ∧ ∀ x, e (((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) + (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s)) : Module.End ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m))) x) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (e x) := by
  first | exact @GlobalTheory.Pst.TwistLetters.wdSpace_twist_equiv | exact GlobalTheory.Pst.TwistLetters.wdSpace_twist_equiv | (intros; apply GlobalTheory.Pst.TwistLetters.wdSpace_twist_equiv <;> assumption)
end
end
