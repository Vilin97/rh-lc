module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusLiftMovesLetterCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesDualStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIntegralSigmaSqFixedStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIsotropicStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearFormsHyperbolicCoordinatesEqTargetStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfValuationLeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlaces
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasisCoordinatesDualStatement
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceDualExpansionOrbitLengthStatement
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrame
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTrace

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaTauOrthonormalBasisSumCoordinates

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem map_inv_field_hom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : A.adjugate.map f = (A.map f).adjugate := by
    have := RingHom.map_adjugate f A; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (A.map f).det = f A.det := by
    have := RingHom.map_det f A; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv', Ring.inverse_eq_inv', map_inv₀]

theorem lamB_sum_gK : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ (k : D.what₂.Tau × Fin N' × Fin N) (z : Bool × HH D) (a : Fin N) (b₀ : Fin N'), ∑ i, Formalism.L2.KerInert.RepFrame.lamB D lam b k i * ((gK D lam P P' b z a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p]) = chgB D lam P P' k ((0 : ZMod 1), (tauPl D z, a, b₀)) := by
  intro D p _ lam σ hσ hcl N N' L L' P P' _ _ r b hb k z a b₀
  obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl z
  set τ := tauPl D z with hτ
  let ι : MaximalUnramifiedExtension p →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype
  have hfun : ∀ y, ι (ρ y) = tauEmb D lam τ y := fun y => (hρ y).2
  have hrho : rhoK D lam z = fun y => ρ y := funext fun y => (hρ y).1
  have hinv : ∀ a a₁, ((((P τ).map (rhoK D lam z))⁻¹ a a₁ : MaximalUnramifiedExtension p) : ℂ_[p]) =
      ((P τ).map (tauEmb D lam τ))⁻¹ a a₁ := by
    intro a a₁
    have e2 : (P τ).map (tauEmb D lam τ) = ((P τ).map ρ).map ι := by
      ext u v; simp [hfun]
    rw [hrho, e2, ← map_inv_field_hom ι]; rfl
  have hg : ∀ i, ((gK D lam P P' b z a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p]) = ∑ b₁ : Fin N', ∑ a₁ : Fin N,
      Formalism.L2.KerInert.RepFrame.lamBc D lam b (τ, b₁, a₁) i *
        (tauEmb D lam τ (P' τ b₁ b₀) * ((P τ).map (tauEmb D lam τ))⁻¹ a a₁) := by
    intro i
    rw [gK, ← hτ]
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, coe_rhoK D lam σ hσ hcl, hinv, mul_assoc, ← hτ]
    rfl
  simp_rw [hg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b₁ _ => Finset.sum_comm).trans ?_
  simp_rw [← mul_assoc, ← Finset.sum_mul, hb k]
  rcases k with ⟨t, c, d⟩
  by_cases ht : t = τ
  · subst ht
    simp [chgB, Prod.ext_iff, ite_and]
  · simp [chgB, Prod.ext_iff, ht, Ne.symm ht]

end GlobalTheory.KerStd.HypCoord
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaTauOrthonormalBasisSumCoordinatesStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.lambdaTau_orthonormalBasis_sum_coordinates : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ (k : D.what₂.Tau × Fin N' × Fin N) (z : Bool × HH D) (a : Fin N) (b₀ : Fin N'), ∑ i, Formalism.L2.KerInert.RepFrame.lamB D lam b k i * ((gK D lam P P' b z a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p]) = chgB D lam P P' k ((0 : ZMod 1), (tauPl D z, a, b₀)) := by
  first | exact @GlobalTheory.KerStd.HypCoord.lamB_sum_gK | exact GlobalTheory.KerStd.HypCoord.lamB_sum_gK | (intros; apply GlobalTheory.KerStd.HypCoord.lamB_sum_gK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLocalBasisStandardCoordLeOneInert

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem norm_hK_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → ∀ w a b₀ i, ‖hK D lam P P' b w a b₀ i‖ ≤ 1 := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b hb w a b₀ i
  obtain ⟨h2, hq, -⟩ := GlobalTheory.InertCompare.ne_of_inert D p hcl
  obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl w
  set τ := tauPl D w with hτ
  have hρK : rhoK D lam w = fun y => ρ y := funext fun y => (hρ y).1
  have hρC : ∀ y, ((ρ y : MaximalUnramifiedExtension p) : ℂ_[p]) = GlobalTheory.KerStd.UnitaryMat.rho D lam τ y := fun y => by
    rw [(hρ y).2, GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]
  have hPW : LocBasisW D (GlobalTheory.KerStd.UnitaryMat.rho D lam τ) L (P τ) := by
    rw [← GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]; exact hP.1 τ
  have hP'W : LocBasisW D (GlobalTheory.KerStd.UnitaryMat.rho D lam τ) L' (P' τ) := by
    rw [← GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]; exact hP'.1 τ
  have hdet : IsUnit (P' τ).det := isUnit_iff_ne_zero.2 hP'W.1
  have hQ : (P' τ)⁻¹ * P' τ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hinv : ((P' τ).map (fun y => ρ y))⁻¹ = ((P' τ)⁻¹).map (fun y => ρ y) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [show ((P' τ)⁻¹).map (fun y => ρ y) = ((P' τ)⁻¹).map ρ from rfl,
      show (P' τ).map (fun y => ρ y) = (P' τ).map ρ from rfl, ← Matrix.map_mul, hQ,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [GlobalTheory.PadicPlaceBound.norm_prime_padicComplex]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hint := GlobalTheory.KerStd.UnitaryMat.intIn_of_locBasis hp1
    (fun x hx => GlobalTheory.EigenGenerator.norm_padicEmbedding_le_one_of_mem_inverseHalfDifferent D h2 hq _ hx) hQ hPW hP'W hb i b₀ a
  have e : hK D lam P P' b w a b₀ i = ρ (((P' τ)⁻¹ * b i * P τ) b₀ a) := by
    unfold hK
    rw [← hτ, hρK, hinv]

    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  show ‖((hK D lam P P' b w a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1
  rw [e, hρC]
  exact hint

end GlobalTheory.KerStd.HypCoord
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLocalBasisStandardCoordLeOneInertStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.norm_localBasis_standardCoord_le_one_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → ∀ w a b₀ i, ‖hK D lam P P' b w a b₀ i‖ ≤ 1 := by
  first | exact @GlobalTheory.KerStd.HypCoord.norm_hK_le_one | exact GlobalTheory.KerStd.HypCoord.norm_hK_le_one | (intros; apply GlobalTheory.KerStd.HypCoord.norm_hK_le_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesScaledEqOrthonormalBasisSeries

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem mvPowerSeries_subst_linearForm {σ τ : Type} [Fintype σ] {K : Type} [Field K] {a : σ → MvPowerSeries τ K}
    (ha : MvPowerSeries.HasSubst a) (α : σ → K) :
    MvPowerSeries.subst a (∑ j, MvPowerSeries.C (α j) * MvPowerSeries.X j : MvPowerSeries σ K) =
      ∑ j, MvPowerSeries.C (α j) * a j := by

  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_C]

theorem stdSer_scaled_eq_thOrth : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' r : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hz : Fin r → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (hz i) = 0) → (∀ k, ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i = ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C (chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) * MvPowerSeries.X j) → ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst hz (thOrth D lam c b G) := by
  intro D p _ lam N N' r P P' b hz hz0 hlin c G
  have hs1 : MvPowerSeries.HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by simp
  have hs2 : MvPowerSeries.HasSubst hz := MvPowerSeries.hasSubst_of_constantCoeff_zero hz0
  have e : ∀ x : ℂ_[p], algebraMap ℂ_[p] (MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) x = MvPowerSeries.C x := fun x => rfl
  rw [stdSer, atLin, thOrth, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp) hs1,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp) hs2]
  congr 1
  funext k
  simp only [e, one_mul]
  rw [mvPowerSeries_subst_linearForm hs1, mvPowerSeries_subst_linearForm hs2]
  have h1 : (∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * hz i :
      MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) =
      MvPowerSeries.C c * ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_assoc]
    rfl
  rw [h1, hlin k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.KerStd.HypCoord
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesScaledEqOrthonormalBasisSeriesStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.standardSeries_scaled_eq_orthonormalBasisSeries : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' r : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hz : Fin r → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (hz i) = 0) → (∀ k, ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i = ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C (chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) * MvPowerSeries.X j) → ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst hz (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth | exact GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth | (intros; apply GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardBasesHyperbolicPairOrthonormal

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)


open GlobalTheory.KerStd.HypCoord in
theorem GlobalTheory.KerStd.hyp_of_stdBases : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p), OwOK (nP D p) σ om oms → TrDual (nP D p) σ om oms → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p, HypPair σ f f' ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') (thOrth D lam c b G) := by
  intro D p _ lam σ hσ hO hcl om oms hOw hTr R hR N N' L L' P P' hA hP hP' r b hb ho
  have hcl' : IsResidueClassZero D p ∨ IsSg D p := hcl.elim (fun h => Or.inl h.1) Or.inr
  have hONB : Formalism.L2.KerInert.RepFrame.LamONB D lam b :=
    Formalism.L2.KerInert.RepFrame.lamONB_of_cols D lam b
      (Formalism.L2.KerInert.RepFrame.rank_of_locBasis L L' hA.2.2.1 hA.2.2.2 b hb)
      (Formalism.L2.KerInert.RepFrame.cols_of_trace D (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) lam b ho)
  obtain ⟨hg, hh⟩ := GlobalTheory.T.frobeniusLift_moves_letter_coordinates D p lam σ hσ hcl' N N' L L' P P' hP hP' r b
  have hpair := GlobalTheory.T.orthonormalLocalBasis_coordinates_dual D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hONB
  have hiso := norm_sigma_eq p σ hσ
  have hhint := GlobalTheory.T.norm_localBasis_standardCoord_le_one_inert D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hb
  have hgint : ∀ z a b₀ i, ‖gK D lam P P' b z a b₀ i‖ ≤ 1 := fun z a b₀ i => by
    rw [← hiso, hg]; exact hhint _ _ _ _
  have hg2 : ∀ z a b₀ i, σ (σ (gK D lam P P' b z a b₀ i)) = gK D lam P P' b (posPl D p z 2) a b₀ i :=
    fun z a b₀ i => by rw [hg, hh, posPl_add]
  obtain ⟨hf1, hf2⟩ := GlobalTheory.T.hyperbolicCoordinates_integral_sigma_sq_fixed D p σ om oms R N N' r (gK D lam P P' b) hO
    (fun x hx => by rw [hiso]; exact hx) hOw hgint hg2
  obtain ⟨hi1, hi2⟩ := GlobalTheory.T.hyperbolicCoordinates_isotropic D p σ om oms R N N' r (gK D lam P P' b) (hK D lam P P' b) hO hR hg hpair
  have hd := GlobalTheory.T.hyperbolicCoordinates_dual D p σ om oms R N N' r (gK D lam P P' b) (hK D lam P P' b) hO hR hTr hg hpair
  refine ⟨fOf D p σ om R (gK D lam P P' b), fOf' D p σ oms R (gK D lam P P' b), ⟨hf1, hf2, hi1, hi2, hd⟩, ?_⟩
  have hlin := GlobalTheory.T.linearForms_hyperbolicCoordinates_eq_target D p σ om oms R N N' r _ (gK D lam P P' b) (Formalism.L2.KerInert.RepFrame.lamB D lam b)
    (fun k j => chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) hO hR (GlobalTheory.T.traceDual_expansion_orbitLength D p σ om oms hTr)
    (fun q z a b₀ => GlobalTheory.T.lambdaTau_orthonormalBasis_sum_coordinates D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hONB q z a b₀)
  refine GlobalTheory.T.standardSeries_scaled_eq_orthonormalBasisSeries D p lam N N' r P P' b _ (fun i => ?_) hlin

  simp only [hypZ, linEv, linOd, map_sum, map_add (f := _), map_mul, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_X,
  mul_zero, apply_ite MvPowerSeries.constantCoeff, map_zero, ite_self, Finset.sum_const_zero, add_zero]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardBasesHyperbolicPairOrthonormalStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.standardSeries_scaled_eq_orthonormalSeries_hyperbolicSubst : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p), OwOK (nP D p) σ om oms → TrDual (nP D p) σ om oms → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p, HypPair σ f f' ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.hyp_of_stdBases | exact GlobalTheory.KerStd.hyp_of_stdBases | (intros; apply GlobalTheory.KerStd.hyp_of_stdBases <;> assumption)
end
end
