module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFrameLatticeIffIntegralCoords
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacterStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceUnitaryPointMemHeckeClosureStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsAlgebraicSplitCharacterTwist
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitHeckeVacuum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.RowEx.BottomHecke

variable {D : D7}

theorem thetaFunO_stdLatSp {ψ : AddChar (AF D.host.F) ℂ} {S V : HSp D} (hV : V.gram = 1) {f : WO S V → ℂ} :
    IsThetaFunO ψ S (GlobalTheory.SplitVacAlg.stdLatSp V hV) f ↔ IsThetaFunO ψ S V f :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem weilDatumO_stdLatSp {ψ : AddChar (AF D.host.F) ℂ} {S V : HSp D} (hV : V.gram = 1) {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)} (h : IsWeilDatumO ψ S V χS χT om) :
    IsWeilDatumO ψ S (GlobalTheory.SplitVacAlg.stdLatSp V hV) χS χT om :=
  { std := h.std,
    hecS := h.hecS,
    hecT := h.hecT,
    resS := h.resS,
    resT := h.resT,
    om_pres := fun p f hf => (thetaFunO_stdLatSp hV).2 (h.om_pres p f ((thetaFunO_stdLatSp hV).1 hf)),
    om_heis := fun g h' w f hf => h.om_heis g h' w f ((thetaFunO_stdLatSp hV).1 hf),
    om_aut := fun γ hγ γ' hγ' f hf => h.om_aut γ hγ γ' hγ' f ((thetaFunO_stdLatSp hV).1 hf),
    om_cont := fun f hf => h.om_cont f ((thetaFunO_stdLatSp hV).1 hf),
    om_unit := fun μ 𝓕 hμ h𝓕 p f hf => h.om_unit μ 𝓕 hμ h𝓕 p f ((thetaFunO_stdLatSp hV).1 hf),
    om_split := fun e he g h' hg hh x y hx hy => by
      obtain ⟨r, hr, H⟩ := h.om_split e he g h' hg hh x y hx hy
      exact ⟨r, hr, fun ℓ hℓ f hf => H ℓ (fun u hu f' hf' => hℓ u hu f' ((thetaFunO_stdLatSp hV).2 hf')) f
        ((thetaFunO_stdLatSp hV).1 hf)⟩ }

theorem vacuum_hecke : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW), Formalism.L2.NTheta.IsHeckeElt (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) e (ϖ : D.host.E) k α →
      ∃ Δ : Finset (WO (GlobalTheory.Grid.neg A) WW), (∀ u ∈ Δ, u.map (infPart D) = 0) ∧
        X.ω t (1, α) X.vac =
          ((((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW α) : Circle) : ℂ) *
            ((Real.sqrt (Δ.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ Δ, heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac := by
  intro D T L sc G W i j A A' WW X hX t e he ϖ k α hα
  obtain ⟨hg, hlat, -⟩ := hX.stdW
  have hS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := isSelfDualC_neg' hX.is.rigA.1
  have hT : IsSelfDualC (GlobalTheory.SplitVacAlg.stdLatSp WW hg) X.rW.Λ := hX.is.rigW.1
  have hL : (X.rW.Λ : Set (Fin WW.rank → D.host.E)) = L0c D (GlobalTheory.SplitVacAlg.stdLatSp WW hg) :=
    Set.ext fun y => (hlat y).trans (GlobalTheory.SplitVacAlg.mem_frameLattice_iff_integral_coords WW hg y).symm
  obtain ⟨Δ, hΔ⟩ := GlobalTheory.HeckeVacuum.exists_halfReps hS hT hL he hα
  refine ⟨Δ, fun x hx => GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj he) (hΔ.1 x hx).2, ?_⟩
  have hW := weilDatumO_stdLatSp hg (hX.is.weil t)
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) (GlobalTheory.SplitVacAlg.stdLatSp WW hg) X.vac :=
    (thetaFunO_stdLatSp hg).2 hX.is.isVac.2.theta
  have h := GlobalTheory.HeckeVacuum.om_elt hW hS hT hL he hα hf hX.is.isVac.2.lat hΔ
  have e1 : X.ω t (1, α) X.vac = ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm 1, α) X.vac := rfl
  rw [e1, map_one]
  exact h

end GlobalTheory.RowEx.BottomHecke
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitHeckeVacuumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.definiteBottom_splitHecke_vacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW), Formalism.L2.NTheta.IsHeckeElt (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) e (ϖ : D.host.E) k α →
      ∃ Δ : Finset (WO (GlobalTheory.Grid.neg A) WW), (∀ u ∈ Δ, u.map (infPart D) = 0) ∧
        X.ω t (1, α) X.vac =
          ((((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW α) : Circle) : ℂ) *
            ((Real.sqrt (Δ.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ Δ, heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac := by
  first | exact @GlobalTheory.RowEx.BottomHecke.vacuum_hecke | exact GlobalTheory.RowEx.BottomHecke.vacuum_hecke | (intros; apply GlobalTheory.RowEx.BottomHecke.vacuum_hecke <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitPlaceStabiliserVacuum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.StabVacSplit

open GlobalTheory.Grid (neg)



theorem stab_vac_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (k : GA D WW), k ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ → Formalism.L2.Theta.SuppAt e WW k →
      X.ω t (1, k) X.vac =
        (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac := by
  intro D T L sc G W i j A A' WW X hX t e he k hk hsupp
  set om' := (X.ω t).toSgn true with hom'
  have hW : IsWeilDatumO W.ψ (neg A) WW _ _ om' := hX.is.weil t
  have hsdS : IsSelfDualC (neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hLW : L0c D (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) = (X.rW.Λ : Set (Fin WW.rank → D.host.E)) := by
    ext y
    exact (GlobalTheory.SplitVacAlg.mem_frameLattice_iff_integral_coords WW hX.stdW.1 y).trans (hX.stdW.2.1 y).symm
  have fwd : ∀ h : GA D WW, h ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ →
      ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) →
        actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) := by
    intro h hh u hu
    have h1 : (1 : AE D) • actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) :=
      GlobalTheory.HeckeVacuum.smul_actO_mem _ _ 1 h (fun y hy => by
        rw [map_one, one_smul]
        have h2 := (hh.2.1 y).1 (by rw [hLW]; exact hy)
        rw [hLW] at h2
        exact h2) u hu
    rwa [one_smul] at h1
  have hinv : k⁻¹ ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ :=
    (GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k⁻¹).1
      (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k).2 hk))
  have hback : ∀ u : WO (neg A) WW, actO (neg A) WW 1 k⁻¹ (actO (neg A) WW 1 k u) = u := fun u => by
    rw [← GlobalTheory.HeckeVacuum.act_mul (S := neg A) (T := WW) k⁻¹ k u, inv_mul_cancel, GlobalTheory.HeckeVacuum.act_one]
  have hlat : ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) ↔
      actO (neg A) WW 1 k u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) :=
    fun u => ⟨fwd k hk u, fun hu => (hback u) ▸ fwd k⁻¹ hinv _ hu⟩
  have h1 : om' (1, k) X.vac = ((splitFacO _ _ (GlobalTheory.VecInv.detAt e he.1 (neg A) 1) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac :=
    GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character D W.ψ (neg A) WW X.rA.Λ X.rW.Λ _ _ om' hW hsdS hsdT e he 1 k
      (GlobalTheory.SplitLinear.suppAt_one e _) hsupp hlat _ _ (GlobalTheory.VecInv.isDetAt_detAt e he.1 (neg A) 1)
      (GlobalTheory.VecInv.isDetAt_detAt e he.1 WW k) X.vac hX.is.isVac.2.theta hX.is.isVac.2.lat
  have e1 : X.ω t (1, k) = om' (1, k) := by
    rw [hom']
    show X.ω t (1, k) = X.ω t ((GlobalTheory.Grid.ofSgn true A) 1, k)
    rw [map_one]
  rw [e1, h1, splitFacO, map_one, map_one, inv_one, one_mul]

end GlobalTheory.StabVacSplit

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitPlaceStabiliserVacuumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.definiteBottom_splitPlace_stabiliser_vacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (k : GA D WW), k ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ → Formalism.L2.Theta.SuppAt e WW k →
      X.ω t (1, k) X.vac =
        (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac := by
  first | exact @GlobalTheory.StabVacSplit.stab_vac_split | exact GlobalTheory.StabVacSplit.stab_vac_split | (intros; apply GlobalTheory.StabVacSplit.stab_vac_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportIdempotent

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitVacAlg

open GlobalTheory.MovedAlg

theorem isAlg_sqrt_inv (n : ℕ) : IsAlgebraic ℚ (((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹) := by
  have h : IsAlgebraic ℚ (((Real.sqrt (n : ℝ) : ℝ) : ℂ)) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (n : ℚ), Polynomial.X_pow_sub_C_ne_zero (by norm_num) _, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast, Rat.cast_natCast]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp
  rw [← mem_algebraicClosure_iff] at h ⊢
  exact inv_mem h

section Comb

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem isAlgComb_heis {u : WO S T} (hu : u.map (infPart D) = 0) : IsAlgComb ψ S T f₀ (heisO ψ S T u f₀) :=
  ⟨1, fun _ => 1, fun _ => u, fun _ => isAlgebraic_one, fun _ => hu, by simp⟩

theorem isAlgComb_sum (Δ : Finset (WO S T)) (hΔ : ∀ u ∈ Δ, u.map (infPart D) = 0) :
    IsAlgComb ψ S T f₀ (∑ u ∈ Δ, heisO ψ S T u f₀) := by
  classical
  induction Δ using Finset.induction_on with
  | empty => simpa using (IsAlgComb.zero : IsAlgComb ψ S T f₀ 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (isAlgComb_heis (hΔ a (Finset.mem_insert_self a s))).add
      (ih fun u hu => hΔ u (Finset.mem_insert_of_mem hu))

theorem isAlgComb_self : IsAlgComb ψ S T f₀ f₀ := by
  have := isAlgComb_heis (ψ := ψ) (f₀ := f₀) (u := (0 : WO S T)) (by simp)
  rwa [GlobalTheory.SplitScalar.heisO_zero ψ S T f₀] at this

end Comb


end GlobalTheory.SplitVacAlg

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitVacuumAlgebraicCombination

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.SplitVacAlg
open GlobalTheory.MovedAlg
section Comb
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}
end Comb

theorem split_vacuum_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hInp hLμ hX t N e P hP _ h hh hs
  classical
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) :=
    fun u v hu hv => GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero hX.is.isVac.1 (GlobalTheory.Grid.neg A) WW u v hu hv
  have hchr := _root_.GlobalTheory.T.isAlgebraic_splitCharacter_twist hPr hInp hLμ hX
  have vac : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac X.vac := isAlgComb_self
  have detAlg : ∀ (e' : AE D) (he' : IsSplitIdem D e') (g : GA D WW),
      IsAlgebraic ℚ (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e' he'.1 WW g) : Circle) : ℂ) :=
    fun e' he' g => hchr e' he' _ (by
      change e' * (Formalism.L2.Theta.mt WW g).det + (1 - e') =
        e' * (e' * (Formalism.L2.Theta.mt WW g).det + (1 - e')) + (1 - e')
      rw [mul_add, ← mul_assoc, he'.1, mul_sub, mul_one, he'.1, sub_self, add_zero])
  have hecke : ∀ (e' : AE D) (he' : IsSplitIdem D e') (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW),
      Formalism.L2.NTheta.IsHeckeElt (stdLatSp WW hX.stdW.1) e' (ϖ : D.host.E) k α →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, α) X.vac) := by
    intro e' he' ϖ k α hα
    obtain ⟨Δ, hΔ, heq⟩ := GlobalTheory.T.definiteBottom_splitHecke_vacuum hX t e' he' ϖ k α hα
    rw [heq]
    exact (isAlgComb_sum Δ hΔ).smul (isAlg_mul (detAlg e' he' α) (isAlg_sqrt_inv _))
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 :=
    SetLike.exists_of_lt (by
      simpa using Ideal.pow_right_strictAnti P.asIdeal P.ne_bot P.isPrime.ne_top (by norm_num : 1 < 2))
  have gen := GlobalTheory.T.splitPlace_unitaryPoint_mem_heckeClosure (stdLatSp WW hX.stdW.1) P e ϖ hP hϖ hϖ2 h hh hs
  refine Submonoid.closure_induction
    (motive := fun x _ => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, x) X.vac)) ?_ ?_ ?_ gen
  · intro x hx
    rcases hx with (⟨hk, hks⟩ | ⟨k, hα⟩) | ⟨k, hα⟩
    · rw [GlobalTheory.T.definiteBottom_splitPlace_stabiliser_vacuum hX t e hP.1 x hk hks]
      exact vac.smul (detAlg e hP.1 x)
    · exact hecke e hP.1 ϖ k x hα
    · have hc := ((GlobalTheory.SplitPlace.split_local (stdLatSp WW hX.stdW.1) P e hP).2.2 ϖ hϖ hϖ2).2 k x⁻¹ hα |>.1
      have h2 := hecke (cA D e) (GlobalTheory.SplitScalar.isSplitIdem_conj hP.1)
        ⟨star (ϖ : D.host.E), ϖ.2.map (starRingEnd D.host.E).toIntAlgHom⟩ k _ hc
      exact (congrArg (fun y : GA D WW => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, y) X.vac))
        (inv_inv x)).mp h2
  · show IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t 1 X.vac)
    rw [map_one]
    exact vac
  · intro x y _ _ hx hy
    have e1 : ((1 : GA D A), x * y) = (1, x) * (1, y) := by simp
    rw [e1, map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t 1 x hx hy
end GlobalTheory.SplitVacAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.split_place_vacuum_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  first | exact @_root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination | exact _root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination | (intros; apply _root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination <;> assumption)
end
end
end
