module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IoUniq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RightInv
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfVanishIt

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.StepUniq


open Classical in
theorem eq_zero_of_vanish_it : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ u : MMap (R.MY k), Formalism.IndefR.Eqv.ContAt (R.MY k) u → (∀ φ w, PiTensorProduct.lift u (R.ItY k φ w) = 0) → u = 0 := by
  intro hDS hHC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH t k hk u hc hv
  have hB := hP.char.base
  have hCh : R.toRealDat.IsChain := RealDat.chain_of_weak hB.chain hH.aux.ex
  have hok := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A3.A Ks R.toRealDat hB.lev hB.models.inf hCh.ωY hCh.ωX hCh.vY hCh.vX
  obtain ⟨hw, hvv⟩ := hok.1 t ⟨k, by omega⟩ hk
  have hIt := hCh.ItY t k hk
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ _ _
    (R.ωY t k) (R.vY t k) (R.ItY k) hB.models.inf hw hvv hIt
  have hx : ∀ x, (LinearMap.proj x : (GA D (Yc D k) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ PiTensorProduct.lift u = 0 := by
    intro x
    refine GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D _ _ (R.MY k) _ ?_ ?_
    · intro τ v
      obtain ⟨ℓ, hℓ, he⟩ := hc τ v x
      refine ⟨ℓ, hℓ, fun w => ?_⟩
      rw [he w]
      simp [PiTensorProduct.lift.tprod]
    · intro v hv'
      have hmem := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv' τ), rfl⟩)
      have hker : Submodule.span ℂ {w | ∃ P, ∃ y ∈ Submodule.span ℂ {w | ∃ v, (∀ τ, ((v τ : (R.MY (k + 1)).sm τ) :
          (R.MY (k + 1)).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin (R.MY (k + 1)) τ) ∧ w = PiTensorProduct.tprod ℂ v},
            w = (R.ItY k P) y} ≤ LinearMap.ker ((LinearMap.proj x : (GA D (Yc D k) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
              PiTensorProduct.lift u) := by
        rw [Submodule.span_le]
        rintro _ ⟨P, y, -, rfl⟩
        simp [hv P y]
      exact hker hmem
  have h0 : PiTensorProduct.lift u = 0 := by
    ext v x
    have := congrArg (fun Λ => Λ (PiTensorProduct.tprod ℂ v)) (hx x)
    simpa using this
  have : u = PiTensorProduct.lift.symm (PiTensorProduct.lift u) := by simp
  rw [this, h0, map_zero]

end GlobalTheory.Mem.R3.StepUniq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevChange

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta

theorem stepLev_change : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (b : Bool) (t : T) (k : ℕ), k + 1 < D.R.m → ∀ (κ : GA D (Yc D k)), ∀ κ' ∈ levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)), ∀ c : ℂ, (∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ) → ∀ y : R.CC t (k + 1), y.1 ∈ MultT R.θ (R.MY (k + 1)) (levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) → ∀ φ w g, (R.ioY t k y).1 (R.ItY k φ w) (g * κ) = c * levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ' * (R.ioY t k y).1 (R.ItY k φ w) g := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk κ κ' hκ' c hc y hy φ w g
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hP.char.base.chain hH.aux.ex
  have hio := hch.ioY t k (by omega)
  have e1 := hio.eq y φ w (g * κ)
  have e2 := hio.eq y φ w g
  rw [← e1, ← e2]
  unfold Lift.liftInt

  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hy)
  set χ1 := levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) with hχ1
  have hlev : ∀ (u : SmT (R.MY (k + 1))) h, y.1 u (h * κ') = χ1 κ' * y.1 u h := by
    intro u h
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := hm.lev v κ' hκ' h
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
      ring
    | add a a' ha ha' =>
      simp only [map_add (f := _), Pi.add_apply, ha, ha']
      ring
  have hleft : ∀ (u : SmT (R.MY (k + 1))), ∀ γ ∈ GQ (Yc D (k + 1)), ∀ h, y.1 u (γ * h) = y.1 u h := by
    intro u γ hγ h
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (hm.aut v).left γ hγ h
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
    | add a a' ha ha' =>
      simp only [map_add (f := _), Pi.add_apply, ha, ha']
  have hω := hch.ωY t k hk
  have hpt := hch.ptY t k hk φ
  have hθ1 : ∀ h, thetaKO (R.ωY t k) (g * κ) h (R.toRealDat.ptY t k φ) =
      c * thetaKO (R.ωY t k) g (h * κ'⁻¹) (R.toRealDat.ptY t k φ) := by
    intro h
    unfold thetaKO
    have e : ((g * κ, h) : GA D (Yc D k) × GA D (Yc D (k + 1))) = (g, h * κ'⁻¹) * (κ, κ') := by
      ext <;> simp [mul_assoc]
    rw [e, map_mul, Module.End.mul_apply, hc φ, map_smul, Pi.smul_apply, smul_eq_mul]
  have hθ2 : ∀ γ ∈ GQ (Yc D (k + 1)), ∀ h, thetaKO (R.ωY t k) g (γ * h) (R.toRealDat.ptY t k φ) =
      thetaKO (R.ωY t k) g h (R.toRealDat.ptY t k φ) := by
    intro γ hγ h
    unfold thetaKO
    have e : ((g, γ * h) : GA D (Yc D k) × GA D (Yc D (k + 1))) = (1, γ) * (g, h) := by
      ext <;> simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ hpt)
  have hmod := hP.char.base.models
  have hHF : (R.νY t (k + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (k + 1))) (R.fdY t (k + 1)) (R.νY t (k + 1)) := by
    by_cases h2 : k + 1 + 1 < D.R.m
    · have h3 := hmod.νY t (k + 1) h2
      exact ⟨h3.1.1, h3.2⟩
    · have h3 := hmod.νY' t
      have e : D.R.m - 1 = k + 1 := by omega
      rw [e] at h3
      exact ⟨h3.1.1, h3.2⟩
  haveI := Formalism.IndefR.Eqv.measurableMul_GA D (Yc D (k + 1))
  haveI := Formalism.IndefR.Eqv.gQ_countable D (Yc D (k + 1))
  haveI := hHF.1
  haveI : (R.νY t (k + 1)).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds _ _ hHF.1
  set Ψ : GA D (Yc D (k + 1)) → ℂ := fun h => thetaKO (R.ωY t k) g h (R.toRealDat.ptY t k φ) * y.1 w h with hΨ
  have hRI := Formalism.IndefR.Eqv.rightInv_holds (GA D (Yc D (k + 1))) (GQ (Yc D (k + 1))) (R.νY t (k + 1))
    (R.fdY t (k + 1)) hHF.2 Ψ (fun γ hγ h => by simp only [hΨ, hθ2 γ hγ h, hleft w γ hγ h]) κ'⁻¹
  calc ∫ h in R.fdY t (k + 1), thetaKO (R.ωY t k) (g * κ) h (R.toRealDat.ptY t k φ) * y.1 w h ∂(R.νY t (k + 1))
      = ∫ h in R.fdY t (k + 1), c * χ1 κ' * Ψ (h * κ'⁻¹) ∂(R.νY t (k + 1)) := by
        congr 1
        funext h
        have e := hlev w (h * κ'⁻¹)
        rw [inv_mul_cancel_right] at e
        simp only [hΨ, hθ1 h, e]
        ring
    _ = c * χ1 κ' * ∫ h in R.fdY t (k + 1), Ψ h ∂(R.νY t (k + 1)) := by
        rw [integral_const_mul, hRI.2]

end GlobalTheory.Mem.R3.DTheta
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevLift

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
noncomputable section

namespace GlobalTheory.Mem.R3.DTheta.StepLevLift

theorem stepLev_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (b : Bool) (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ levS (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)), ∃ κ' ∈ levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)), R.ωY t k (κ, κ') (R.vY t k) = (levChi (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) κ * (levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ')⁻¹) • R.vY t k := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk κ hκ
  have hL := hP.char.base.lev
  have hk' : k < D.R.m := Nat.lt_of_succ_lt hk
  obtain ⟨hκ1, hκ2⟩ := hκ
  set g0 : G0 R.Pg D.R.r := rTup (R.βY k) (R.datYt t k R.triv) (finE (Yc D k) κ) with hg0
  have hl : IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) g0 κ := ⟨hκ1, hκ2.1, rfl⟩
  obtain ⟨κ', hl'⟩ := GlobalTheory.ChainLiftEquiv.liftsExist_chain R.toRealDat hL t (k + 1) hk g0
  have hlaw := GlobalTheory.StepVecLaw.stepVec_lifts R.toRealDat hL hP.char.base.models.inf hP.char.base.chain.ωY
    hP.char.base.chain.vY t k hk g0 κ κ' hl hl'
  have hmem : rTup (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) (finE (Yc D (k + 1)) κ') ∈
      (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H := by
    rw [hl'.2.2]; exact hκ2.2
  refine ⟨κ', ⟨hl'.1, hl'.2.1, hmem⟩, ?_⟩
  have e1 := levFn_withP (V := Yc D k) (β := R.βY k) (L := R.datYt t k (R.toRealDat.levR F.lv2 b))
    (R.datYt t k (R.toRealDat.levR F.lv2 b)).P (finE (Yc D k) κ)
  have e2 := levFn_withP (V := Yc D (k + 1)) (β := R.βY (k + 1)) (L := R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))
    (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P (finE (Yc D (k + 1)) κ')
  have x1 : ext1 (R.datYt t k (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t k (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) (finE (Yc D k) κ)) =
      ext1 (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ')) := by
    have : rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ') = g0 := hl'.2.2
    rw [this]
    rfl
  unfold levChi
  change R.ωY t k (κ, κ') (R.vY t k) = (((Formalism.L2.DIV.levFn (R.βY k) (withP (R.datYt t k (R.toRealDat.levR F.lv2 b)) (R.datYt t k (R.toRealDat.levR F.lv2 b)).P) (finE (Yc D k) κ) : ℂˣ) : ℂ) * ((Formalism.L2.DIV.levFn (R.βY (k + 1)) (withP (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P) (finE (Yc D (k + 1)) κ') : ℂˣ) : ℂ)⁻¹) • R.vY t k
  rw [e1, e2, x1]
  unfold levChi at hlaw
  change ((Formalism.L2.DIV.levFn (R.βY k) (flagL (R.datYt t k (R.toRealDat.levR F.lv2 b))) (finE (Yc D k) κ) : ℂˣ) : ℂ)⁻¹ • R.ωY t k (κ, κ') (R.vY t k) = ((Formalism.L2.DIV.levFn (R.βY (k + 1)) (flagL (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (finE (Yc D (k + 1)) κ') : ℂˣ) : ℂ)⁻¹ • R.vY t k at hlaw
  set c := ext1 (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ'))
  set a := Formalism.L2.DIV.levFn (R.βY k) (flagL (R.datYt t k (R.toRealDat.levR F.lv2 b))) (finE (Yc D k) κ)
  set a' := Formalism.L2.DIV.levFn (R.βY (k + 1)) (flagL (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (finE (Yc D (k + 1)) κ')
  have ha : ((a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hc : ((c : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h3 : R.ωY t k (κ, κ') (R.vY t k) = (((a : ℂˣ) : ℂ) * ((a' : ℂˣ) : ℂ)⁻¹) • R.vY t k := by
    rw [mul_smul, ← hlaw, smul_inv_smul₀ ha]
  rw [h3, Units.val_mul, Units.val_mul]
  congr 1
  field_simp

end GlobalTheory.Mem.R3.DTheta.StepLevLift

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFockVectorEigenOfFiniteStepEigen

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta.StepLevFock

theorem om_ptY_of_finite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ GfC (Yc D k), ∀ κ' ∈ GfC (Yc D (k + 1)), ∀ c : ℂ, R.ωY t k (κ, κ') (R.vY t k) = c • R.vY t k → ∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH t k hk κ hκ κ' hκ' c hc φ
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hP.char.base.chain hH.aux.ex
  exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ (R.ωY t k) hP.char.base.models.inf (hch.ωY t k hk)
    _ _ _ _ (R.vY t k) (hch.ptY t k hk) κ hκ κ' hκ' c hc φ

end GlobalTheory.Mem.R3.DTheta.StepLevFock
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFockVectorEigenOfFiniteStepEigenStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.weilFock_vector_eigen_of_finite_step_eigen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ GfC (Yc D k), ∀ κ' ∈ GfC (Yc D (k + 1)), ∀ c : ℂ, R.ωY t k (κ, κ') (R.vY t k) = c • R.vY t k → ∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ := by
  first | exact @GlobalTheory.Mem.R3.DTheta.StepLevFock.om_ptY_of_finite | exact GlobalTheory.Mem.R3.DTheta.StepLevFock.om_ptY_of_finite | (intros; apply GlobalTheory.Mem.R3.DTheta.StepLevFock.om_ptY_of_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerThetaStepsPreserveFaceLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta

theorem stepLev_holds : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.StepLev R.toRealDat F.lv2 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk y hy
  have hx0 := (R.ioY t k y).2
  have hT := Formalism.IndefR.Eqv.contAt_of_mem ((mem_multT _ _ _ _ _).1 hx0)
  have hx := hx0
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  refine ⟨hx.aut, hx.cusp, ?_, hx.equiv, hx.cont⟩
  intro v κ hκ g
  obtain ⟨κ', hκ', hω⟩ := GlobalTheory.Mem.R3.DTheta.StepLevLift.stepLev_lift D G Pl0 I0 T A3 Ks R F cG hP hH b t k hk κ hκ
  have hpt := GlobalTheory.T.weilFock_vector_eigen_of_finite_step_eigen D G Pl0 I0 T A3 Ks R F cG hP hH t k hk κ hκ.1 κ' hκ'.1 _ hω
  have hval := GlobalTheory.Mem.R3.DTheta.stepLev_change D G Pl0 I0 T A3 Ks R F cG hP hH b t k hk κ κ' hκ' _ hpt y hy
  set x := (R.ioY t k y).1 with hxdef
  set c0 := levChi (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) κ with hc0
  set c1 := levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ' with hc1
  have hne : c1 ≠ 0 := by rw [hc1]; unfold levChi; exact Units.ne_zero _
  let u : MMap (R.MY k) := (LinearMap.funLeft ℂ ℂ (fun h : GA D (Yc D k) => h * κ)).compMultilinearMap
    (PiTensorProduct.lift.symm x) - c0 • PiTensorProduct.lift.symm x
  have hu : Formalism.IndefR.Eqv.ContAt (R.MY k) u := by
    intro τ v' z
    obtain ⟨ℓ₁, s₁, e₁⟩ := hT τ v' (z * κ)
    obtain ⟨ℓ₂, s₂, e₂⟩ := hT τ v' z
    refine ⟨ℓ₁ + (-c0) • ℓ₂, GlobalTheory.MultMem.sobCont_add s₁ (GlobalTheory.MultMem.sobCont_smul _ s₂), fun w => ?_⟩
    simp only [u, LinearMap.add_apply, LinearMap.smul_apply, e₁, e₂, MultilinearMap.sub_apply,
      MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply, Pi.sub_apply, Pi.smul_apply,
      LinearMap.funLeft_apply, smul_eq_mul]
    ring
  have hz : ∀ φ w, PiTensorProduct.lift u (R.ItY k φ w) = 0 := by
    intro φ w
    have e : PiTensorProduct.lift u = (LinearMap.funLeft ℂ ℂ (fun h : GA D (Yc D k) => h * κ)) ∘ₗ x - c0 • x := by
      apply PiTensorProduct.ext
      ext v'
      simp [u]
    rw [e]
    funext g'
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
      LinearMap.funLeft_apply, smul_eq_mul, Pi.zero_apply]
    rw [hval φ w g']
    field_simp
    ring
  have h0 := GlobalTheory.Mem.R3.StepUniq.eq_zero_of_vanish_it hC.1 hC.2.1 D G Pl0 I0 T A3 Ks R F cG hP hH t k hk u hu hz
  have h1 := congrFun (congrArg (fun U : MMap (R.MY k) => U v) h0) g
  simp only [u, MultilinearMap.sub_apply, MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply, Pi.sub_apply,
    Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul, MultilinearMap.zero_apply, Pi.zero_apply] at h1
  linear_combination h1

end GlobalTheory.Mem.R3.DTheta
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerThetaStepsPreserveFaceLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.innerThetaSteps_preserve_faceLevel : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.StepLev R.toRealDat F.lv2 := by
  first | exact @GlobalTheory.Mem.R3.DTheta.stepLev_holds | exact GlobalTheory.Mem.R3.DTheta.stepLev_holds | (intros; apply GlobalTheory.Mem.R3.DTheta.stepLev_holds <;> assumption)
end
end
