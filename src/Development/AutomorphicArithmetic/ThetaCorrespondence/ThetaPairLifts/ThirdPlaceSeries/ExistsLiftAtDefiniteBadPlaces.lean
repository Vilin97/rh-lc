module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittaker
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSumman
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfFreePermute
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsFreeHalfLiftOfNeat
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSplitDeformationLift
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActCCoe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointRead
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalShareCountLeExp

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexification

section

@[expose] public section

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.DefRead.Transport

section General

variable {Ks LL WL C : Type} [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Algebra Ks ℂ] [Algebra LL ℂ] [IsScalarTower Ks LL ℂ]

def phiBil (e : C →ₗ[Ks] WL) : ℂ →+ C →+ ℂ ⊗[LL] WL :=
  AddMonoidHom.mk' (fun z => ((TensorProduct.mk LL ℂ WL z).toAddMonoidHom.comp e.toAddMonoidHom))
    (fun a b => by ext f; exact TensorProduct.add_tmul a b (e f))

theorem phiBil_compat (e : C →ₗ[Ks] WL) (r : Ks) (z : ℂ) (f : C) :
    phiBil (LL := LL) e (r • z) f = phiBil (LL := LL) e z (r • f) := by
  show (r • z) ⊗ₜ[LL] e f = z ⊗ₜ[LL] e (r • f)
  rw [map_smul, ← algebraMap_smul LL r (e f), TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    algebraMap_smul LL r z]

def phi (e : C →ₗ[Ks] WL) : ℂ ⊗[Ks] C →ₗ[ℂ] ℂ ⊗[LL] WL where
  toFun := TensorProduct.liftAddHom (phiBil (LL := LL) e) (phiBil_compat e)
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul z f =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
      show (c • z) ⊗ₜ[LL] e f = c • (z ⊗ₜ[LL] e f)
      rw [TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

@[simp] theorem phi_tmul (e : C →ₗ[Ks] WL) (z : ℂ) (f : C) : phi e (z ⊗ₜ[Ks] f) = z ⊗ₜ[LL] e f :=
  TensorProduct.liftAddHom_tmul (phiBil (LL := LL) e) (phiBil_compat e) z f

theorem phi_comm (e : C →ₗ[Ks] WL) (a : C →ₗ[Ks] C) (r : WL →ₗ[LL] WL) (h : ∀ f, e (a f) = r (e f)) :
    phi e ∘ₗ a.baseChange ℂ = r.baseChange ℂ ∘ₗ phi e := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [h]
  | add x y hx hy => simp only [LinearMap.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]

theorem phi_bijective (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL) (hliK : LinearIndependent Ks b)
    (hspK : Submodule.span Ks (Set.range b) = WK) (hliL : LinearIndependent LL b)
    (hspL : Submodule.span LL (Set.range b) = ⊤) (e : C ≃ₗ[Ks] WK) :
    Function.Bijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap)) := by
  let bW : Module.Basis (Fin n) Ks (Submodule.span Ks (Set.range b)) := Module.Basis.span hliK
  let bK : Module.Basis (Fin n) Ks WK := bW.map (LinearEquiv.ofEq _ _ hspK)
  let bC : Module.Basis (Fin n) Ks C := bK.map e.symm
  let bL : Module.Basis (Fin n) LL WL := Module.Basis.mk hliL (by rw [hspL])
  let cC := Algebra.TensorProduct.basis ℂ bC
  let cL := Algebra.TensorProduct.basis ℂ bL
  have key : phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) = (cC.equiv cL (Equiv.refl _)).toLinearMap := by
    refine cC.ext fun j => ?_
    show _ = (cC.equiv cL (Equiv.refl _)) (cC j)
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    simp [cC, cL, bC, bK, bW, bL, Module.Basis.span_apply]
  rw [key]
  exact (cC.equiv cL (Equiv.refl _)).bijective

theorem transport_general {H G X : Type} [Group G] [Group H] [DecidableEq X] [MulAction H X]
    (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL) (hliK : LinearIndependent Ks b)
    (hspK : Submodule.span Ks (Set.range b) = WK) (hliL : LinearIndependent LL b)
    (hspL : Submodule.span LL (Set.range b) = ⊤) (e : C ≃ₗ[Ks] WK) (ρ0 : G → (WL →ₗ[LL] WL))
    (act : G → C →ₗ[Ks] C) (he : ∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) (s : G → ℂ) (φ : H →* G)
    (A : X → Submodule ℂ (ℂ ⊗[Ks] C)) (hA : DirectSum.IsInternal A)
    (hinv : ∀ (h : H) (y : X), ∀ v ∈ A y, (act (φ h)).baseChange ℂ v ∈ A (h • y)) :
    ∃ A' : X → Submodule ℂ (ℂ ⊗[LL] WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, (s (φ h) • (ρ0 (φ h)).baseChange ℂ) v ∈ A' (h • y) := by
  let Ψ := LinearEquiv.ofBijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap))
    (phi_bijective WK n b hliK hspK hliL hspL e)
  let o := Submodule.orderIsoMapComap Ψ
  refine ⟨fun y => o (A y), ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hA ⊢
    refine ⟨iSupIndep.map_orderIso o hA.1, ?_⟩
    rw [← o.map_iSup, hA.2, o.map_top]
  · intro h y v hv
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_map).1 hv
    have hc := LinearMap.congr_fun (phi_comm (WK.subtype ∘ₗ e.toLinearMap) (act (φ h)) (ρ0 (φ h))
      (fun f => he _ f)) u
    refine Submodule.mem_map.2 ⟨s (φ h) • (act (φ h)).baseChange ℂ u, (A (h • y)).smul_mem _ (hinv h y u hu), ?_⟩
    simp only [LinearMap.comp_apply] at hc
    simp only [LinearMap.smul_apply, map_smul]
    show s (φ h) • phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) _ = s (φ h) • (ρ0 (φ h)).baseChange ℂ (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) u)
    rw [hc]

end General


open GlobalTheory.DefRead in
theorem transport : ∀ (Ks LL WL C H G X : Type) [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Group G] [Group H] [Fintype X] [DecidableEq X] [MulAction H X]
    (σ : LL →+* ℂ) (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL), (∀ j, b j ∈ WK) → LinearIndependent Ks b →
    Submodule.span Ks (Set.range b) = WK → LinearIndependent LL b → Submodule.span LL (Set.range b) = ⊤ →
    ∀ (e : C ≃ₗ[Ks] WK) (ρ0 : G →* (WL →ₗ[LL] WL)) (χ : G →* LLˣ) (act : G → C →ₗ[Ks] C),
    (∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) → ∀ (φ : H →* G) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (σ.comp (algebraMap Ks LL)) C)),
    DirectSum.IsInternal A → (∀ (h : H) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (σ.comp (algebraMap Ks LL)) (act (φ h)) v ∈ A (h • y)) →
    ∃ A' : X → Submodule ℂ (GlobalTheory.DefRead.VC σ WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, GlobalTheory.DefRead.twBC σ ρ0 χ (φ h) v ∈ A' (h • y) := by
  intro Ks LL WL C H G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ WK n b _ hliK hspK hliL hspL e ρ0 χ act he φ A hA hinv
  letI : Algebra Ks ℂ := (σ.comp (algebraMap Ks LL)).toAlgebra
  letI : Algebra LL ℂ := σ.toAlgebra
  haveI : IsScalarTower Ks LL ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨A', h1, h2⟩ := transport_general (X := X) WK n b hliK hspK hliL hspL e (fun g => ρ0 g) act he
    (fun g => σ (((χ g)⁻¹ : LLˣ) : LL)) φ A hA hinv
  exact ⟨A', h1, fun h y v hv => by rw [twBC_apply]; exact h2 h y v hv⟩

end GlobalTheory.DefRead.Transport
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexificationStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.transport_permuted_directSum_complexification : ∀ (Ks LL WL C H G X : Type) [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Group G] [Group H] [Fintype X] [DecidableEq X] [MulAction H X]
    (σ : LL →+* ℂ) (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL), (∀ j, b j ∈ WK) → LinearIndependent Ks b →
    Submodule.span Ks (Set.range b) = WK → LinearIndependent LL b → Submodule.span LL (Set.range b) = ⊤ →
    ∀ (e : C ≃ₗ[Ks] WK) (ρ0 : G →* (WL →ₗ[LL] WL)) (χ : G →* LLˣ) (act : G → C →ₗ[Ks] C),
    (∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) → ∀ (φ : H →* G) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (σ.comp (algebraMap Ks LL)) C)),
    DirectSum.IsInternal A → (∀ (h : H) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (σ.comp (algebraMap Ks LL)) (act (φ h)) v ∈ A (h • y)) →
    ∃ A' : X → Submodule ℂ (GlobalTheory.DefRead.VC σ WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, GlobalTheory.DefRead.twBC σ ρ0 χ (φ h) v ∈ A' (h • y) := by
  first | exact @GlobalTheory.DefRead.Transport.transport | exact GlobalTheory.DefRead.Transport.transport | (intros; apply GlobalTheory.DefRead.Transport.transport <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeHalfOfDeformationSpace

section

@[expose] public section



section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
noncomputable section
namespace GlobalTheory.DefHalf

theorem halfH_acts_freely_on_internal_sum_decomposition : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) X)
      (A : X → Submodule ℂ (GlobalTheory.DefRead.VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), ∀ v ∈ A y,
        GlobalTheory.DefRead.repAt p i (h : G0g (Fm.D x ι).nd) v ∈ A (h • y) := by
  intro hP hG
  have h1 := _root_.GlobalTheory.T.freePt_lev2_halfH_at_last_index hP hG
  have h2 := _root_.GlobalTheory.T.exists_isInternal_free_permuted_thirdPlace hP hG
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine Closed.imp (h1.and h2) ?_
  rintro eps Fm CH - ⟨⟨C1, -, x1, ha1⟩, ⟨C2, -, x2, ha2⟩⟩
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi k => ?_⟩
  have a1 := ha1 x hx (le_trans (le_max_left _ _) hle) ι p hp i hi k
  have a2 := ha2 x hx (le_trans (le_max_right _ _) hle) ι p hp i hi hp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k)
    (((p.R.eG.trans p.cG).symm.toMonoidHom).comp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k).subtype) a1
  obtain ⟨X, hX, hdX, hact, A, hfr, hint, hperm⟩ := a2
  letI := ((p.R.toRealDat.FW i)).towKs
  obtain ⟨n, b, hbW, hbK, hbsK, hbL, hbsL⟩ := p.fw.ks i
  have hK := (p.rhoGeo i).1 (fun g f hf => _root_.GlobalTheory.DefHalf.keeps_alt p i hp.1 g f hf)
  have he : ∀ g f, (((p.fw.e i) (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1 g f) : (p.R.FW i).WK) : Fin (p.R.nW i) → (Fm.D x ι).what₂.LL) =
      (p.R.FW i).ρ g ((p.fw.e i) f) := by
    intro g f
    obtain ⟨hf, h⟩ := hK g f
    rw [← h]
    rfl
  obtain ⟨A', hint', hperm'⟩ := GlobalTheory.T.transport_permuted_directSum_complexification p.T.Q.c.F (Fm.D x ι).what₂.LL (Fin (p.R.nW i) → (Fm.D x ι).what₂.LL) (CF p i)
    (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) p.P.Gp X (Fm.D x ι).what₂.embLL (p.R.FW i).WK n b hbW hbK hbsK hbL hbsL
    (p.fw.e i) (p.R.FW i).ρ (p.R.FW i).chi (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1) he
    (((p.R.eG.trans p.cG).symm.toMonoidHom).comp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k).subtype) A hint hperm
  exact ⟨X, hX, hdX, hact, A', hfr, hint', fun h y v hv => hperm' h y v hv⟩
end GlobalTheory.DefHalf
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.halfH_free_action_and_isInternal_repAt_mem : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) X)
      (A : X → Submodule ℂ (GlobalTheory.DefRead.VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), ∀ v ∈ A y,
        GlobalTheory.DefRead.repAt p i (h : G0g (Fm.D x ι).nd) v ∈ A (h • y) := by
  first | exact @_root_.GlobalTheory.DefHalf.halfH_acts_freely_on_internal_sum_decomposition | exact _root_.GlobalTheory.DefHalf.halfH_acts_freely_on_internal_sum_decomposition | (intros; apply _root_.GlobalTheory.DefHalf.halfH_acts_freely_on_internal_sum_decomposition <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepresentativeOfDeformationClass

section

@[expose] public section



section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.DefRead
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.DefRead
namespace GlobalTheory.DefRead

theorem exists_representative_of_deformation_class_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (π : Γ →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X) (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧ ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) V) (Fm.D x ι).ntypes.e0) : Submodule ℂ V) := by
  intro hP hG
  have h1 := _root_.GlobalTheory.T.halfH_free_action_and_isInternal_repAt_mem hP hG
  have h2 := hG
  unfold _root_.GlobalTheory.CovTop.GramCondition at h2
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at h1 h2 ⊢
  refine (h1.and h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩ := h
  obtain ⟨x0, e⟩ := e1.and e2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨a1, a2⟩ := e x hx hle ι p hp
  exact _root_.GlobalTheory.DefRead.point_read_alt p i hp (a2 i) (a1 i hi)
end GlobalTheory.DefRead
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.deformation_class_has_representative_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (π : Γ →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X) (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧ ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) V) (Fm.D x ι).ntypes.e0) : Submodule ℂ V) := by
  first | exact @_root_.GlobalTheory.DefRead.exists_representative_of_deformation_class_alt | exact _root_.GlobalTheory.DefRead.exists_representative_of_deformation_class_alt | (intros; apply _root_.GlobalTheory.DefRead.exists_representative_of_deformation_class_alt <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLiftAtDefiniteBadPlaces

section

@[expose] public section



section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop
theorem definite_bad_place_lift_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → BadAt p i := by
  intro hP hGr hG
  have h1 := _root_.GlobalTheory.T.deformation_class_has_representative_alt hP hG
  have h2 := _root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp_alt hP hGr
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at h1 h2 ⊢
  refine (h1.and h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩ := h
  obtain ⟨x0, e⟩ := e1.and e2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨a1, a2⟩ := e x hx hle ι p hp
  obtain ⟨Γ, _, _, V, _, _, _, π, s, ρ, Pb, lam, ψ, lamb, H, hS, hW, hl, hH, hfree, hT, hB⟩ := a1 i hi
  obtain ⟨ψ₀, hψ₀, hsh⟩ := a2 i
  have hc : ∀ k, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤
      1 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := by
    intro k
    obtain ⟨X, _, _, _, A, hf, hA, hpm⟩ := hfree k
    obtain ⟨n, hn, hn'⟩ := embReg_of_free_permuted_summands ℂ Γ V X ρ _ hf A hA hpm
    have hle : Pb.comap π ≤ (H k).comap π := fun g hg => (hH k (π g)).2 fun kv _ => (hW.2.1 (π g)).1 hg kv
    have h3 := card_mul_finrank_eig_of_free ℂ Γ V X ρ _ hf A hA hpm (Pb.comap π) hle lamb
    refine ⟨n, hn, ?_⟩
    rw [one_mul]
    exact_mod_cast (hn'.trans h3.symm).le
  choose n hn hn' using hc
  obtain ⟨S, hSb, hbd⟩ := GlobalTheory.BadCount.bad_part_le_locShare (Fm.D x ι) Γ V π s hS ρ Pb lam ψ hW lamb hl H hH n 1 hn hn' ψ₀ hψ₀
  have hs := hsh S hSb
  unfold BadAt
  rw [hT, hB]
  have hr : (0 : ℝ) ≤ (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ) := Nat.cast_nonneg _
  have hx := Real.exp_pos (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7)))
  calc _ ≤ _ := hbd
    _ ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) * (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_right hs hr
    _ ≤ _ := by nlinarith
end GlobalTheory.CovTop
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lifts_badAt_last_of_green_cuspidal : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → BadAt p i := by
  first | exact @_root_.GlobalTheory.CovTop.definite_bad_place_lift_alt | exact _root_.GlobalTheory.CovTop.definite_bad_place_lift_alt | (intros; apply _root_.GlobalTheory.CovTop.definite_bad_place_lift_alt <;> assumption)
end
end
end
end
