module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinPartIdemSumMulInvMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffIdempotentScaleMemCompletedTensorLatticeStatement
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatMod
import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentPartFinitePointMemShiftedTensorLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section

namespace GlobalTheory.LiftLevel

theorem partAt_finW_mem_hatA_sh : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) (conjI Lv.𝔪 • C.X.Λ), GlobalTheory.LiftLevel.partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
  intro D S T C Pg Q e he Lv hLv y hy

  have hm : Lv.𝔪 ⊔ conjI Lv.𝔪 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 Lv.cop
  have h1 : (1 : 𝓞 D.host.E) ∈ Lv.𝔪 ⊔ conjI Lv.𝔪 := by rw [hm]; exact Submodule.mem_top
  obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1
  have hcP : ∀ PP ∈ Pg ∪ Q, conjI Lv.𝔪 ≤ PP.asIdeal := by
    intro PP hPP x hx
    have h2 := mem_of_mem_conjI hx
    rw [hLv, liftI] at h2
    have h3 : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
      hPP (Ideal.prod_le_inf h2)
    have h4 := mem_of_mem_conjI h3
    have h5 : stO (stO x) = x := RingOfIntegers.ext (star_star _)
    rwa [h5] at h4
  have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
    intro PP hPP htm
    have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
  have hPQ : (Pg ∪ Q).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply Lv.proper
    rw [hLv, liftI, hne, Finset.prod_empty, Ideal.one_eq_top]
  have ht0 : (t : D.host.E) ≠ 0 := by
    obtain ⟨PP, hPP⟩ := hPQ
    intro h
    apply htP PP hPP
    have : t = 0 := RingOfIntegers.ext (h.trans rfl)
    rw [this]; exact zero_mem _

  have hsub : conjI Lv.𝔪 • C.X.Λ ≤ C.X.Λ := Submodule.smul_le_right
  have htL : ∀ v ∈ conjI Lv.𝔪 • C.X.Λ, t • v ∈ Lv.sh C.X.Λ := by
    intro v hv s hs
    have hv' : t • v ∈ Lv.𝔪 • C.X.Λ := Submodule.smul_mem_smul ht (hsub hv)
    exact Submodule.smul_mem _ s hv'
  have hty : (t : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ) := smul_mem_tens t htL hy
  have h0 : finW S T ((t : D.host.E) • y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
    rw [GlobalTheory.Ker.SignVac.finW_eq]
    exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hty

  have hz1 : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D :=
    GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP
  have hA' : ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ),
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ) :=
    fun o z hz => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have e1 : partAt e (finW S T y) = (e * incA D ((t : D.host.E))⁻¹) • finW S T ((t : D.host.E) • y) := by
    have e2 : finW S T ((t : D.host.E) • y) =
        (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) • finW S T y := by
      rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul,
        Matrix.transpose_smul]
    have e3 : finW S T y = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • finW S T y := by
      rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, one_smul]
    rw [e2, smul_smul, mul_assoc]
    have e4 : incA D ((t : D.host.E))⁻¹ * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) =
        pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((t : D.host.E))⁻¹) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ht0]
    rw [e4, mul_smul, ← e3, partAt_eq_smul]
  rw [e1]
  exact smul_mem_hatA_of_int hA' hz1 h0

end GlobalTheory.LiftLevel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentPartFinitePointMemShiftedTensorLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.idempotentPart_finitePoint_mem_shiftedTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) (conjI Lv.𝔪 • C.X.Λ), GlobalTheory.LiftLevel.partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
  first | exact @GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh | exact GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh | (intros; apply GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedClassEqPartAddTwoMovedShiftedPoint

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.LiftLevel.MovedClass

open GlobalTheory.LiftLevel

variable {D : D7}

theorem partAt_eq_smul {S T : HSp D} (c : AE D) (w : WO S T) : partAt c w = c • w := by
  ext i j; rfl

theorem actO_smul' (S T : HSp D) (g : GA D S) (h : GA D T) (c : AE D) (x : WO S T) :
    actO S T g h (c • x) = c • actO S T g h x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

theorem actO_actO_inv (S T : HSp D) (g : GA D S) (x : WO S T) : actO S T g 1 (actO S T g⁻¹ 1 x) = x := by
  simpa using GlobalTheory.WeilVacMove.actO_inv_actO (S := S) (T := T) g⁻¹ 1 x

theorem finW_two (S T : HSp D) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (2 • y) = 2 • finW S T y := by
  ext a k
  simp only [finW, two_nsmul, Matrix.add_apply, Matrix.of_apply, TensorProduct.tmul_add]

theorem tens_mono {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) {L L' : Lt E r} (h : L ≤ L') :
    tens Λ L ≤ tens Λ L' :=
  AddSubgroup.closure_mono fun _ ⟨v, hv, u, hu, e⟩ => ⟨v, hv, u, h hu, e⟩

theorem tens_two {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) (N : Lt E r)
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ (Ideal.span {(2 : 𝓞 E)} • N)) :
    ∃ y' ∈ tens Λ N, y = 2 • y' := by
  have key : tens Λ (Ideal.span {(2 : 𝓞 E)} • N) ≤
      (tens Λ N).map (DistribSMul.toAddMonoidHom (Matrix (Fin n) (Fin r) E) (2 : ℕ)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    rw [Submodule.ideal_span_singleton_smul] at hu
    obtain ⟨u', hu', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hu
    refine ⟨vecMulVec v u', AddSubgroup.subset_closure ⟨v, hv, u', hu', rfl⟩, ?_⟩
    ext i j
    simp [vecMulVec_apply, two_smul, two_nsmul, mul_add]
  obtain ⟨y', hy', e⟩ := key hy
  exact ⟨y', hy', e.symm⟩

theorem mem_sh {S T : HSp D} (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) :
    Lv.𝔪 • (conjI Lv.𝔪 • C.X.Λ) ≤ Lv.sh C.X.Λ := by
  intro v hv b hb
  exact Submodule.smul_mono le_rfl Submodule.smul_le_right (Submodule.smul_mem _ b hv)

theorem moved_class : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1 := by
  intro D S T C hn ΛT hT hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' hab hmov hgen hΛ' Lv hLv y hy
  rw [Submodule.mul_smul] at hy
  obtain ⟨y', hy', rfl⟩ := tens_two _ _ hy
  have hS := C.m.gS
  set std := stdL D.host.E S.rank with hstd
  set x := finW S T y' with hx
  set X := actO S T k₀ 1 x with hX
  have hX2 : actO S T k₀ 1 (finW S T (2 • y')) = 2 • X := by
    rw [finW_two, GlobalTheory.WeilVacMove.actO_two_nsmul]
  rw [hX2]

  have hxM : x ∈ hatA S T (tens std (conjI Lv.𝔪 • C.X.Λ)) := by
    rw [hx, GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.TensLatMove.intAf_one (D := D)) hy'
  have hE : partAt e x ∈ hatA S T (tens std (Lv.sh C.X.Λ)) := GlobalTheory.T.idempotentPart_finitePoint_mem_shiftedTensorLattice D S T C Pg Q e he Lv hLv y' hy'
  have hF : partAt (1 - e - cA D e) x ∈ hatA S T (tens std (Lv.sh C.X.Λ)) := by
    refine GlobalTheory.T.offIdempotent_scale_mem_completedTensorLattice D S T e (Pg ∪ Q) he _ _ ?_ x hxM
    have : (∏ PP ∈ Pg ∪ Q, conjI PP.asIdeal) = Lv.𝔪 := by rw [hLv]; rfl
    rw [this]; exact mem_sh C Lv
  have hB : (1 - cA D e) • x ∈ hatA S T (tens std (Lv.sh C.X.Λ)) := by
    have : (1 - cA D e) • x = partAt e x + partAt (1 - e - cA D e) x := by
      rw [partAt_eq_smul, partAt_eq_smul, ← add_smul]; congr 1; ring
    rw [this]; exact add_mem hE hF
  have hmov1 : IsMov (fmt T 1) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) := by
    have hmt1 : Formalism.L2.Theta.mt T 1 = 1 := by simp [Formalism.L2.Theta.mt]
    have hfmt1 : fmt T 1 = 1 := by simp [fmt, hmt1]
    rw [hfmt1]
    intro u
    exact ⟨fun h => ⟨u, h, (Matrix.one_mulVec u).symm⟩, fun ⟨u₀, h, e⟩ => by rw [e, Matrix.one_mulVec]; exact h⟩
  obtain ⟨u₀, hu₀, hu₀e⟩ := (GlobalTheory.TensLatMove.mem_hatA_iff S T hS k₀⁻¹ 1 Λ' std (Lv.sh C.X.Λ) (Lv.sh C.X.Λ)
    hΛ' hmov1 _).1 hB
  have hv : partAt (1 - cA D e) X = u₀ := by
    rw [partAt_eq_smul, hX, ← actO_smul', hu₀e, actO_actO_inv]
  refine ⟨partAt (1 - cA D e) X, hv ▸ hu₀, ?_, ?_⟩
  · rw [partAt_eq_smul, partAt_eq_smul, smul_comm (cA D e) (2 : ℕ) X, ← smul_add, ← add_smul]
    congr 1
    rw [add_sub_cancel, one_smul]
  · have hce : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
    have hint1 : finPart D (cA D e) ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hce])
    have hce' : (1 - cA D e) * (1 - cA D e) = 1 - cA D e := by linear_combination hce
    have hint2 : finPart D (1 - cA D e) ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hce'])
    have hstar : ∀ v : Fin S.rank → D.host.E, v ∈ std ↔ star v ∈ std := by
      have : ∀ v : Fin S.rank → D.host.E, v ∈ std → star v ∈ std := fun v hv =>
        (GlobalTheory.SW.Base.mem_stdL _).2 fun a => GlobalTheory.SW.Base.isIntegral_cc ((GlobalTheory.SW.Base.mem_stdL _).1 hv a)
      exact fun v => ⟨this v, fun h => by simpa using this _ h⟩
    have hlat := GlobalTheory.Ker.LatTens.latO_eq_hatA D S T C std std ΛT C.X.Λ hstar hAA
    have hxΛ : x ∈ hatA S T (tens std C.X.Λ) := by
      rw [hx, GlobalTheory.Ker.SignVac.finW_eq]
      exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.TensLatMove.intAf_one (D := D)) (tens_mono _ Submodule.smul_le_right hy')
    rw [← hlat] at hxΛ
    have hP := Formalism.IndefR.Fin.latO_smul_mem S T std ΛT hint1 hxΛ
    have hR := Formalism.IndefR.Fin.latO_smul_mem S T std ΛT hint2 hxΛ
    have hpair := GlobalTheory.LatVac.char_sympl_eq_one C.std (GlobalTheory.Ker.Base.selfDualC_stdL hS) hT hP hR
    have hpair' : C.ψ (symplO S T (cA D e • X) ((1 - cA D e) • X)) = 1 := by
      rw [hX, ← actO_smul', ← actO_smul', GlobalTheory.SymplOInv.symplO_actO]; exact hpair
    rw [partAt_eq_smul, partAt_eq_smul, smul_comm (cA D e) (2 : ℕ) X, two_nsmul, two_nsmul,
      GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self, GlobalTheory.LatVac.symplO_add_right,
      AddChar.map_add_eq_mul, hpair', one_mul]

end GlobalTheory.LiftLevel.MovedClass

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedClassEqPartAddTwoMovedShiftedPointStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.movedClass_eq_part_add_two_movedShiftedPoint : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1 := by
  first | exact @GlobalTheory.LiftLevel.MovedClass.moved_class | exact GlobalTheory.LiftLevel.MovedClass.moved_class | (intros; apply GlobalTheory.LiftLevel.MovedClass.moved_class <;> assumption)
end
end
