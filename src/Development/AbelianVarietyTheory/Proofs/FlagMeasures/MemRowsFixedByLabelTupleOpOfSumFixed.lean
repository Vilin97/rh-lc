module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ReductionConjugacy
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TupOfOneMemLabT
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuous
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPointsStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InflationBasic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvUniqueAddSmulMulComm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPoints
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeffChosenRedEqRedHom

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem coeff_goodAt_eq (D : D7) (X : HidaSetting D) (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ b, a * b = b * a)
    (x : X.B.I.Gf) (γ γ' : G0g D.nd) (h : GoodAt X x γ) (h' : GoodAt X x γ') : a.coeff γ' = a.coeff γ := by
  have hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      γ' kv = P⁻¹ * γ kv * P := by
    intro kv
    exact Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw kv.1 kv.2))
      (D.host.g kv.1) (D.host.g_prime kv.1)
      (by rw [Formalism.L2.SG.Pf.RowDictPf.card_wB, Formalism.L2.SG.Pf.RowDictPf.card_res_host]) D.R.r X.n_eq.symm x (γ kv) (γ' kv)
      ((Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ x _).1 (h kv))
      ((Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ x _).1 (h' kv))
  choose P hP using hP
  have e : γ' = (P : G0g D.nd)⁻¹ * γ * P := funext fun kv => hP kv
  rw [e]
  exact Formalism.L2.SG.Pf.RowDictPf.coeff_conj_of_central ha γ P

theorem coeff_chosenRed_eq_redHom : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd), IsRedHom X red →
    ∀ a : MonoidAlgebra ℂ (G0g D.nd), (∀ b, a * b = b * a) → ∀ x : X.B.I.Gf,
    (if h : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ then
      a.coeff (Classical.choose h.2) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0) =
    if x ∈ X.B.I.Kset then a.coeff (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0 := by
  intro D X red hred a ha x
  by_cases hx : x ∈ X.B.I.Kset
  · have hc : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ := ⟨hx, red x, hred.1 x hx⟩
    rw [dite_eq_left hc, if_pos hx,
      coeff_goodAt_eq D X a ha x (red x) (Classical.choose hc.2) (hred.1 x hx) (Classical.choose_spec hc.2)]
  · rw [dite_eq_right (fun h => hx h.1), if_neg hx]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ESSingleCoeffCentral

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabIdem

theorem ES_single_coeff_central : ∀ (D : D7) (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) →
    (∀ γ, (ES {t}).coeff γ = serCoef t γ) ∧ ∀ b, ES {t} * b = b * ES {t} := by
  intro D t _
  have e : (ES {t} : MonoidAlgebra ℂ (G0g D.nd)) = GlobalTheory.RowLev.zTup D t := GlobalTheory.RowLev.ES_singleton (D := D) t
  refine ⟨fun γ => ?_, fun b => ?_⟩
  · rw [e]; rfl
  · rw [e]; exact GlobalTheory.RowLev.zTup_comm t b

end GlobalTheory.LabIdem
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuousStatement

section

@[expose] public section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.rightRegularRepresentation_unitary_mul_continuous : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → R 1 = ContinuousLinearMap.id ℂ _ ∧ (∀ x y, R (x * y) = (R x).comp (R y)) ∧ (∀ x F, ‖R x F‖ = ‖F‖) ∧ ∀ F, Continuous fun x => R x F := by
  first | exact @GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous | exact GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous | (intros; apply GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWeakIntegralOfStronglyContinuous

section

@[expose] public section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_weakIntegral_of_stronglyContinuous {X H : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) (R : X → (H →L[ℂ] H)) (hn : ∀ x F, ‖R x F‖ = ‖F‖)
    (hc : ∀ F, Continuous fun x => R x F) (φ : X → ℂ) (hφ : Integrable φ μ) :
    ∃ T : H →L[ℂ] H, ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, φ g * ⟪x, R g y⟫_ℂ ∂μ := by
  have hint : ∀ y : H, Integrable (fun g => φ g • R g y) μ := fun y =>
    (hφ.norm.mul_const ‖y‖).mono' (hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun g => by rw [norm_smul, hn])
  let Tl : H →ₗ[ℂ] H :=
    { toFun := fun y => ∫ g, φ g • R g y ∂μ
      map_add' := fun y z => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (hint y) (hint z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        congr 1
        ext g
        rw [smul_comm] }
  refine ⟨Tl.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun x y => ?_⟩
  · calc ‖Tl y‖ = ‖∫ g, φ g • R g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • R g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by
        congr 1
        ext g
        rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · show ⟪x, ∫ g, φ g • R g y ∂μ⟫_ℂ = _
    rw [← integral_inner (hint y)]
    congr 1
    ext g
    rw [inner_smul_right]

theorem AutInst_exists_isRConvF_and_isRConv : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → (∀ e : I.Gf → ℂ, Integrable e μf → ∃ T, I.IsRConvF μf fund R e T) ∧ ∀ φ : I.GA → ℂ, Integrable φ (I.muA μf) → ∃ T, I.IsRConv μf fund R φ T := by
  intro I μf _ _ fund hfund R hR
  obtain ⟨-, -, hn, hc⟩ := GlobalTheory.T.rightRegularRepresentation_unitary_mul_continuous I μf fund hfund R hR
  haveI := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints I
  refine ⟨fun e he => ?_, fun φ hφ => ?_⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous μf (fun g => R (1, g))
      (fun g F => hn _ F) (fun F => (hc F).comp (by fun_prop)) e he
    exact ⟨T, he, hT⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous (I.muA μf) R hn hc φ hφ
    exact ⟨T, hφ, hT⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableCoeff

section

@[expose] public section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab
open scoped InnerProductSpace Classical

noncomputable section

namespace GlobalTheory.LevelIdem

section Conv

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Conv

section Alg

variable {Q : Type} [Group Q] [Fintype Q]

end Alg

section Lev

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem vol_ne_zero (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] {g : ℕ} (hg : 1 ≤ g) :
    μf (I.Kg g) ≠ ⊤ ∧ ((μf (I.Kg g)).toReal : ℂ) ≠ 0 := by
  obtain ⟨-, -, -, hK, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨hopen, ⟨S, hS⟩, -⟩ := hKg g hg
  have hsub : I.Kg g ⊆ I.Kset := fun x hx => hx.1
  have hfin : μf (I.Kg g) ≠ ⊤ := ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
  have h1 : (1 : I.Gf) ∈ I.Kg g := by rw [← hS]; exact S.one_mem
  have hpos : μf (I.Kg g) ≠ 0 := (hopen.measure_pos μf ⟨1, h1⟩).ne'
  exact ⟨hfin, Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hpos hfin).ne'⟩

theorem mem_fibre {s : I.Gf} (hs : s ∈ I.Kset) (x : I.Gf) :
    s⁻¹ * x ∈ I.Kg g ↔ x ∈ I.Kset ∧ ρ.toFun x = ρ.toFun s := by
  have hmul : ∀ a ∈ I.Kset, ∀ b ∈ I.Kset, a * b ∈ I.Kset := fun a ha b hb =>
    (mem_Ksub I _).1 ((Ksub I).mul_mem ((mem_Ksub I a).2 ha) ((mem_Ksub I b).2 hb))
  have hinv : ∀ a ∈ I.Kset, a⁻¹ ∈ I.Kset := fun a ha =>
    (mem_Ksub I _).1 ((Ksub I).inv_mem ((mem_Ksub I a).2 ha))
  constructor
  · intro h
    have hk : s⁻¹ * x ∈ I.Kset := (show s⁻¹ * x ∈ I.Kset ∧ _ from h).1
    have hx : x ∈ I.Kset := by simpa using hmul s hs _ hk
    refine ⟨hx, ?_⟩
    have hm := ρ.map_mul s hs _ hk
    rwa [mul_inv_cancel_left, (ρ.ker _ hk).2 h, mul_one] at hm
  · rintro ⟨hx, hxs⟩
    have hk := hmul _ (hinv s hs) x hx
    refine (ρ.ker _ hk).1 ?_
    rw [ρ.map_mul _ (hinv s hs) x hx, ρ.map_inv hs, hxs, inv_mul_cancel]

theorem integral_lift [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q)
    (s : Q → I.Gf) (hs : ∀ q, s q ∈ I.Kset ∧ ρ.toFun (s q) = q) (φ : I.Gf → ℂ)
    (hφ : ∀ x, ∀ k ∈ I.Kg g, φ (x * k) = φ x) :
    ∫ x, ρ.lift μf a x * φ x ∂μf = ∑ q, a.coeff q * φ (s q) := by
  classical
  obtain ⟨hfin, hvol⟩ := vol_ne_zero I μf hg
  have hopen := ((GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.2 g hg).1
  have hSm : ∀ q, MeasurableSet ((fun y => (s q)⁻¹ * y) ⁻¹' I.Kg g) := fun q =>
    (hopen.preimage (continuous_const_mul _)).measurableSet
  have hpt : ∀ x, ρ.lift μf a x * φ x = ∑ q, ((fun y => (s q)⁻¹ * y) ⁻¹' I.Kg g).indicator
      (fun _ => a.coeff q * φ (s q) / ((μf (I.Kg g)).toReal : ℂ)) x := by
    intro x
    by_cases hx : x ∈ I.Kset
    · rw [ρ.lift_of_mem μf a hx, Finset.sum_eq_single (ρ.toFun x)]
      · have hmem : (s (ρ.toFun x))⁻¹ * x ∈ I.Kg g :=
          (mem_fibre ρ (hs _).1 x).2 ⟨hx, (hs _).2.symm⟩
        rw [Set.indicator_of_mem (show x ∈ (fun y => (s (ρ.toFun x))⁻¹ * y) ⁻¹' I.Kg g from hmem)]
        have hφx : φ x = φ (s (ρ.toFun x)) := by
          have h' := hφ (s (ρ.toFun x)) _ hmem
          rwa [mul_inv_cancel_left] at h'
        rw [hφx]
        ring
      · intro q _ hq
        refine Set.indicator_of_notMem (fun hmem => hq ?_) _
        exact ((((mem_fibre ρ (hs q).1 x).1 hmem).2).trans (hs q).2).symm
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [ρ.lift_of_notMem μf a hx, zero_mul]
      refine (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun hmem => hx ?_) _).symm
      exact ((mem_fibre ρ (hs q).1 x).1 hmem).1
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hSm q), measureReal_def, measure_preimage_mul, Complex.real_smul]
    field_simp
  · intro q _
    refine (integrable_indicator_iff (hSm q)).2 (integrableOn_const ?_)
    rw [measure_preimage_mul]
    exact hfin

end Lev

end GlobalTheory.LevelIdem
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRowsFixedByLabelTupleOpOfSumFixed

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabFix

theorem mem_VT_of_sum_fixed : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf), IsRedHom X red → IsSec X red sec → ∀ (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) → ∀ f ∈ HHX X, ∑ᶠ γ, serCoef t γ • X.B.R ((1, sec γ) : X.B.I.GA) f = f → f ∈ VT X t := by
  intro D X red sec hred hsec t ht f hf hsum
  classical
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  let ρ : GlobalTheory.RowLev.Red X.B.I X.B.g (G0g D.nd) :=
    { toFun := red, map_mul := hred.2.1, ker := hred.2.2.2, surj := hred.2.2.1 }
  obtain ⟨hcoef, hcent⟩ := GlobalTheory.LabIdem.ES_single_coeff_central D t ht
  have hegA : egA X (ES {t}) = ρ.lift X.B.μf (ES {t}) := by
    funext x
    rw [egA, GlobalTheory.coeff_chosenRed_eq_redHom D X red hred _ hcent x]
    by_cases hx : x ∈ X.B.I.Kset
    · rw [if_pos hx, GlobalTheory.RowLev.Red.lift_of_mem ρ _ _ hx]
    · rw [if_neg hx, GlobalTheory.RowLev.Red.lift_of_notMem ρ _ _ hx]
  obtain ⟨h1R, hm, hn, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  obtain ⟨huniq, -, -, hprod, -⟩ := GlobalTheory.WeakConv.rightConv_unique_add_smul_mul_comm X.B.I X.B.μf X.B.fund X.B.R
    X.B.fund_spec X.B.R_spec
  obtain ⟨hQ, -, -, -, -, hinfl, -, -, -⟩ := GlobalTheory.InflBasic.inflation_basic X.B.I X.B.g (G0g D.nd) ρ X.B.μf hg
  letI : Fintype (G0g D.nd) := Fintype.ofFinite _
  obtain ⟨hlint, hlloc, -⟩ := hinfl (ES {t})
  obtain ⟨Ta, hTa⟩ := (GlobalTheory.AutInst_exists_isRConvF_and_isRConv X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R
    X.B.R_spec).1 _ hlint
  have he := X.B.e_adm
  have hecont : Continuous X.B.e := he.1.continuous
  have hReRe : X.B.Re.comp X.B.Re = X.B.Re := by
    have h := hprod _ _ _ _ hecont hecont X.B.Re_spec X.B.Re_spec
    rw [he.2.1] at h
    exact huniq _ _ _ h X.B.Re_spec
  have hRT : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X {t}) (X.B.Re.comp Ta) := by
    unfold eT
    rw [hegA]
    exact hprod _ _ _ _ hecont hlloc.continuous X.B.Re_spec hTa
  have hReT : ReT X {t} = X.B.Re.comp Ta := by
    have hex : ∃ T, X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X {t}) T := ⟨_, hRT⟩
    unfold ReT
    rw [dite_eq_left hex]
    exact huniq _ _ _ (Classical.choose_spec hex) hRT
  obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hf
  have hRef : X.B.Re f = f := by
    rw [← hz]
    show X.B.Re (X.B.Re (X.Rph z)) = X.B.Re (X.Rph z)
    rw [← ContinuousLinearMap.comp_apply X.B.Re X.B.Re, hReRe]
  have p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1 := h1R
  have pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b) := by
    intro a b
    rw [ContinuousLinearMap.mul_def, ← hm]
    simp
  have pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖ := fun g v => hn _ v
  have hone : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
    refine ⟨(Formalism.UG.stabGL X.B.I.Lf).one_mem, fun y _ => ⟨0, X.B.I.Lf.zero_mem, ?_⟩⟩
    have : X.B.I.fmat 1 = 1 := rfl
    simp [this]
  haveI : SecondCountableTopology X.B.I.Gf := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints X.B.I
  have hfix : ∀ k ∈ X.B.I.Kg X.B.g, X.B.R (1, k) f = f := by
    intro k hk
    have h := GlobalTheory.IdemProj.op_fixed X.B.μf (fun g => X.B.R (1, g)) p1 pm pn X.B.e X.B.Re X.B.Re_spec.2 k
      (fun x => by simpa using he.2.2.2.2.2.1 x k hk 1 hone)
    rw [← hRef, ← ContinuousLinearMap.comp_apply]
    exact DFunLike.congr_fun h f
  have hTaf : Ta f = f := by
    apply ext_inner_left ℂ
    intro v
    rw [hTa.2, GlobalTheory.LevelIdem.integral_lift ρ X.B.μf hg (ES {t}) sec hsec (fun x => ⟪v, X.B.R (1, x) f⟫_ℂ) ?_]
    · conv_rhs => rw [← hsum]
      rw [finsum_eq_sum_of_fintype, inner_sum]
      simp only [inner_smul_right, hcoef]
    · intro x k hk
      show ⟪v, X.B.R (1, x * k) f⟫_ℂ = ⟪v, X.B.R (1, x) f⟫_ℂ
      rw [show ((1 : X.B.I.Ginf), x * k) = ((1, x) : X.B.I.GA) * (1, k) by simp, hm,
        ContinuousLinearMap.comp_apply, hfix k hk]
  refine Submodule.mem_inf.2 ⟨hf, ?_⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  show ReT X {t} f = f
  rw [hReT, ContinuousLinearMap.comp_apply, hTaf, hRef]

end GlobalTheory.LabFix
end
end
