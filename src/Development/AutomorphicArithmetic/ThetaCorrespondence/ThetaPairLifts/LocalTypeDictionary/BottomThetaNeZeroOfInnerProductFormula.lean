module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsBottomBasisChange
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaLargeRank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaSmallRank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomMinorMatching

-- Source module: Development.AbelianVarietyTheory.Definitions.SpanningFamilies.PolarizationScalarImPos

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.Ker.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Char

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_int (F : Type) [Field F] [NumberField F] : IsOpen (intAf F) :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun v => Valued.isOpen_valuationSubring _

theorem trace_int {a : F} (h : algebraMap F (Af F) a ∈ intAf F) : ∃ n : ℤ, Algebra.trace ℚ F a = n := by
  have h1 : a ∈ (algebraMap (𝓞 F) F).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F a fun v => ?_
    have h2 : Valued.v ((a : F) : v.adicCompletion F) ≤ 1 := h v
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
  obtain ⟨b, rfl⟩ := h1
  have h3 : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F b)) := Algebra.isIntegral_trace b.2
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  exact ⟨n, hn.symm⟩

theorem int_sub {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a - b ∈ intAf F := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)

theorem int_add {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a + b ∈ intAf F := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem int_zero : (0 : Af F) ∈ intAf F := fun v => by
  rw [map_zero]; exact zero_mem _

theorem exists_char (t : Ainf F →+ ℂ) (hc : Continuous t) (hre : ∀ x, (t x).im = 0)
    (ht : ∀ a : F, t (algebraMap F (Ainf F) a) = ((Algebra.trace ℚ F a : ℚ) : ℂ)) :
    ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
      ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℤ)) : ℂ) * t x) := by
  have hap : ∀ y : Af F, ∃ a : F, y - algebraMap F (Af F) a ∈ intAf F := fun y => by
    obtain ⟨a, β, hβ, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 y
    refine ⟨a, ?_⟩
    rw [h, one_smul, add_sub_cancel_left]
    exact hβ
  choose ap hap using hap
  let c : ℂ := 2 * Real.pi * Complex.I
  let f : AF F → ℂ := fun x => Complex.exp (c * (((Algebra.trace ℚ F (ap x.2) : ℚ) : ℂ) - t x.1))
  have key : ∀ (x : AF F) (a : F), x.2 - algebraMap F (Af F) a ∈ intAf F →
      f x = Complex.exp (c * (((Algebra.trace ℚ F a : ℚ) : ℂ) - t x.1)) := by
    intro x a h
    have h1 : algebraMap F (Af F) (ap x.2 - a) ∈ intAf F := by
      have := int_sub h (hap x.2)
      rw [map_sub]
      convert this using 1
      ring
    obtain ⟨n, hn⟩ := trace_int h1
    rw [map_sub, sub_eq_iff_eq_add] at hn
    show Complex.exp _ = _
    rw [hn, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨n, ?_⟩
    push_cast
    ring
  have f0 : ∀ x : AF F, x.2 ∈ intAf F → f x = Complex.exp (-(c * t x.1)) := fun x hx => by
    rw [key x 0 (by rwa [map_zero, sub_zero])]
    simp
  have fadd : ∀ x y, f (x + y) = f x * f y := fun x y => by
    rw [key (x + y) (ap x.2 + ap y.2) (by
      have := int_add (hap x.2) (hap y.2)
      rw [map_add (f := _)]
      convert this using 1
      show x.2 + y.2 - _ = _
      ring), ← Complex.exp_add]
    congr 1
    rw [map_add (f := _), show (x + y).1 = x.1 + y.1 from rfl, map_add (f := _)]
    push_cast
    ring
  let ψ : AddChar (AF F) ℂ :=
    { toFun := f
      map_zero_eq_one' := by
        rw [f0 0 int_zero, show (0 : AF F).1 = 0 from rfl, map_zero]; simp
      map_add_eq_mul' := fadd }
  have hinf : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℤ)) : ℂ) * t x) := fun x => by
    show f (x, 0) = _
    rw [f0 (x, 0) int_zero]
    congr 1
    push_cast
    ring
  refine ⟨ψ, ⟨?_, fun x => ?_, fun a => ?_, ?_⟩, hinf⟩
  · rw [continuous_iff_continuousAt]
    intro x₀
    have hU : {x : AF F | x.2 - x₀.2 ∈ intAf F} ∈ nhds x₀ :=
      ((isOpen_int F).preimage (continuous_snd.sub continuous_const)).mem_nhds (by
        show x₀.2 - x₀.2 ∈ intAf F
        rw [sub_self]; exact int_zero)
    have hg : Continuous fun x : AF F => f x₀ * Complex.exp (-(c * t (x.1 - x₀.1))) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul (hc.comp (continuous_fst.sub continuous_const))).neg)
    refine hg.continuousAt.congr (Filter.eventually_of_mem hU fun x hx => ?_)
    show _ = f x
    rw [← add_sub_cancel x₀ x, fadd, f0 (x - x₀) hx, add_sub_cancel]
    rfl
  · show ‖Complex.exp _‖ = 1
    rw [Complex.norm_exp]
    simp [c, hre]
  · show f _ = 1
    rw [key _ a (by
      show algebraMap F (Af F) a - _ ∈ _
      rw [sub_self]; exact int_zero)]
    show Complex.exp (c * (_ - t (algebraMap F (Ainf F) a))) = 1
    rw [ht, sub_self, mul_zero, Complex.exp_zero]
  · have hn : (Module.finrank ℚ F : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    refine ⟨pairA F (algebraMap F (Ainf F) (algebraMap ℚ F (1 / (2 * Module.finrank ℚ F)))) 0, ?_⟩
    show psiInf F ψ _ ≠ 1
    rw [hinf, ht, Algebra.trace_algebraMap, nsmul_eq_mul,
      show (Module.finrank ℚ F : ℚ) * (1 / (2 * Module.finrank ℚ F)) = 1 / 2 by field_simp,
      show 2 * (Real.pi : ℂ) * Complex.I * (((-1 : ℤ)) : ℂ) * ((1 / 2 : ℚ) : ℂ) = -(Real.pi * Complex.I) by
        push_cast; ring, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

end Char

theorem exists_stdChar (D : D7) : ∃ ψ, IsStdChar D ψ (-1) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let t : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)))
    fun x y => by simp only [TensorProduct.add_tmul, map_add (f := _), Finset.sum_add_distrib]
  have hts : ∀ x, t x = (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x : ℂ) := GlobalTheory.DualPairCompare.sum_infFam θ hθ
  obtain ⟨ψ, h1, h2⟩ := exists_char t (continuous_finsetSum _ fun ρ _ => (hθ ρ).2)
    (fun x => by rw [hts, Complex.ofReal_im]) (fun a => by
      show ∑ ρ, θ ρ _ = _
      rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace])
  exact ⟨ψ, h1, ⟨θ, hθ⟩, fun θ' hθ' x => by rw [h2, hts, GlobalTheory.DualPairCompare.sum_infFam θ' hθ']⟩

section Lattice

open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA FractionalIdeal

variable (D : D7)

end Lattice

variable {D : D7} {S T : HSp D} (C : Ctx S T)

end GlobalTheory.Ker.Model

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaNeZeroOfInnerProductFormula

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTop.BotNeFormula

theorem bottomTheta_ne_zero_of_innerProduct_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  intro hPr hK hM hI hL hB hN hT
  have hLarge := _root_.GlobalTheory.T.theta_bottom_formula_large hPr hK hM hI hB
  have hSmall := _root_.GlobalTheory.T.theta_bottom_formula_small hPr hK hM hI hB
  have hMatch := _root_.GlobalTheory.T.rallis_bottom_minor_matching hPr hK hM hI hB
  have hBasis := _root_.GlobalTheory.T.exists_bottom_basis_change hPr
  unfold LNe at hL
  unfold BotSmall at hB
  unfold NormBig at hN
  unfold TriEx at hT
  unfold BotNe
  have hLevel := Model.gBig_and hL hB
  have hNorm := Model.gBig_and hN hT
  have hInputs := Model.gBig_and hLevel hNorm
  have hMatchBasis := Model.gBig_and hMatch hBasis
  have hSmallMatch := Model.gBig_and hSmall hMatchBasis
  have hFormulas := Model.gBig_and hLarge hSmallMatch
  have hAll := Model.gBig_and hInputs hFormulas
  apply BotConstPf.gBig_imp hAll
  intro D T Lc sc G μ₀ C x b hLc hData δ t0 Q P P' i j hbot
  have hLValues := hData.1.1.1
  have hTwistEmpty := hData.1.1.2.2.1
  have hNormFormula := hData.1.2.1
  have hTriangle := hData.1.2.2
  have hLargeFormula := hData.2.1
  have hSmallFormula := hData.2.2.1
  have hMinorMatch := hData.2.2.2.1
  have hBasisChange := hData.2.2.2.2
  have hmod : modT G μ₀ = SqNum.condE G.pl := by
    simp only [modT, hTwistEmpty, Finset.prod_empty, mul_one]
  rw [← hmod] at hbot
  obtain ⟨Λ, hΛ, hnz⟩ := (hLValues i j).1 μ₀
  have hh : (h0 D i j : ℤ) ≤ halfRank D i j :=
    Int.ofNat_le.mpr (squareBottomHalfRankSum_le_halfRank D i j)
  obtain ⟨Aa, hAa, hAn⟩ := hNormFormula δ t0 i j
  have hProd : (∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    have ⟨hs₁, hs₂⟩ := Finset.mem_Icc.mp hs
    exact hnz s hs₁ (hs₂.trans hh)
  have hP : P.norm ≠ 0 := fun hz =>
    mul_ne_zero hAa hProd ((hAn μ₀ Q P P' Λ hbot hΛ).symm.trans (Complex.ofReal_eq_zero.mpr hz))
  obtain ⟨h, Tt, hne⟩ := exists_coord_ne_of_norm_ne P hP
  constructor
  · exact ⟨h, Tt, hne⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Ker.Model.exists_stdChar D
  obtain ⟨W, hWψ⟩ := GlobalTheory.GridWeil.exists_weil hPr.weilRepresentationUnitaryPair D T Lc μ₀ hLc sc G ψ hψ
  have hψW : IsStdChar D W.ψ (-1) := hWψ ▸ hψ
  obtain ⟨A, A', WW, X₀, c₀, hX₀, hc₀⟩ := hTriangle W hψW i j
  obtain ⟨X, ζ, hX, hβ, -, hc⟩ := hBasisChange W hψW i j A A' WW X₀ c₀ hX₀ hc₀
  obtain ⟨Ω, -, HA⟩ := hLargeFormula W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', -, HB⟩ := hSmallFormula W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, -, HC⟩ := hMinorMatch W hψW i j A A' WW X (fun t => ζ t * c₀ t) hX hc
  obtain ⟨uA, -, -, -, HA⟩ := HA μ₀ Q P P' hbot
  obtain ⟨uB, -, -, -, HB⟩ := HB μ₀ Q P P' hbot
  have ea : P.a = A.rank := hbot.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hbot.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hbot.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have hd : P'.d = P.d := hbot.rank.2.2.2
  have ed' : P'.d = WW.rank := hd.trans ed
  obtain ⟨M, -, -, HC⟩ := HC μ₀ Q δ t0 P P' hbot ea ea' ed ed'
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  by_contra hz
  push Not at hz
  apply hne
  have e := HA ea ed h g hg Tt
  rw [HC g Tt] at e
  have hs : ∑ T', (M Tt T' : ℂ) * X.I' W.ψ W.θ μ₀ (GlobalTheory.BotFormula.minorF ea' ed' T') g = 0 := by
    apply Finset.sum_eq_zero
    intro T' _
    rw [HB ea' ed' (hd ▸ h) g hg' T', hz, mul_zero, mul_zero]
  rw [hs, mul_zero, mul_zero] at e
  simpa using e
end GlobalTheory.SqTop.BotNeFormula
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottomTheta_nonvanishing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  exact _root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula
end
end
end
