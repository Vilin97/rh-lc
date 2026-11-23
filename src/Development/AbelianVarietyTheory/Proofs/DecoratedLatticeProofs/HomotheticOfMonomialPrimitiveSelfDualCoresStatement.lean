module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeRationalLineTraceFractionalIdealStatement
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrimitiveCharacterMatchesLinesDownFlagStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastIsotropicLineHomothetyMatchesLattices

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LastLine

variable {D : D7}

theorem cancel (v : GlobalTheory.FinPl.Pl D) (x : D.host.E) (hx : x ≠ 0) (A : AE D → Prop)
    (hA : ∀ a ∈ idAt D (· = v), A a ↔ incA D x⁻¹ * a ∈ intAt D (· = v)) (P Q : AE D → Prop)
    (hP : ∀ o ∈ intAt D (· = v), ∀ t, P t → P (o * t)) (hQ : ∀ o ∈ intAt D (· = v), ∀ t, Q t → Q (o * t))
    (h : ∀ s ∈ idAt D (· = v), (∀ a ∈ idAt D (· = v), A a → P (s * a)) ↔ (∀ a ∈ idAt D (· = v), A a → Q (s * a))) :
    ∀ t ∈ idAt D (· = v), (P t ↔ Q t) := by
  intro t ht
  obtain ⟨ε, -, hεI, hε⟩ := GlobalTheory.IwaPlace.LocSD.exists_idem (D := D) v
  have hs : incA D x⁻¹ * t ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ht
  have ha0 : incA D x * ε ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hεI.1
  have hA0 : A (incA D x * ε) := by
    rw [hA _ ha0, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]
    exact hεI
  have hst : incA D x⁻¹ * t * (incA D x * ε) = t := by
    rw [show incA D x⁻¹ * t * (incA D x * ε) = (incA D x⁻¹ * incA D x) * (ε * t) by ring, ← map_mul,
      inv_mul_cancel₀ hx, map_one, one_mul, hε t ht]
  have hsa : ∀ a, incA D x⁻¹ * t * a = (incA D x⁻¹ * a) * t := fun a => by ring
  constructor
  · intro hPt
    have := (h _ hs).1 (fun a ha hAa => by
      rw [hsa]; exact hP _ ((hA a ha).1 hAa) t hPt) _ ha0 hA0
    rwa [hst] at this
  · intro hQt
    have := (h _ hs).2 (fun a ha hAa => by
      rw [hsa]; exact hQ _ ((hA a ha).1 hAa) t hQt) _ ha0 hA0
    rwa [hst] at this

theorem colMul_mul {m n : ℕ} (X : Mx D m n) (i : Fin n) (o t : AE D) :
    colMul X i (o * t) = o • colMul X i t := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.Core.Mi.LastLine

end

noncomputable section

namespace GlobalTheory.Core.Mi.LastLine

variable {D : D7}

theorem lastLine_match : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S₀ M → z ≠ 0 → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → ∀ i : Fin ρ, i.1 + 1 = ρ → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  intro D ψ S S₀ ρ d z L L' M M' v c γ hM hz hL hL' hc hγ hmv i hi a ha
  obtain ⟨𝔞, h𝔞, -, hline⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D S₀ M z hM hz
  obtain ⟨x, hx, hgen⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  have hA : ∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) ↔ incA D x⁻¹ * b ∈ intAt D (· = v) :=
    fun b hb => (hline v b hb).trans ((hgen b).trans ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩)
  have hent : ∀ b ∈ idAt D (· = v), ∀ k, (b • ratV z) k ∈ idAt D (· = v) := fun b hb k => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hb
  have hmove : ∀ b ∈ idAt D (· = v),
      b • ratV z ∈ latV S₀ M (· = v) ↔ (c * b) • ratV z ∈ latV S₀ M' (· = v) := by
    intro b hb
    rw [hmv _ (hent b hb), Matrix.mulVec_smul, hγ, smul_smul]
  have hcc : c * cA D c = 1 := hc.1
  have key : ∀ s ∈ idAt D (· = v),
      (∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) → colMul d.jX i (s * b) ∈ latV S L (· = v)) ↔
        (∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) →
          colMul d.jX i (c * (s * b)) ∈ latV S L' (· = v)) := by
    intro s hs
    rw [hL i hi s hs, ← hL' i hi s hs]
    constructor
    · intro h b hb hbM
      rw [show c * (s * b) = s * (c * b) by ring]
      exact h _ (Ideal.mul_mem_left _ _ hb) ((hmove b hb).1 hbM)
    · intro h b' hb' hb'M
      have hb : cA D c * b' ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hb'
      have hcb : c * (cA D c * b') = b' := by rw [← mul_assoc, hcc, one_mul]
      have := h _ hb ((hmove _ hb).2 (by rw [hcb]; exact hb'M))
      rwa [show c * (s * (cA D c * b')) = s * (c * (cA D c * b')) by ring, hcb] at this
  exact cancel v x hx (fun b => b • ratV z ∈ latV S₀ M (· = v)) hA
    (fun t => colMul d.jX i t ∈ latV S L (· = v)) (fun t => colMul d.jX i (c * t) ∈ latV S L' (· = v))
    (fun o ho t ht => by
      show colMul d.jX i (o * t) ∈ latV S L (· = v)
      rw [colMul_mul]
      exact GlobalTheory.FinPlLoc.smul_latV v ho ht)
    (fun o ho t ht => by
      show colMul d.jX i (c * (o * t)) ∈ latV S L' (· = v)
      rw [mul_left_comm, colMul_mul]
      exact GlobalTheory.FinPlLoc.smul_latV v ho ht)
    key a ha

end GlobalTheory.Core.Mi.LastLine

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastIsotropicLineHomothetyMatchesLatticesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.lastIsotropicLine_homothety_matches_lattices : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S₀ M → z ≠ 0 → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → ∀ i : Fin ρ, i.1 + 1 = ρ → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LastLine.lastLine_match | exact GlobalTheory.Core.Mi.LastLine.lastLine_match | (intros; apply GlobalTheory.Core.Mi.LastLine.lastLine_match <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneMatchesIsotropicYOfMatchesIsotropicX

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}


open GlobalTheory.IwaPlace in
theorem hermAt_colMul_jY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D)
    (x : Fin S.rank → AE D) : hermAt S (colMul d.jY i a) x = a * cA D ((d.pX *ᵥ x) i) := by
  have hg : ∀ j k, cA D (gA S j k) = gA S k j := fun j k => congrFun (congrFun (adj_gA S) k) j
  rw [d.pX_eq]

  simp only [hermAt, colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, adj, Matrix.transpose_apply,
  Matrix.map_apply, map_sum, map_mul, cA_cA, hg, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pX_colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (b : AE D) :
    (d.pX *ᵥ colMul d.jX i b) i = b := by
  have h := congrFun (congrFun d.pX_jX i) i
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.mulVec, dotProduct, colMul]
  calc ∑ k, d.pX i k * (b * d.jX k i) = b * ∑ k, d.pX i k * d.jX k i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = b := by rw [h, mul_one]

theorem mem_idAt_of_colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} (hL : IsSelfDualC S L)
    (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ) {b : AE D} (hb : colMul d.jX i b ∈ latV S L (· = v)) : b ∈ idAt D (· = v) := by
  rw [← pX_colMul_jX d i b]
  exact GlobalTheory.IwaPlace.mulVec_mem_idAt d.pX ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL).1 _ hb) i

theorem colMul_jY_mem_iff {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {M : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (hL : IsSelfDualC S L) (hM : MonoAt d L M v) (i : Fin ρ) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    colMul d.jY i a ∈ latV S L (· = v) ↔
      ∀ b, colMul d.jX i b ∈ latV S L (· = v) → a * cA D b ∈ intAt D (· = v) := by
  have hy : ∀ k, colMul d.jY i a k ∈ idAt D (· = v) := fun k => Ideal.mul_mem_right _ _ ha
  rw [(GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL).2.2 _ hy]
  constructor
  · intro h b hb
    have h1 := h _ hb
    rwa [hermAt_colMul_jY, pX_colMul_jX] at h1
  · intro h x hx
    rw [hermAt_colMul_jY]
    exact h _ (((hM x).1 hx).1 i)

theorem dualLine_match : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → IsSelfDualC S L' → MonoAt d L M v → MonoAt d L' M' v → NormOneAt v c → (∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v))) → ∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jY i a ∈ latV S L (· = v) ↔ colMul d.jY i (c * a) ∈ latV S L' (· = v)) := by
  intro D S S₀ ρ d L L' M M' v c hL hL' hM hM' hc hX i a ha
  have hca : c * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ha
  rw [colMul_jY_mem_iff d hL hM i ha, colMul_jY_mem_iff d hL' hM' i hca]
  have hcc : c * cA D c = 1 := hc.1
  constructor
  · intro h b' hb'
    have hbI : cA D c * b' ∈ idAt D (· = v) :=
      Ideal.mul_mem_left _ _ (mem_idAt_of_colMul_jX d hL' v i hb')
    have e : c * (cA D c * b') = b' := by rw [← mul_assoc, hcc, one_mul]
    have h1 : colMul d.jX i (cA D c * b') ∈ latV S L (· = v) := (hX i _ hbI).2 (by rw [e]; exact hb')
    have h2 := h _ h1
    rw [map_mul, cA_cA] at h2
    have e2 : c * a * cA D b' = a * (c * cA D b') := by ring
    rw [e2]
    exact h2
  · intro h b hb
    have h1 := (hX i b (mem_idAt_of_colMul_jX d hL v i hb)).1 hb
    have h2 := h _ h1
    have e : c * a * cA D (c * b) = a * cA D b := by
      rw [map_mul]
      calc c * a * (cA D c * cA D b) = (c * cA D c) * (a * cA D b) := by ring
        _ = a * cA D b := by rw [hcc, one_mul]
    rwa [e] at h2

end GlobalTheory.Core.Mi.LatMatch

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneMatchesIsotropicYOfMatchesIsotropicXStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.normOne_matchesIsotropicY_of_matchesIsotropicX : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → IsSelfDualC S L' → MonoAt d L M v → MonoAt d L' M' v → NormOneAt v c → (∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v))) → ∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jY i a ∈ latV S L (· = v) ↔ colMul d.jY i (c * a) ∈ latV S L' (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.dualLine_match | exact GlobalTheory.Core.Mi.LatMatch.dualLine_match | (intros; apply GlobalTheory.Core.Mi.LatMatch.dualLine_match <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomotheticOfMonomialPrimitiveSelfDualCores

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem homothetic_of_monomial_primitive_selfDual_cores : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S L → IsSelfDualC S L' → IsSelfDualC S₀ M → z ≠ 0 → MonoAt d L M v → MonoAt d L' M' v → PrimAt ψ d L v → PrimAt ψ d L' v → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → SMoves S c (d.emb0 γ) L L' v := by
  intro D ψ S S₀ ρ d z L L' M M' v c γ hL hL' hM hz hmL hmL' hpL hpL' hlL hlL' hc hγ hmv
  have hX : ∀ i : Fin ρ, ∀ a ∈ idAt D (· = v),
      (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
    suffices h : ∀ k : ℕ, ∀ i : Fin ρ, i.1 + k + 1 = ρ → ∀ a ∈ idAt D (· = v),
        (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) by
      intro i
      exact h (ρ - 1 - i.1) i (by omega)
    intro k
    induction k with
    | zero =>
      intro i hi
      exact GlobalTheory.T.lastIsotropicLine_homothety_matches_lattices D ψ S S₀ ρ d z L L' M M' v c γ hM hz hlL hlL' hc hγ hmv i (by omega)
    | succ k ih =>
      intro i hi
      exact GlobalTheory.T.primitive_character_matches_lines_down_flag D ψ S S₀ ρ d L L' v c hL hpL hpL' hc i ⟨i.1 + 1, by omega⟩ rfl
        (ih ⟨i.1 + 1, by omega⟩ (by simp only; omega))
  have hY := GlobalTheory.T.normOne_matchesIsotropicY_of_matchesIsotropicX D S S₀ ρ d L L' M M' v c hL hL' hmL hmL' hc hX
  intro y hy
  have hpX : d.pX *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) = c • (d.pX *ᵥ y) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
  have hpY : d.pY *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) = c • (d.pY *ᵥ y) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
  have hp0 : d.p0 *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) =
      c • (Formalism.L2.Theta.mt S₀ γ *ᵥ (d.p0 *ᵥ y)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding, ← Matrix.mulVec_mulVec]
  rw [hmL y, hmL' _, hpX, hpY, hp0]
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) ?_)
  · rw [Pi.smul_apply, smul_eq_mul]
    exact hX i _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  · rw [Pi.smul_apply, smul_eq_mul]
    exact hY i _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  · exact hmv _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy)

end GlobalTheory.Core.Mi.LatMatch
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomotheticOfMonomialPrimitiveSelfDualCoresStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.sMoves_emb0_of_sMoves_selfDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S L → IsSelfDualC S L' → IsSelfDualC S₀ M → z ≠ 0 → MonoAt d L M v → MonoAt d L' M' v → PrimAt ψ d L v → PrimAt ψ d L' v → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → SMoves S c (d.emb0 γ) L L' v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.homothetic_of_monomial_primitive_selfDual_cores | exact GlobalTheory.Core.Mi.LatMatch.homothetic_of_monomial_primitive_selfDual_cores | (intros; apply GlobalTheory.Core.Mi.LatMatch.homothetic_of_monomial_primitive_selfDual_cores <;> assumption)
end
end
