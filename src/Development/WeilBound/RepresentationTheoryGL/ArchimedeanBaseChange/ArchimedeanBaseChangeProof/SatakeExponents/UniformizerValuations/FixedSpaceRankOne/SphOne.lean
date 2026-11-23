module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.FinrankFixedEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentraliz
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CayleyRuleOfBiInvariantVacuumCoefficient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
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
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseDoubleCosetNonsplit

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.PRep
open GlobalTheory.CuspRep Formalism.BasicNotions
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.InvDoubleCoset

section Generic

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def wJ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) : GL (Fin n) L :=
  ⟨antiJ L n, antiJ L n, GlobalTheory.UnitarySwap.antiJ_mul_self, GlobalTheory.UnitarySwap.antiJ_mul_self⟩

theorem cT_antiJ (σ : L →+* L) : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, antiJ]
  by_cases h : i.val + j.val + 1 = n
  · rw [if_pos h, if_pos (by omega)]; simp
  · rw [if_neg h, if_neg (by omega)]; simp

theorem wJ_mem_GU (σ : L →+* L) : wJ L n ∈ GU σ n := by
  change cT σ (antiJ L n) * antiJ L n * antiJ L n = antiJ L n
  rw [cT_antiJ, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]

theorem wJ_mem_GLint (O : Subring L) : wJ L n ∈ GLint (Fin n) O := by
  have h : ∀ i j, antiJ L n i j ∈ O := fun i j => by
    simp only [antiJ]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  exact GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨h, h⟩

theorem wJ_conj_diag {σ : L →+* L} {ϖ : L} (hϖ : σ ϖ = ϖ) (d : Fin n → ℤ) (t : GU σ n)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) : wJ L n * t.1 * wJ L n = (t.1)⁻¹ := by
  have h0 : cT σ t.1.1 * antiJ L n * t.1.1 = antiJ L n := t.2
  have hc : cT σ t.1.1 = t.1.1 := by
    rw [ht]
    ext i j
    by_cases h : i = j
    · subst h
      simp [cT, map_zpow₀, hϖ]
    · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [hc] at h0
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  change antiJ L n * t.1.1 * antiJ L n * t.1.1 = 1
  calc antiJ L n * t.1.1 * antiJ L n * t.1.1 = antiJ L n * (t.1.1 * antiJ L n * t.1.1) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h0, GlobalTheory.UnitarySwap.antiJ_mul_self]

end Generic

theorem inv_mem_doubleCoset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (g : UL n w),
      ∃ k₁ ∈ KL n w, ∃ k₂ ∈ KL n w, g⁻¹ = k₁ * g * k₂ := by
  intro E _ _ _ hU w hw n g
  obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, -⟩, -⟩ := hns hw
  obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hUI (B := 1) (one_mem _) (cT_one _)
  have hb' : cT (cj w) b.val * b.val = antiJ _ n := by simpa using hb
  have hconj : ∀ x : GLw n w, b * x * b⁻¹ ∈ UL n w ↔ x ∈ UJ (cj w) (antiJ _ n) := fun x => by
    rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
    exact GlobalTheory.CompanionTheory.UnitaryWitt.conj_mem_UJ_one_iff _ b x hb'
  have hback : b⁻¹ * g.1 * b ∈ UJ (cj w) (antiJ _ n) :=
    (hconj _).1 (by rw [show b * (b⁻¹ * g.1 * b) * b⁻¹ = g.1 by group]; exact g.2)
  have hbi := (GlobalTheory.LFun.KGL w (n := n)).inv_mem hbK
  have hO : Ov E w = intL (w.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  have hKU : ∀ k ∈ KU (cj w) n, (k.1 : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) := fun k hk => by
    have h : k.1 ∈ intPts (intL (w.adicCompletion E)).subtype (GU (cj w) n) := Subgroup.mem_subgroupOf.1 hk
    show k.1 ∈ (bc (Ov E w).subtype).range
    rw [hO]
    exact (Subgroup.mem_inf.1 h).2
  obtain ⟨d, t, ht, k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.ChainOnto.CayleyVac.exists_cartanU hUI ⟨_, hback⟩
  have e' : b⁻¹ * g.1 * b = k₁.1 * t.1 * k₂.1 := congrArg Subtype.val e
  have hinv : (t.1)⁻¹ = wJ _ n * t.1 * wJ _ n := (wJ_conj_diag hUI.2.2.1 d t ht).symm

  set c : GLw n w := (k₂.1 : GLw n w)⁻¹ * wJ _ n * (k₁.1 : GLw n w)⁻¹ with hc
  have hcU : c ∈ UJ (cj w) (antiJ _ n) :=
    mul_mem (mul_mem (inv_mem k₂.2) (wJ_mem_GU _)) (inv_mem k₁.2)
  have hcK : c ∈ GlobalTheory.LFun.KGL w (n := n) :=
    mul_mem (mul_mem (inv_mem (hKU k₂ hk₂)) (wJ_mem_GLint _)) (inv_mem (hKU k₁ hk₁))
  have hx : b * c * b⁻¹ ∈ UL n w := (hconj _).2 hcU
  have hxK : (⟨b * c * b⁻¹, hx⟩ : UL n w) ∈ KL n w :=
    Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK hcK) hbi)
  refine ⟨_, hxK, _, hxK, Subtype.ext ?_⟩
  show (g.1)⁻¹ = b * c * b⁻¹ * g.1 * (b * c * b⁻¹)
  have hg : g.1 = b * (k₁.1 * t.1 * k₂.1) * b⁻¹ := by
    rw [← e']
    group
  have hti : (k₁.1 * t.1 * k₂.1 : GLw n w)⁻¹ = c * (k₁.1 * t.1 * k₂.1) * c := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hinv, hc]
    group
  calc (g.1)⁻¹ = b * (k₁.1 * t.1 * k₂.1 : GLw n w)⁻¹ * b⁻¹ := by
        rw [hg]
        group
    _ = b * c * b⁻¹ * g.1 * (b * c * b⁻¹) := by
        rw [hti, hg]
        group

end GlobalTheory.CompanionTheory.InvDoubleCoset
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseDoubleCosetNonsplitStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inverse_double_coset_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (g : UL n w), ∃ k₁ ∈ KL n w, ∃ k₂ ∈ KL n w, g⁻¹ = k₁ * g * k₂ := by
  first | exact @GlobalTheory.CompanionTheory.InvDoubleCoset.inv_mem_doubleCoset | exact GlobalTheory.CompanionTheory.InvDoubleCoset.inv_mem_doubleCoset | (intros; apply GlobalTheory.CompanionTheory.InvDoubleCoset.inv_mem_doubleCoset <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.SphOne

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.EigA

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem relIndex_conj_KL_ne_zero (n : ℕ) (w : Pl E) (g : UL n w) :
    ((KL n w).map (MulAut.conj g).toMonoidHom).relIndex (KL n w) ≠ 0 := by
  have hK : IsCompact (KL n w : Set (UL n w)) := GlobalTheory.LocFinU.isCompact_KL n w
  have hKo : IsOpen (KL n w : Set (UL n w)) := GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w
  have hH : IsOpen (((KL n w).map (MulAut.conj g).toMonoidHom : Subgroup (UL n w)) : Set (UL n w)) := by
    rw [GlobalTheory.LocFinU.conj_map_eq]
    exact ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ hKo
  exact GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hH hK

theorem gelPair_split (n : ℕ) (w : Pl E) (hw : IsSplitAt w) : GelPair (KL n w) := by
  have hmem : ∀ x : GLw n w, x ∈ UL n w := fun x => by
    have h : UL n w = ⊤ := if_pos hw
    rw [h]
    exact Subgroup.mem_top x
  refine ⟨relIndex_conj_KL_ne_zero n w, fun g => ⟨Formalism.UG.P.heckecomm_tr g.1, hmem _⟩, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact Subtype.ext (Formalism.UG.P.heckecomm_tr_mul a.1 b.1)
  · intro a
    exact Subtype.ext (Formalism.UG.P.heckecomm_tr_tr a.1)
  · intro g
    obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp E w n g.1
    exact ⟨⟨a, hmem _⟩, Subgroup.mem_subgroupOf.2 a.2, ⟨b, hmem _⟩, Subgroup.mem_subgroupOf.2 b.2, Subtype.ext e⟩
  · intro k hk
    exact Subgroup.mem_subgroupOf.2 (Formalism.UG.P.heckecomm_tr_mem (Ov E w) k.1 (Subgroup.mem_subgroupOf.1 hk))

theorem gelPair_inert (hE : Unr E) (n : ℕ) (w : Pl E) (hw : ¬ IsSplitAt w) : GelPair (KL n w) :=
  ⟨relIndex_conj_KL_ne_zero n w, fun g => g⁻¹, fun a b => mul_inv_rev a b, fun a => inv_inv a,
    fun g => GlobalTheory.T.inverse_double_coset_nonsplit E hE w hw n g, fun _ hk => (KL n w).inv_mem hk⟩

theorem gelPair_KL (hE : Unr E) (n : ℕ) (w : Pl E) : GelPair (KL n w) := by
  by_cases hw : IsSplitAt w
  · exact gelPair_split n w hw
  · exact gelPair_inert hE n w hw

end PositivityTheory.Rg.BcB.F.EigA

end
end
end
