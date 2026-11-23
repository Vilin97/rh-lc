module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Counterexamples.AnisotropicRankZero.WittSphericalSectionLeftInvariantRationalParabol

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AnisotropicResidueNonvanishing

variable {D : D7} {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r)

theorem isIwasawa (l : Lvl V) (hl : l.Good) (h : HasIw d l.K) : IsIwasawa (absDet d) l.K :=
  ⟨h, fun p hp => triv_of_isCompact (isClosed_stab d) (continuous_absDet d) hl.isCompact_K p hp⟩

theorem absDet_rat (q : stab d) (hq : (q : GA D V) ∈ GQ V) : absDet d q = 1 := by
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 ((mem_GQ_iff _ _).1 hq)
  have hα : (onX d q).1 = rat (d.qX * γ * d.e) := by
    rw [eq_of_mul_jX d (mul_jX d q), ← hγ, rat_mul, rat_mul, Matrix.mul_assoc]
    rfl
  have hdet : ((Matrix.GeneralLinearGroup.det (onX d q) : (AE D)ˣ) : AE D)
      = incA D (d.qX * γ * d.e).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hα, RingHom.map_det]
    rfl
  have hne : (d.qX * γ * d.e).det ≠ 0 := by
    intro h0
    have h1 : (1 : AE D) = 0 := by
      rw [← (Matrix.GeneralLinearGroup.det (onX d q)).mul_inv, hdet, h0, map_zero, zero_mul]
    exact one_ne_zero (incA_injective (D := D) (by rw [map_one, map_zero]; exact h1))
  have hu : Matrix.GeneralLinearGroup.det (onX d q)
      = Units.map (incA D).toMonoidHom (Units.mk0 _ hne) := Units.ext hdet
  show absA D (Matrix.GeneralLinearGroup.det (onX d q)) = 1
  rw [hu]
  exact absE_inclR _

theorem witt_spherical_section_left_invariant_rational_parabolic (l : Lvl V) (hl : l.Good) (h : HasIw d l.K) (s : ℂ) :
    LeftInv (stab d ⊓ GQ V) (sphericalSectionIwasawa d l.K s) := by
  have hI : IsIwasawa (absDet d) l.K := isIwasawa d l hl h
  intro γ hγ g
  have hγ' := Subgroup.mem_inf.1 hγ
  have e : iwAbs (absDet d) l.K (((⟨γ, hγ'.1⟩ : stab d) : GA D V) * g) = iwAbs (absDet d) l.K g := by
    rw [hI.iwAbs_left, absDet_rat d _ hγ'.2, one_mul]
  show npow (iwAbs (absDet d) l.K (γ * g)) _ = npow (iwAbs (absDet d) l.K g) _
  exact congrArg (fun t => npow t (s + (rhoH V r : ℂ))) e

end GlobalTheory.AnisotropicResidueNonvanishing

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnisotropicCoreWittFrame

section

@[expose] public section

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittFrameOfDec

theorem form_mulVec {D : D7} {n m : ℕ} (A : Matrix (Fin n) (Fin m) D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E)
    (w : Fin m → D.host.E) : star (A *ᵥ w) ⬝ᵥ (G *ᵥ (A *ᵥ w)) = star w ⬝ᵥ ((Aᴴ * G * A) *ᵥ w) := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem isWittFrame_of_hypDec (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (h : IsAniso T₀) :
    IsWittFrame D.sp.cm.sig T.gram d.e d.e' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cT_sig]; exact d.ee
  · rw [cT_sig]; exact d.e'e'
  · rw [cT_sig]
    have h1 := congrArg Matrix.conjTranspose d.e'e
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h1
    exact h1
  · intro z hX hY hz
    rw [cT_sig] at hX hY
    have hqY : d.qY *ᵥ z = 0 := hX
    have hqX : d.qX *ᵥ z = 0 := hY
    have hz0 : z = d.i₀ *ᵥ (d.q0 *ᵥ z) := by
      have := congrArg (fun M => M *ᵥ z) d.sum_eq_one_rat
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hqX, hqY,
        Matrix.mulVec_zero, zero_add, add_zero] at this
      exact this.symm
    obtain ⟨z₀, hz₀⟩ : ∃ w, w = d.q0 *ᵥ z := ⟨_, rfl⟩
    rw [← hz₀] at hz0
    by_cases h0 : z₀ = 0
    · rw [hz0, h0, Matrix.mulVec_zero]
    exfalso
    have e1 : hE D.sp.cm.sig T.gram z z = star z ⬝ᵥ (T.gram *ᵥ z) := by
      simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc]; rfl
    have hzz : star z₀ ⬝ᵥ (T₀.gram *ᵥ z₀) = 0 := by
      rw [← d.iso, ← form_mulVec, ← hz0, ← e1, hz]
    let C : Matrix (Fin T₀.rank) (Fin 1) D.host.E := Matrix.of fun i _ => z₀ i
    apply h 1 C
    refine ⟨Nat.one_pos, ?_, ?_⟩
    · change LinearIndependent D.host.E (fun _ : Fin 1 => z₀)
      exact linearIndependent_unique_iff.2 h0
    · rw [cT_sig]
      ext a b
      fin_cases a; fin_cases b
      have : (Cᴴ * T₀.gram * C) 0 0 = star z₀ ⬝ᵥ (T₀.gram *ᵥ z₀) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, C, Matrix.of_apply, dotProduct, Matrix.mulVec,
          Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      simpa using this.trans hzz

end GlobalTheory.WittFrameOfDec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittDecompositionIsotropicFrameEisensteinDiction

section

@[expose] public section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch GlobalTheory.ResidueEisenstein
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResidueDictionary

theorem dict : ∀ (D : D7) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ (r + 1)), IsAniso V₀ → ∀ l : Lvl V, l.Good → HasIw d l.K → DataJ D.sp.cm.sig V.gram d.e d.e' l.L l.c (fun g => (iwAbs (absDet d) l.K g : ℝ)) ∧ (∃ T, IsRepsJ D.sp.cm.sig V.gram d.e T) ∧ ∀ T, IsRepsJ D.sp.cm.sig V.gram d.e T → ∀ (g : GA D V) (s : ℂ), sphericalEisensteinSeriesOnGroup d l.K g s = ∑' t : T, (((iwAbs (absDet d) l.K (t.1.1 * g) : ℝ≥0) : ℝ) : ℂ) ^ (s + ((V.rank : ℂ) - (r + 1)) / 2) := by
  intro D V V₀ r d hA l hl hIw
  have hsc : ∀ q : stab d, ScalesBy D.sp.cm.sig V.gram d.e (q : GA D V) (onX d q) := fun q => mul_jX d q
  have hstab := (GlobalTheory.EisCont.parFlag_stab_leftInv D V V₀ (r + 1) d).2.2.1
  have hiff : ∀ x : GA D V, (∃ β, ScalesBy D.sp.cm.sig V.gram d.e x β) ↔ x ∈ stab d := fun x =>
    ⟨fun ⟨β, e⟩ => (hstab x β e).1, fun hx => ⟨_, hsc ⟨x, hx⟩⟩⟩
  have htriv := GlobalTheory.Doubling.triv_of_isCompact (isClosed_stab d) (continuous_absDet d) hl.isCompact_K

  have hmk : ∀ t γ : GQ V, GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) t = GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ ↔
      ((γ * t⁻¹ : GQ V) : GA D V) ∈ stab d := fun t γ => by
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    constructor
    · rintro ⟨δ, hδ⟩
      have : (γ * t⁻¹ : GQ V) = δ := by rw [← hδ]; group
      rw [this]; exact δ.2
    · intro h
      exact ⟨⟨γ * t⁻¹, h⟩, by simp⟩
  refine ⟨⟨isCMExt_host D, GlobalTheory.Doubling.isHermND_gram V, GlobalTheory.WittFrameOfDec.isWittFrame_of_hypDec D V V₀ _ d hA, hl.1,
    fun g => ?_, fun p β e k hk => ?_⟩, ?_, fun T hT g s => ?_⟩
  · obtain ⟨q, k, hk, rfl⟩ := hIw g
    exact ⟨q, onX d q, hsc q, k, hk, rfl⟩
  · obtain ⟨hp, rfl⟩ := hstab p β e
    have := iwAbs_mul_of_triv htriv ⟨p, hp⟩ hk
    rw [this]
    rfl
  · refine ⟨Set.range fun q : GlobalTheory.AutomorphicL2Unitary.Quot ((stab d).subgroupOf (GQ V)) => (q.out : GQ V), fun γ => ?_⟩
    refine ⟨(GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ).out, ⟨⟨_, rfl⟩, (hiff _).2 ((hmk _ _).1 (Quotient.out_eq _))⟩, ?_⟩
    rintro t' ⟨⟨q, rfl⟩, ht'⟩
    have e := (hmk q.out γ).2 ((hiff _).1 ht')
    have e2 : q = GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ := (Quotient.out_eq q).symm.trans e
    subst e2
    rfl
  · have hbij : Function.Bijective fun t : T => GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) (t.1 : GQ V) := by
      constructor
      · rintro ⟨t, ht⟩ ⟨t', ht'⟩ e
        have e' := (hmk _ _).1 e
        obtain ⟨u, -, hu⟩ := hT t'
        have h1 := hu t' ⟨ht', (hiff _).2 (by simp)⟩
        have h2 := hu t ⟨ht, (hiff _).2 e'⟩
        exact Subtype.ext (h2.trans h1.symm)
      · intro q
        induction q using Quotient.inductionOn with
        | h γ =>
          obtain ⟨t, ⟨ht, hs⟩, -⟩ := hT γ
          exact ⟨⟨t, ht⟩, (hmk _ _).2 ((hiff _).1 hs)⟩
    change cosetSum (stab d) (GQ V) (sphericalSectionIwasawa d l.K s) g = _
    rw [GlobalTheory.Eis.cosetSum_eq_tsum (GlobalTheory.AnisotropicResidueNonvanishing.witt_spherical_section_left_invariant_rational_parabolic d l hl hIw s) hbij g]
    refine tsum_congr fun t => ?_
    simp only [sphericalSectionIwasawa, npow, rhoH]
    congr 1
    push_cast
    ring

end GlobalTheory.ResidueDictionary
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittDecompositionIsotropicFrameEisensteinDictionStatement

section

@[expose] public section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch GlobalTheory.ResidueEisenstein
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wittDecomposition_isotropicFrameEisenstein_dictionary : ∀ (D : D7) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ (r + 1)), IsAniso V₀ → ∀ l : Lvl V, l.Good → HasIw d l.K → DataJ D.sp.cm.sig V.gram d.e d.e' l.L l.c (fun g => (iwAbs (absDet d) l.K g : ℝ)) ∧ (∃ T, IsRepsJ D.sp.cm.sig V.gram d.e T) ∧ ∀ T, IsRepsJ D.sp.cm.sig V.gram d.e T → ∀ (g : GA D V) (s : ℂ), sphericalEisensteinSeriesOnGroup d l.K g s = ∑' t : T, (((iwAbs (absDet d) l.K (t.1.1 * g) : ℝ≥0) : ℝ) : ℂ) ^ (s + ((V.rank : ℂ) - (r + 1)) / 2) := by
  first | exact @GlobalTheory.ResidueDictionary.dict | exact GlobalTheory.ResidueDictionary.dict | (intros; apply GlobalTheory.ResidueDictionary.dict <;> assumption)
end
end
