module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlgebraicCharacterOfAdm
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParams

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

namespace GlobalTheory.BridgeAdmDict

theorem sz_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) :
    AdmissibleParameterJ.sz D (D.nd.j i) ρ = (D.hc ρ).e (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.liftIdx D i) := by
  have := D.nd.j_range i
  unfold AdmissibleParameterJ.sz
  rw [dite_eq_left (by omega)]
  rfl

theorem PPm_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) :
    AdmissibleParameterJ.PPm D (D.nd.j i) ρ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.PP D i ρ := by
  unfold AdmissibleParameterJ.PPm GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.PP GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.param GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.run
  rw [sz_eq, Finset.range_val]

theorem mem_placesOver (D : D7) (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : InducesW D.nd i τ₀ w) :
    w ∈ placesOver D.host.E (D.nd.l i) := by
  have h1 := (h ((D.nd.l i : ℕ) : 𝓞 D.host.E)).1
  show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  apply h1
  have e : τ₀ (((D.nd.l i : ℕ) : 𝓞 D.host.E) : D.host.E) = algebraMap ℚ_[D.nd.l i] (PadicAlgCl (D.nd.l i)) (D.nd.l i : ℚ_[D.nd.l i]) := by
    simp
  rw [e, PadicAlgCl.norm_extends]
  simpa using (Padic.norm_p_lt_one (p := D.nd.l i))

end GlobalTheory.BridgeAdmDict
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsDictionaryAtEmbeddingOverRealPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

noncomputable section

namespace GlobalTheory.JumpDictRec

open GlobalTheory.JumpDictionaryFoundation

theorem main : ∀ D : D7, WeightParam D → BlockCharParam D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D →
    GlobalTheory.TwSys.Cheb → ∀ (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i)) (ρ : D.what₂.Tau) (b : Bool),
    (D.naut.iotaQC i).toRingHom.comp τ = embOver D ρ b → ∃ cτ : ℤ,
      (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℚ)) = (PP D i ρ).map (fun p => sgnOf true b * p + cτ) ∧
      ∀ w ∈ placesOver D.host.E (D.nd.l i),
        D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) w ∧
        (D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) τ).map (fun n : ℤ => (n : ℚ)) =
          {sgnOf true b * (-(D.hc ρ).e (liftIdx D i)) - ((D.R.t : ℚ) - 1) / 2 + cτ} := by
  intro D hW hB hG hC i τ ρ b hτ
  have hs := shift_embOver D ρ b
  refine ⟨shift D (embOver D ρ b), ?_, fun w hw => ?_⟩
  · apply Multiset.map_injective (f := fun q : ℚ => (q : ℂ)) Rat.cast_injective
    rw [Multiset.map_map, Multiset.map_map]
    have e0 := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ
    rw [hτ] at e0
    have e1 : (D.naut.locAutHodgeTateWeightsLevelZero i τ).map ((fun q : ℚ => (q : ℂ)) ∘ fun n : ℤ => (n : ℚ)) =
        (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℂ)) :=
      Multiset.map_congr rfl fun n _ => by simp
    rw [e1, e0]
    cases b
    · rw [(hW i ρ).1, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [Function.comp, sgnOf, hs]
      push_cast
      norm_num
      ring
    · rw [(hW i ρ).2, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [Function.comp, sgnOf, hs]
      push_cast
      norm_num
      ring
  · have ht : 1 ≤ D.R.t := by
      obtain ⟨u, v, -, hv, -⟩ := exists_halves D.R
      omega
    have hz : ∀ φ, ∃ z : ℤ, (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) φ).map
        (· + (blockExp D 1 : ℂ)) = {(z : ℂ)} := by
      intro φ
      obtain ⟨ρ', b', rfl⟩ := exists_embOver D φ
      obtain ⟨a, ha⟩ := firstJump_int D i ρ' b'
      refine ⟨-a, ?_⟩
      rw [inf_block D hB, ha]
      push_cast
      simp
    choose z hz using hz
    obtain ⟨r, hrc, hrf, hrd, hrj⟩ := hG i _ _ z hz
    have hr : r = mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1) := by
      have h := eq_of_frob D.nd hC i
        (a := fun g => ((r g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)
        (b := fun g => iotaOQ D.nd D.naut i ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i))
        ((continuous_apply 0).comp ((continuous_apply 0).comp hrc))
        ((continuous_iotaOQ D i w hw).comp (D.nd.chi_cont i 1)) fun v hv B σ hB' hσ => by
          have e1 := hrf v hv.2.1 (D.naut.chi_mu i v hv).1 B σ hB' hσ
          rw [chi_frob D i 1 le_rfl ht v hv B σ hB' hσ, Multiset.singleton_inj] at e1
          exact ((D.naut.iotaQC i).injective e1).symm
      ext g a c
      obtain rfl : a = 0 := Subsingleton.elim _ _
      obtain rfl : c = 0 := Subsingleton.elim _ _
      refine (congrFun h g).trans ?_
      rw [← chiGL_apply D i 1 g 0 0]
      rfl
    subst hr
    refine ⟨hrd w hw, ?_⟩
    have hq : firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1) = ((-z (embOver D ρ b) : ℤ) : ℚ) := by
      have e := (inf_block D hB i 1 ρ b).symm.trans (hz _)
      rw [Multiset.singleton_inj] at e
      have e' : -(firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1)) = (z (embOver D ρ b) : ℚ) := by exact_mod_cast e
      rw [Int.cast_neg, ← e', neg_neg]
    rw [hrj, hτ, Multiset.map_singleton, ← hq, hs]
    congr 1
    cases b
    · simp only [firstJump, sgnOf, Ranks.nV]
      push_cast
      norm_num
      ring
    · simp only [firstJump, sgnOf, Ranks.nV]
      push_cast
      norm_num
      ring

end GlobalTheory.JumpDictRec

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsDictionaryAtEmbeddingOverRealPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

theorem _root_.GlobalTheory.T.jumps_dictionary_at_embedding_over_realPlace : ∀ D : D7, WeightParam D → BlockCharParam D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D → GlobalTheory.TwSys.Cheb → ∀ (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i)) (ρ : D.what₂.Tau) (b : Bool), (D.naut.iotaQC i).toRingHom.comp τ = embOver D ρ b → ∃ cτ : ℤ, (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℚ)) = (PP D i ρ).map (fun p => sgnOf true b * p + cτ) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) w ∧ (D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) τ).map (fun n : ℤ => (n : ℚ)) = {sgnOf true b * (-(D.hc ρ).e (liftIdx D i)) - ((D.R.t : ℚ) - 1) / 2 + cτ} := by
  first | exact @GlobalTheory.JumpDictRec.main | exact GlobalTheory.JumpDictRec.main | (intros; apply GlobalTheory.JumpDictRec.main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAlt

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
namespace GlobalTheory.BridgeAdmDict
theorem main_alt_alt : GlobalTheory.TwSys.Cheb → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  intro hC D hA hW hB
  have hAC := _root_.GlobalTheory.T.algebraicCharacter_of_adm2 D hA
  refine ⟨false, ?_⟩
  rintro i τ₀ g ρ ⟨hτ, hP⟩
  obtain ⟨b, hb, hU⟩ : ∃ b : Bool, (D.naut.iotaQC i).toRingHom.comp τ₀ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ b ∧
      (AdmissibleParameterJ.TypeU D false g ↔ b = true) := by
    rcases hP with h | h
    · refine ⟨false, ?_, ?_⟩
      · rw [hτ, ← h]; rfl
      · subst h
        simp [AdmissibleParameterJ.TypeU, (D.eTau ρ).2]
    · refine ⟨true, ?_, ?_⟩
      · rw [hτ, ← h, Formalism.L2.Geo.emb_mul_cc_comp]; rfl
      · subst h
        have := (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau ρ).2
        simp [AdmissibleParameterJ.TypeU, this]
  obtain ⟨cτ, h1, h2⟩ := GlobalTheory.T.jumps_dictionary_at_embedding_over_realPlace D hW hB hAC hC i τ₀ ρ b hb
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.sgnOf true b, cτ, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [hU.1 h]; rfl
  · intro h
    cases b
    · rfl
    · exact absurd (hU.2 rfl) h
  · rw [PPm_eq]; exact h1
  · intro w hw
    obtain ⟨h3, h4⟩ := h2 w (mem_placesOver D i τ₀ w hw)
    refine ⟨h3, ?_⟩
    rw [show AdmissibleParameterJ.rankOneCharacterQbar D i = mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.chiGL D i 1) from rfl, h4, sz_eq]
    rfl
end GlobalTheory.BridgeAdmDict
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

theorem _root_.GlobalTheory.T.admDict_of_weight_blockChar : GlobalTheory.TwSys.Cheb → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  first | exact @_root_.GlobalTheory.BridgeAdmDict.main_alt_alt | exact _root_.GlobalTheory.BridgeAdmDict.main_alt_alt | (intros; apply _root_.GlobalTheory.BridgeAdmDict.main_alt_alt <;> assumption)
end
end
end
