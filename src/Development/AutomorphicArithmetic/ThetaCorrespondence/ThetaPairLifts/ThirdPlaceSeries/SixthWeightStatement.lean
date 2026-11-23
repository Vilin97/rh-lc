module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.RankOneOfLong
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartFrobEigNormO

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatement

section

@[expose] public section

noncomputable section

namespace GlobalTheory.FrobeniusCharacterNorms

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem normV_pos (w : PlE H) : 0 < normV w := by
  have h := GlobalTheory.LocalInv.one_lt_normV w
  have : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by linarith
  exact_mod_cast this

theorem frob_one {w : PlE H} {a : A.LP w} (hu : A.unr a) (hd : A.lpDim a = 1) : ∃ c, A.frobEig a = {c} :=
  Multiset.card_eq_one.1 (by rw [A.frobEig_card a hu, hd])

theorem eta_frob (hAut : At.TieAut N A) (w : PlE H) : ∃ b, A.frobEig (A.locG A.etaT w) = {b} ∧ ‖b‖ = 1 := by
  obtain ⟨b, hb⟩ := frob_one (A.etaT_unr w) (A.locG_dim A.etaT w)
  refine ⟨b, hb, (A.tempered_unr _ (A.etaT_unr w)).1 (hAut.2.2.1 w) b ?_⟩
  rw [hb]
  exact Multiset.mem_singleton_self b

theorem norm_first_character_frobenius (hAut : At.TieAut N A) (i : N.Loc) {w : PlE H} (hw : SplitOut N i w)
    (huμ : A.unr (A.locG (A.muC i) w)) {B : ValuationSubring N.Om} {σ : G H.E N.Om}
    (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    ‖A.iotaQC i (iotaOQ N A i (chi1 N i σ))‖ =
      (normV w : ℝ) ^ (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2) := by
  obtain ⟨hu, hf⟩ := A.chi_mu i w hw
  have e : A.frobEig (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w) (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2)) =
      {A.iotaQC i (iotaOQ N A i (chi1 N i σ))} := hf B σ hB hσ
  rw [A.frobEig_tw _ _ hu, A.locG_tw] at e
  obtain ⟨m, hm⟩ := frob_one huμ (A.locG_dim (A.muC i) w)
  have hm1 : ‖m‖ = 1 := (A.tempered_unr _ huμ).1 (hAut.2.2.2 i w) m (by rw [hm]; exact Multiset.mem_singleton_self m)
  obtain ⟨b, hb, hb1⟩ := eta_frob hAut w
  obtain ⟨hui, hfi⟩ := A.etaTinv_def w
  have hfi' : A.frobEig (A.locG A.etaTinv w) = {b⁻¹} := by rw [hfi, hb, Multiset.map_singleton]
  have hfe := A.frobEig_char (A.locG (A.muC i) w) (A.locG A.etaTinv w) b⁻¹ huμ hui (A.locG_dim _ w) hfi'
  rw [hfe, hm, Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj] at e
  rw [← e, norm_mul, norm_mul, hm1, norm_inv, hb1, inv_one, one_mul, one_mul,
    Complex.norm_natCast_cpow_of_pos (normV_pos w), Complex.ofReal_re]

theorem eps_frob (i : N.Loc) {w : PlE H} (hl : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    A.iotaQC i (iotaOQ N A i ((Glob.epsO N i σ : (N.O i)ˣ) : N.O i)) = (normV w : ℂ) := by
  have hc := cycZ_of_isFrob (F := H.E) (Ω := N.Om) (l := N.l i) (by simpa [placesOver] using hl) hB hσ
  have e1 : ((Glob.epsO N i σ : (N.O i)ˣ) : N.O i) =
      algebraMap ℤ_[N.l i] (N.O i) ((cycZ H.E N.Om (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) := rfl
  rw [e1, hc]
  show A.iotaQC i (A.iotaQ i (algebraMap (N.O i) (FractionRing (N.O i))
    (algebraMap ℤ_[N.l i] (N.O i) ((normV w : ℕ) : ℤ_[N.l i])))) = _
  rw [A.iotaQ_alg i, PadicInt.coe_natCast, map_natCast, map_natCast]

end GlobalTheory.FrobeniusCharacterNorms

namespace GlobalTheory.FrobeniusCharacterNorms

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

end GlobalTheory.FrobeniusCharacterNorms
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthWeightPurity

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.FrobeniusCharacterNorms
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
end GlobalTheory.FrobeniusCharacterNorms
namespace GlobalTheory.FrobeniusCharacterNorms
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
theorem sixth_weight_purity_alt_alt : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' := by
  intro D hA i x P Pa hxP hBC k R hR j hj hv
  have hAut : At.TieAut D.nd D.naut := hA.1.1.1.2.1
  have hC := hA.1.1.2.2.2.2.2.2.2.2.1
  have hp : Pa.get k ∈ Pa := List.get_mem Pa k
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) ∪
      {w | ¬ D.naut.unr (D.naut.locG (Pa.get k).π w)} ∪
      {w | ¬ D.naut.unr (D.naut.locG (D.naut.muC i) w)} : Set (PlE D.host)).Finite := by
    have h1 : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
      ((placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union
        (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
    exact (h1.union (Filter.eventually_cofinite.1 (D.naut.locG_unr_ae (Pa.get k).π))).union
      (Filter.eventually_cofinite.1 (D.naut.locG_unr_ae (D.naut.muC i)))
  have hne := (hC _ hfin).symm ▸ Set.mem_univ (1 : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)
  obtain ⟨σ, ⟨w, hw, hsp, B, hB, hσ⟩⟩ : Set.Nonempty {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ (placesOver D.host.E (D.nd.l i) ∪
      ↑(D.nd.S i) ∪ ↑(D.nd.Q i) ∪ {w | ¬ D.naut.unr (D.naut.locG (Pa.get k).π w)} ∪
      {w | ¬ D.naut.unr (D.naut.locG (D.naut.muC i) w)} : Set (PlE D.host)), IsSplitPl D.host w ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hne
    exact hne
  simp only [Set.mem_union, not_or, Finset.mem_coe, Set.mem_setOf_eq, not_not] at hw
  have hl := hw.1.1.1.1
  have hwo : SplitOut D.nd i w := ⟨hsp, hl, hw.1.1.1.2, hw.1.1.2⟩
  have huπ := hw.1.2
  have huμ := hw.2
  have hR := _root_.UpperTheory.GalS.strN' hR
  have hwd := (hR.2.2 w hl).eq_of_unr ((D.naut.unr_tw _ _).2 huπ)
  have hU : D.naut.unr (D.naut.wdOf i R w) := by rw [hwd]; exact (D.naut.unr_tw _ _).2 huπ
  have hF := D.naut.wdOf_frob i R w hl hR.1 hU B σ hB hσ
  rw [hwd, D.naut.frobEig_tw _ _ huπ] at hF
  obtain ⟨v, hv0, hvg⟩ := hv
  have h1 := hvg σ
  set M : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i)) :=
    ((R σ : GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))) with hM
  set c : Qbar (D.nd.l i) := iotaOQ D.nd D.naut i (chi1 D.nd i σ) with hc
  have he0 : epsQ D i σ ≠ 0 :=
    ((Units.isUnit (Formalism.MainNotions.N.Glob.epsO D.nd i σ)).map (iotaOQ D.nd D.naut i)).ne_zero
  have hMv : M.mulVec v = (epsQ D i σ ^ j * c) • v := by
    have h2 := congrArg (fun u => (epsQ D i σ ^ j) • u) h1
    simp only [smul_smul, inv_pow] at h2
    rw [mul_inv_cancel₀ (pow_ne_zero _ he0), one_smul] at h2
    exact h2
  have hdet : (Matrix.scalar (Fin (Pa.get k).a) (epsQ D i σ ^ j * c) - M).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, hMv]
    ext t
    simp [Matrix.scalar_apply]
  have hroot : (M.charpoly.map (D.naut.iotaQC i).toRingHom).IsRoot
      ((D.naut.iotaQC i).toRingHom (epsQ D i σ ^ j * c)) :=
    Polynomial.IsRoot.map (D.naut.iotaQC i).toRingHom
      (by rw [Polynomial.IsRoot.def, Matrix.eval_charpoly]; exact hdet)
  rw [hF] at hroot
  have hmem := (Polynomial.mem_roots (Polynomial.monic_multiset_prod_of_monic _ _
    (fun a _ => Polynomial.monic_X_sub_C a)).ne_zero).2 hroot
  rw [Polynomial.roots_multiset_prod_X_sub_C] at hmem
  obtain ⟨α, hα, hαe⟩ := Multiset.mem_map.1 hmem
  have hα1 := (_root_.GlobalTheory.PartUnitary.frobEig_openB_and_norm_one_of_isBCV D hA.1.1.1 hA.1.2 i P Pa hBC (Pa.get k) hp w huπ α hα).1
  have hq0 : 0 < normV w := normV_pos w
  have hq1 : (1 : ℝ) < normV w := GlobalTheory.LocalInv.one_lt_normV w
  have hε : D.naut.iotaQC i (epsQ D i σ) = (normV w : ℂ) := eps_frob i hl hB hσ
  have hχ := norm_first_character_frobenius hAut i hwo huμ hB hσ
  have hn := congrArg norm hαe
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow, hε, norm_mul, norm_pow,
    Complex.norm_natCast_cpow_of_pos hq0, Complex.ofReal_re, Complex.norm_natCast] at hn
  rw [hc, hχ, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)] at hn
  have hx := hα1.exp_eq (UpperTheory.GalN.one_lt_q w) hn (2 * (j : ℤ) + D.R.t - (Pa.get k).d) (by push_cast; ring)
  have hz : (((Pa.get k).d : ℤ) - 1 - 2 * j : ℝ) = ((D.R.t : ℤ) - 1 : ℝ) := by push_cast; linarith
  exact_mod_cast hz
end GlobalTheory.FrobeniusCharacterNorms
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthWeightStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.purity_string_weight : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' := by
  first | exact @_root_.GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt | exact _root_.GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt | (intros; apply _root_.GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt <;> assumption)
end
end
end
