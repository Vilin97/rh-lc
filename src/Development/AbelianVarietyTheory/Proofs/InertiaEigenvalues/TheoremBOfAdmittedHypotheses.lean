module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleShapeAndEpsilonAtEveryLocalisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalConditionAllLocalizations
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
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockBoundQdPlacesUniformConstStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosingNumericalInequalityTheoremBStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldsAtAuxiliaryPrimesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulLtFinrankCyclotomicAtQAndDStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowPlacesSatisfyRowHypothesisAtQAndDStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDegPosAndSumLe
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoHypothesisGlobalStepAtQd

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.BKAtQD

theorem admBK_embeddingTypeJumps : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) →
    ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  intro D hBK hLit i hi w hw C
  obtain ⟨-, hTD, -⟩ := hLit i hi
  exact ⟨(hTD w hw C).1, (hTD w hw C).2,
    fun _ => TruncatedSeriesCountingIdentities.bkBAt_of_core _ _ _ (hBK _ _).2.2.2.1 (GlobalTheory.AdmBK.litGoodO_all _ _)⟩

end GlobalTheory.BKAtQD
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoHypothesisGlobalStepAtQdStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.blochKatoHypothesis_globalStep_at_qd : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  first | exact @GlobalTheory.BKAtQD.admBK_embeddingTypeJumps | exact GlobalTheory.BKAtQD.admBK_embeddingTypeJumps | (intros; apply GlobalTheory.BKAtQD.admBK_embeddingTypeJumps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBLocalDegreeSumBounds

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.QDDeg

theorem locDeg_sum_le_and_ge : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := by
  intro D h1 i hi s hs
  have hl : (D.nd.l i).Prime := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.hyp.1
    · exact D.host.hyp.2.1
  have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
    rcases hi with h | h <;> simp [h]
  obtain ⟨hpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le D.host.E (D.nd.l i) hl
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  refine ⟨(hsum s hs).trans hfr.le, ?_⟩
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun w hw => ?_
  have he : w.asIdeal.ramificationIdx ℤ = 2 := ((h1 _ hmem).2 w (hs w hw)).1
  have hp := hpos w
  unfold Formalism.MainNotions.N.locDeg at hp ⊢
  rw [he] at hp ⊢
  omega

end GlobalTheory.Proof.QDDeg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBLocalDegreeSumBoundsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.theoremB_localDegree_sum_bounds : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := by
  first | exact @GlobalTheory.Proof.QDDeg.locDeg_sum_le_and_ge | exact GlobalTheory.Proof.QDDeg.locDeg_sum_le_and_ge | (intros; apply GlobalTheory.Proof.QDDeg.locDeg_sum_le_and_ge <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBRamifiedPrimesNeTypePrimes

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.TypePrimesQD

theorem not_split_of_ram_two (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hram : ∀ v ∈ placesOver E l, v.asIdeal.ramificationIdx ℤ = 2)
    (hsplit : (placesOver E l).ncard = Module.finrank ℚ E) : False := by
  classical
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : (placesOver E l).Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨hdpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le E l hl
  have hle := hsum hfin.toFinset (fun v hv => hfin.mem_toFinset.1 hv)
  have hge : ∑ v ∈ hfin.toFinset, 2 ≤ ∑ v ∈ hfin.toFinset, Formalism.MainNotions.N.locDeg E v := by
    refine Finset.sum_le_sum fun v hv => ?_
    have h2 := hram v (hfin.mem_toFinset.1 hv)
    have hp := hdpos v
    unfold Formalism.MainNotions.N.locDeg at hp ⊢
    rw [h2] at hp ⊢
    omega
  rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hsplit] at hge
  omega

theorem qd_ne_typePrimes : ∀ (D : D7), Formalism.MainNotions.EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc,
    (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := by
  intro D h1 i hl
  have key : ∀ k : Fin 2, D.nd.l i ≠ D.host.g k := by
    intro k hk
    have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
      rcases hl with h | h <;> simp [h]
    have hram := (h1 _ hmem).2
    rw [hk] at hram
    exact not_split_of_ram_two D.host.E (D.host.g k) (D.host.g_prime k)
      (fun v hv => (hram v hv).1) (D.nd.g_split k)
  exact ⟨key 0, key 1⟩

end GlobalTheory.Proof.TypePrimesQD
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBRamifiedPrimesNeTypePrimesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.theoremB_ramifiedPrimes_ne_typePrimes : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := by
  first | exact @GlobalTheory.Proof.TypePrimesQD.qd_ne_typePrimes | exact GlobalTheory.Proof.TypePrimesQD.qd_ne_typePrimes | (intros; apply GlobalTheory.Proof.TypePrimesQD.qd_ne_typePrimes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfAdmittedHypotheses

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TheoremB

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem declNoColumns : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, dc.col = ∅ := by
  intro D i _
  have hf := placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
  exact ⟨⟨hf.toFinset, ∅, Finset.disjoint_empty_right _, fun v => by simp⟩, rfl⟩

theorem localDelta_le_cuspTwistDepth : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.vdel i ≤ (D.R.t : ℚ) := by
  intro D i hl
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have htr : D.R.t ≤ D.R.t * D.R.r := Nat.le_mul_of_pos_right _ hr1
  have h4 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
  have hlt : D.R.t < D.nd.l i := by
    rcases hl with h | h <;> rw [h]
    · have := D.host.qd_big.1; rw [h4] at this; omega
    · have := D.host.qd_big.2; rw [h4] at this; omega
  have hl2 : D.nd.l i ≠ 2 := by have := D.R.rank_add_five_le; omega
  unfold NData.vdel
  rw [UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i (UpperTheory.Small.not_mem_of_qd D.host hl)]
  have hk : ∀ k ∈ Finset.Ioo 0 D.R.t, ((1 : ℕ) : ℚ) + (padicValNat (D.nd.l i) k : ℚ) = 1 := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))]
    simp
  rw [Finset.sum_congr rfl hk]
  simp

theorem rowBound : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := GlobalTheory.T.rowPlaces_satisfy_rowHypothesis_at_q_and_d

theorem tbConst : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∃ cB : ℕ, TruncatedSeriesCountingIdentities.admTB i (r i) π cB ∧ (cB : ℝ) ≤ 60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b := GlobalTheory.T.blockBound_qd_places_uniformConst

theorem bkAt : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := GlobalTheory.T.blochKatoHypothesis_globalStep_at_qd

theorem cycDegree_gt : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := GlobalTheory.T.mul_lt_finrank_cyclotomic_at_q_and_d

theorem ne_typePrimes : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := GlobalTheory.T.theoremB_ramifiedPrimes_ne_typePrimes

theorem degBounds : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := GlobalTheory.T.theoremB_localDegree_sum_bounds

theorem closingIneq : ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := GlobalTheory.T.closing_numerical_inequality_theoremB

theorem theoremB_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 13 * max CA 0 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  intro D HW F r ρ large₂ ep CA C Qp hC hP hW hA hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hTB hBK hKill hJump hFon hLit hPar
  obtain ⟨h0, h1⟩ := GlobalTheory.T.local_fields_at_auxiliary_primes D
  intro i hl tw hbig π hπ hsF hsha
  have hQ : EmbeddingTypeJumps.AtQD i := ⟨⟨hl, tw⟩, ⟨π, (D.Zgood_tie i π).1 hπ⟩⟩
  obtain ⟨dc, hcol⟩ := declNoColumns D i hl
  obtain ⟨lenRow, hROW, hRowB⟩ := rowBound D r ρ large₂ ep CA h0 h1 hA hJump hFon hG2 hSet hLit hPar i hQ π hπ dc
  obtain ⟨cB, hTBi, hcB⟩ := tbConst D HW F r ρ large₂ ep h0 h1 hW hTB hJump hFon hG2 hSet hLit hPar i hQ π hπ
  have hAdm : TruncatedSeriesCountingIdentities.admitted i (r i) (ρ i) π dc lenRow (fun _ => 0) cB := by
    refine ⟨hG1 i hQ, hG2 i hQ π hπ, hG3 i hQ π hπ, hG4 i hQ, hG5 i hQ, (hLit i hQ).1, hG6 i hQ,
      bkAt D hBK hLit i hQ, hTBi, hROW, ?_, (hSet i hQ π hπ).1, (hSet i hQ π hπ).2.1,
      (hSet i hQ π hπ).2.2.1, (hSet i hQ π hπ).2.2.2, (hLit i hQ).2.2.1, (GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main D i).1,
      (hLit i hQ).2.2.2.1, (hLit i hQ).2.2.2.2.1, (hLit i hQ).2.2.2.2.2⟩
    intro w hw hwc
    simp [hcol] at hwc
  obtain ⟨hg0, hg1⟩ := ne_typePrimes D h1 i hl
  have key := hN5 i π dc lenRow (fun _ => 0) cB hAdm hg0 hg1 (LargeLevelLemmas.zgoodSubsetZ i hπ) hsF hsha
  have hlw : ∀ w ∈ dc.row, TruncatedSeriesCountingIdentities.lenW i (ρ i) π dc lenRow (fun _ => 0) w = lenRow w := by
    intro w _
    unfold TruncatedSeriesCountingIdentities.lenW
    rw [dite_eq_right (by simp [hcol])]
  rw [hcol] at key
  simp only [Finset.union_empty] at key
  rw [Finset.sum_congr rfl hlw] at key
  simp only [Finset.card_empty, Nat.cast_zero, zero_add, mul_one, mul_zero, zero_mul, add_zero] at key
  have keyR := (Rat.cast_le (K := ℝ)).2 key
  push_cast at keyR
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hmr : D.R.m ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; omega
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf1 : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  have hl3 : 3 ≤ D.nd.l i := by
    have htr : 1 ≤ D.R.t * D.R.r := Nat.mul_pos ht1 hr1
    rcases hl with h | h <;> rw [h]
    · have := D.host.qd_big.1; nlinarith
    · have := D.host.qd_big.2; nlinarith
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hL0 : 0 < large₂.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hb1 : 1 < large₂.sc.b := by unfold Scale.b; have := Real.add_one_lt_exp (ne_of_gt hL0); linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hLb : 1 < Real.log large₂.sc.b := by
    unfold Scale.b; rw [Real.log_exp]; unfold Scale.L
    exact Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrowP : ∀ w ∈ dc.row, w ∈ placesOver D.host.E (D.nd.l i) := fun w hw => (dc.cover w).1 (Or.inl hw)
  obtain ⟨hSD, hSC⟩ := degBounds D h1 i hl dc.row hrowP
  have hSDr : ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) ≤ 2 * D.R.f := by exact_mod_cast hSD
  have hSCr : 2 * (dc.row.card : ℝ) ≤ ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) := by exact_mod_cast hSC
  set SD : ℝ := ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) with hSDdef
  set K := max CA 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  set X := 4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ) with hX
  have hl3r : (3 : ℝ) ≤ D.nd.l i := by exact_mod_cast hl3
  have hX0 : 0 ≤ X := by
    have : 0 ≤ Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) := Real.logb_nonneg (by linarith) (by linarith)
    have := large₂.Sc_pos; have := large₂.etaSz_pos
    have : 0 ≤ 4 * large₂.sc.b / (D.nd.l i : ℝ) := by positivity
    positivity
  set Y := 2 * large₂.sc.b + 1 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hRw : (∑ w ∈ dc.row, (lenRow w : ℝ)) ≤
      K * (3 * (D.R.f : ℝ) * D.R.r * X + 6 * (D.R.f : ℝ) * D.R.m * Y) + D.R.f := by
    have hcard : (dc.row.card : ℝ) ≤ D.R.f := by linarith
    have hsum : (∑ w ∈ dc.row, (K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
        3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1)) =
        (K * D.R.r * X + 3 * K * D.R.m * Y) * SD + dc.row.card * (K * D.R.r * X + 1) := by
      have : ∀ w ∈ dc.row, K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
          3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1 =
          (K * D.R.r * X + 3 * K * D.R.m * Y) * ((locDeg D.host.E w : ℕ) : ℝ) + (K * D.R.r * X + 1) := by
        intro w _; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hSDdef]
      push_cast; ring
    have e1 : (K * D.R.r * X + 3 * K * D.R.m * Y) * SD ≤ (K * D.R.r * X + 3 * K * D.R.m * Y) * (2 * D.R.f) :=
      mul_le_mul_of_nonneg_left hSDr (by positivity)
    have e2 : (dc.row.card : ℝ) * (K * D.R.r * X + 1) ≤ D.R.f * (K * D.R.r * X + 1) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    calc (∑ w ∈ dc.row, (lenRow w : ℝ)) ≤ ∑ w ∈ dc.row, (K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
          3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1) := Finset.sum_le_sum hRowB
      _ = (K * D.R.r * X + 3 * K * D.R.m * Y) * SD + dc.row.card * (K * D.R.r * X + 1) := hsum
      _ ≤ (K * D.R.r * X + 3 * K * D.R.m * Y) * (2 * D.R.f) + D.R.f * (K * D.R.r * X + 1) := add_le_add e1 e2
      _ = K * (3 * (D.R.f : ℝ) * D.R.r * X + 6 * (D.R.f : ℝ) * D.R.m * Y) + D.R.f := by ring
  have hTb : (D.R.t : ℝ) * ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ) ≤
      240 * (D.R.t : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + D.R.t) * Real.log large₂.sc.b := by
    have hs : ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ) = (SD + 2 * dc.row.card) * cB := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hSDdef]
      push_cast; ring
    rw [hs]
    have h4 : SD + 2 * (dc.row.card : ℝ) ≤ 4 * D.R.f := by linarith
    have hc0 : (0 : ℝ) ≤ cB := by positivity
    have hS0 : (0 : ℝ) ≤ SD + 2 * (dc.row.card : ℝ) := by positivity
    calc (D.R.t : ℝ) * ((SD + 2 * dc.row.card) * cB) ≤ (D.R.t : ℝ) * ((4 * D.R.f) *
          (60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b)) := by
          gcongr
      _ = 240 * (D.R.t : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + D.R.t) * Real.log large₂.sc.b := by ring
  have hVd : 4 * (D.R.nV : ℝ) * ((D.nd.vdel i : ℚ) : ℝ) ≤ 4 * ((D.R.r : ℝ) + D.R.t) * D.R.t := by
    rw [hnV]
    have h1' : ((D.nd.vdel i : ℚ) : ℝ) ≤ D.R.t := by exact_mod_cast localDelta_le_cuspTwistDepth D i hl
    have : (0 : ℝ) ≤ D.R.r + D.R.t := by positivity
    nlinarith
  have hK2 := (hKill i hl tw (Or.inr (cycDegree_gt D h1 i hl)) π hπ).2
  simp only [EmbeddingTypeJumps.vZeta] at hK2
  push_cast at hK2
  have har := closingIneq CA C large₂.sc.b (D.nd.l i) large₂.Sc large₂.etaSz (∑ w ∈ dc.row, (lenRow w : ℝ))
    ((D.R.t : ℝ) * ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ))
    (4 * (D.R.nV : ℝ) * ((D.nd.vdel i : ℚ) : ℝ)) D.R.f D.R.r D.R.t D.R.m (EmbeddingTypeJumps.polyVal Qp D.R.f D.R.r D.R.t)
    hC (hP _ _ _) ht1 hf1 hmr hl3r large₂.Sc_pos.le large₂.etaSz_pos.le hb0 hLb hRw hTb hVd
  unfold EmbeddingTypeJumps.bndB
  push_cast
  linarith [keyR, hK2, har]

end GlobalTheory.TheoremB
end
end
