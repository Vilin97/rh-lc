module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowers
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FieldDictionaryHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowersNeZero
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.PicardGroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramDeterminantFormula
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LinearIndependentOfDetGram
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowersEqInv

section

@[expose] public section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Loc

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem le_locS (S : Submonoid R) (L : Submodule R W) : L ≤ Formalism.HermitianLatticesTheory.locS S L := fun x hx => ⟨1, S.one_mem, by simpa using hx⟩

theorem locS_mono (S : Submonoid R) {L M : Submodule R W} (h : L ≤ M) :
    Formalism.HermitianLatticesTheory.locS S L ≤ Formalism.HermitianLatticesTheory.locS S M := fun x ⟨s, hs, hx⟩ => ⟨s, hs, h hx⟩

theorem locS_idem (S : Submonoid R) (L : Submodule R W) :
    Formalism.HermitianLatticesTheory.locS S (Formalism.HermitianLatticesTheory.locS S L) = Formalism.HermitianLatticesTheory.locS S L := by
  apply le_antisymm
  · rintro x ⟨s, hs, t, ht, hx⟩
    refine ⟨t * s, S.mul_mem ht hs, ?_⟩
    rw [mul_smul]
    exact hx
  · exact le_locS S _

theorem locS_eq_of (S : Submonoid R) {L M : Submodule R W} (h1 : L ≤ Formalism.HermitianLatticesTheory.locS S M)
    (h2 : M ≤ Formalism.HermitianLatticesTheory.locS S L) : Formalism.HermitianLatticesTheory.locS S L = Formalism.HermitianLatticesTheory.locS S M := by
  apply le_antisymm
  · calc Formalism.HermitianLatticesTheory.locS S L ≤ Formalism.HermitianLatticesTheory.locS S (Formalism.HermitianLatticesTheory.locS S M) := locS_mono S h1
      _ = Formalism.HermitianLatticesTheory.locS S M := locS_idem S M
  · calc Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S (Formalism.HermitianLatticesTheory.locS S L) := locS_mono S h2
      _ = Formalism.HermitianLatticesTheory.locS S L := locS_idem S L

theorem iInf_localization_eq [IsDedekindDomain R] (hR : ¬ IsField R) (L : Submodule R W) :
    (⨅ P : HeightOneSpectrum R, haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L) = L := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_iInf] at hx
    by_contra hxL
    let I : Ideal R := L.comap (LinearMap.toSpanSingleton R W x)
    have hI : I ≠ ⊤ := by
      intro h
      apply hxL
      have h1 : (1 : R) ∈ I := h ▸ Submodule.mem_top
      simpa [I] using h1
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
    have hM0 : M ≠ ⊥ := by
      intro h
      apply hR
      rw [h] at hM
      exact Ring.isField_iff_maximal_bot.2 hM
    obtain ⟨s, hs, hsx⟩ := hx ⟨M, hM.isPrime, hM0⟩
    exact hs (hIM (by simpa [I] using hsx))
  · exact le_iInf fun P => le_locS _ L

end Loc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def JdS (D : Formalism.BasicNotions.D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

def GDiffPrime : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (P : HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
    ∃ s ∈ JdS D, s ∉ P.asIdeal

theorem differentIdealPowers_eq_inv (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) :
    ∃ k : ℕ, differentIdealPowers D i = ((((JdS D) ^ k : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · refine ⟨0, ?_⟩
    rw [differentIdealPowers, Fin.snoc_last, pow_zero, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top, inv_one]
  · refine ⟨D.R.rS - (a : ℕ), ?_⟩
    have hcast : ((D.R.rS : ℤ) - (a : ℕ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
      have := a.isLt
      omega
    rw [differentIdealPowers, Fin.snoc_castSucc, hcast, zpow_neg, zpow_natCast, FractionalIdeal.coeIdeal_pow]
    rfl

theorem JdS_pow_ne_zero (D : Formalism.BasicNotions.D7) (k : ℕ) :
    ((((JdS D) ^ k : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, ← Ideal.zero_eq_bot]
  apply pow_ne_zero
  rw [Ideal.zero_eq_bot, JdS, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
  exact differentIdeal_ne_bot

theorem one_mem_aa (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) (o : 𝓞 D.host.E) :
    (o : D.host.E) ∈ differentIdealPowers D i := by
  obtain ⟨k, hk⟩ := differentIdealPowers_eq_inv D i
  rw [hk, FractionalIdeal.mem_inv_iff (JdS_pow_ne_zero D k)]
  intro y hy
  obtain ⟨a, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  exact (FractionalIdeal.mem_one_iff _).2 ⟨o * a, by rw [map_mul]⟩

theorem clear_aa (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) (s : 𝓞 D.host.E) (hs : s ∈ JdS D) :
    ∃ k : ℕ, ∀ c ∈ differentIdealPowers D i, ∃ o : 𝓞 D.host.E, (o : D.host.E) = ((s ^ k : 𝓞 D.host.E) : D.host.E) * c := by
  obtain ⟨k, hk⟩ := differentIdealPowers_eq_inv D i
  refine ⟨k, fun c hc => ?_⟩
  rw [hk, FractionalIdeal.mem_inv_iff (JdS_pow_ne_zero D k)] at hc
  have hsk : ((s ^ k : 𝓞 D.host.E) : D.host.E) ∈
      ((JdS D ^ k : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨s ^ k, Ideal.pow_mem_pow hs k, rfl⟩
  have h1 := hc _ hsk
  rw [mul_comm] at h1
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  exact ⟨o, ho⟩

theorem smul_O_E {D : Formalism.BasicNotions.D7} (o : 𝓞 D.host.E) (v : (VS D).V) : o • v = ((o : D.host.E)) • v := (algebraMap_smul D.host.E o v).symm

theorem mem_pb {D : Formalism.BasicNotions.D7} {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (i : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (c : D.host.E) (hc : c ∈ Sum.elim (differentIdealPowers D) (differentIdealPowers D) i) :
    c • flagDifferenceVectors D F0 F' i ∈ pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) := Submodule.subset_span ⟨i, c, hc, rfl⟩

theorem loc_g (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (P : HeightOneSpectrum (𝓞 D.host.E)) (s : 𝓞 D.host.E) (hsJ : s ∈ JdS D) (hsP : s ∉ P.asIdeal) :
    haveI := P.isPrime
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MMg D F0 F') =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D))) := by
  haveI := P.isPrime
  apply locS_eq_of
  · refine (Submodule.span_le.mpr ?_).trans (le_locS _ _)
    rintro v (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · have := mem_pb F0 F' (Sum.inl a) _ (one_mem_aa D a 1)
      simpa [flagDifferenceVectors] using this
    · have := mem_pb F0 F' (Sum.inr b) _ (one_mem_aa D b 1)
      simpa [flagDifferenceVectors] using this
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨i, c, hc, rfl⟩
    have hc' : c ∈ Sum.elim (differentIdealPowers D) (differentIdealPowers D) i := hc
    obtain ⟨k, hk⟩ := clear_aa D (Sum.elim id id i) s hsJ
    have hc2 : c ∈ differentIdealPowers D (Sum.elim id id i) := by rcases i with a | a <;> exact hc'
    obtain ⟨o, ho⟩ := hk c hc2
    refine ⟨s ^ k, fun h => hsP (P.isPrime.mem_of_pow_mem k h), ?_⟩
    rw [smul_O_E, smul_smul, ← ho, ← smul_O_E]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rcases i with a | b
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨b, rfl⟩

theorem gS_ne_zero' (D : Formalism.BasicNotions.D7) : ((gS D : D.host.E)) ≠ 0 := by
  have h : gS D ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  exact_mod_cast h

theorem aa_castSucc (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) :
    differentIdealPowers D (Fin.castSucc a) = ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) := by
  rw [differentIdealPowers, Fin.snoc_castSucc]

theorem aa_last (D : Formalism.BasicNotions.D7) : differentIdealPowers D (Fin.last D.R.rS) = 1 := by
  rw [differentIdealPowers, Fin.snoc_last]

theorem mem_UUS_fvec (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (a : Fin (D.R.rS + 1)) (c : D.host.E) (hc : c ∈ differentIdealPowers D a) :
    c • F0.fvec a ∈ UUS D F0 F' ∧ c • F'.fl.fvec a ∈ UUS D F0 F' := by
  induction a using Fin.lastCases with
  | last =>
    rw [aa_last, FractionalIdeal.mem_one_iff] at hc
    obtain ⟨o, rfl⟩ := hc
    simp only [FlagG.fvec, Fin.snoc_last]
    rw [← smul_O_E, ← smul_O_E]
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.smul_mem _ o (Submodule.mem_span_singleton_self _))))
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ o (Submodule.mem_span_singleton_self _))
  | cast a =>
    rw [aa_castSucc] at hc
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.subset_span ⟨a, c, hc, rfl⟩)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, c, hc, rfl⟩))

theorem UUS_le_pb (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') : UUS D F0 F' ≤ pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) := by
  have hg := gS_ne_zero' D
  have key : ∀ (a : Fin (D.R.rS + 1)) (c : D.host.E), c ∈ differentIdealPowers D a →
      c • F0.fvec a ∈ pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) ∧
      c • F'.fl.fvec a ∈ pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) := by
    intro a c hc
    refine ⟨mem_pb F0 F' (Sum.inl a) c hc, ?_⟩
    have hgc : ((gS D : D.host.E)) * c ∈ differentIdealPowers D a := by
      have := Submodule.smul_mem (differentIdealPowers D a : Submodule (𝓞 D.host.E) D.host.E) ((gS D : ℕ) : 𝓞 D.host.E) hc
      rwa [Algebra.smul_def, map_natCast] at this
    have e : c • F'.fl.fvec a = (((gS D : D.host.E)) * c) • flagDifferenceVectors D F0 F' (Sum.inr a) + c • flagDifferenceVectors D F0 F' (Sum.inl a) := by
      simp only [flagDifferenceVectors, Sum.elim_inr, Sum.elim_inl]
      have hgc' : (((gS D : D.host.E)) * c) • (((gS D : D.host.E))⁻¹ • (F'.fl.fvec a - F0.fvec a)) =
          c • (F'.fl.fvec a - F0.fvec a) := by
        rw [smul_smul]
        congr 1
        field_simp
      rw [hgc', smul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (mem_pb F0 F' (Sum.inr a) _ hgc) (mem_pb F0 F' (Sum.inl a) c hc)
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨a, c, hc, rfl⟩
    have := (key (Fin.castSucc a) c (by rw [aa_castSucc]; exact hc)).1
    simpa [FlagG.fvec] using this
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have := (key (Fin.last _) 1 (by simpa using one_mem_aa D (Fin.last D.R.rS) 1)).1
    simpa [FlagG.fvec] using this
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨a, c, hc, rfl⟩
    have := (key (Fin.castSucc a) c (by rw [aa_castSucc]; exact hc)).2
    simpa [FlagG.fvec] using this
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have := (key (Fin.last _) 1 (by simpa using one_mem_aa D (Fin.last D.R.rS) 1)).2
    simpa [FlagG.fvec] using this

theorem loc_ng (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    haveI := P.isPrime
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UUS D F0 F') =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D))) := by
  haveI := P.isPrime
  have hg := gS_ne_zero' D
  apply locS_eq_of
  · exact (UUS_le_pb D F0 F').trans (le_locS _ _)
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨i, c, hc, rfl⟩
    rcases i with a | b
    · exact le_locS _ _ (mem_UUS_fvec D F0 F' a c hc).1
    · refine ⟨((gS D : ℕ) : 𝓞 D.host.E), hP, ?_⟩
      have e : ((gS D : ℕ) : 𝓞 D.host.E) • (c • flagDifferenceVectors D F0 F' (Sum.inr b)) = c • F'.fl.fvec b - c • F0.fvec b := by
        rw [smul_O_E]
        simp only [flagDifferenceVectors, Sum.elim_inr, smul_smul]
        push_cast
        rw [← smul_sub]
        congr 1
        field_simp
      rw [e]
      exact Submodule.sub_mem _ (mem_UUS_fvec D F0 F' b c hc).2 (mem_UUS_fvec D F0 F' b c hc).1

open Classical in
theorem mmPseudo_of (hg : GDiffPrime) : MMPseudo := by
  intro D u u' _ F0 what₂ _ Z F' _ _ _ _
  have hP : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (haveI := P.isPrime
       if ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal then Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MMg D F0 F')
       else Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UUS D F0 F')) =
      (haveI := P.isPrime
       Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)))) := by
    intro P
    split_ifs with h
    · obtain ⟨s, hsJ, hsP⟩ := hg D P h
      exact loc_g D F0 F' P s hsJ hsP
    · exact loc_ng D F0 F' P h
  unfold MMof
  rw [iInf_congr hP]
  exact iInf_localization_eq (NumberField.RingOfIntegers.not_isField D.host.E) _

theorem congruence_prime_different : GDiffPrime := by
  intro D P hP
  haveI := P.isPrime
  have hg : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    apply P.isPrime.mem_or_mem
    unfold gS at hP
    exact_mod_cast hP
  have key : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ s ∈ JdS D, s ∉ P.asIdeal := by
    intro i hi
    set n := Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F))
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F), ?_, ?_⟩
    · exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem _)
    · intro hn
      rw [map_natCast] at hn
      have hc := (Formalism.L2.SG.SplitPrimeNormLemmas.IntG.coprime_gi (D := D) i).cast (R := 𝓞 D.host.E)
      obtain ⟨a, b, hab⟩ := hc
      have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
        rw [← hab]
        exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hi)
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  rcases hg with h | h
  · exact key 0 h
  · exact key 1 h

theorem mass_pseudo_basis : MMPseudo := mmPseudo_of congruence_prime_different

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FinrankOFOE

section

@[expose] public section

open NumberField Module Formalism.MainNotions.S

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_OF_OE (D : Formalism.BasicNotions.D7) : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [D.host.der.finrank_E, D.host.der.finrank_F] at h1
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  rw [D.host.der.finrank_E] at hpos

  have key : ∀ o x : ℕ, 2 * o * x = 4 * o → 0 < 4 * o → x = 2 := by
    intro o x h hp
    have ho : 0 < 2 * o := by omega
    exact Nat.eq_of_mul_eq_mul_left ho (by rw [h]; ring)
  exact key _ _ h1 hpos

theorem absNorm_ddS (D : Formalism.BasicNotions.D7) :
    FractionalIdeal.absNorm (ddS D) = (((NumberField.discr D.host.F).natAbs : ℚ)) ^ 2 := by
  have h := FractionalIdeal.absNorm_eq' (K := D.host.E) (I := ddS D) 1
    (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)))
    (by
      first
        | (open scoped Pointwise in rw [one_smul]; rfl)
        | (exact (one_smul _ _).trans rfl)
        | (open scoped Pointwise in simp; rfl))
  rw [h, Ideal.absNorm_algebraMap, finrank_OF_OE,
    NumberField.absNorm_differentIdeal (K := D.host.F)]
  simp

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ProdAbsNormDifferentIdealPowers

section

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical ValuativeRel

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gZ_ne_zero (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D)
    (hpos : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ T T' Z)) : GZ T T' Z ≠ 0 := by
  intro h0
  have hc : 0 < Fintype.card D.what₂.Tau := by
    rw [D.what₂.card_Tau]
    have := D.R.m_le_f
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    omega
  obtain ⟨τ⟩ := Fintype.card_pos_iff.mp hc
  have := hpos τ
  rw [h0, map_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem gS_ne_zero (D : Formalism.BasicNotions.D7) : ((gS D : D.host.E)) ≠ 0 := by
  have h1 := (D.host.g_prime 0).pos
  have h2 := (D.host.g_prime 1).pos
  unfold gS
  exact_mod_cast (Nat.mul_pos h1 h2).ne'

theorem prod_tri {c : ℚ} (hc : c ≠ 0) :
    ∀ n : ℕ, (∏ a : Fin n, c ^ (-((n : ℤ) - (a : ℕ)))) ^ 2 = c ^ (-((n * (n + 1) : ℕ) : ℤ))
  | 0 => by simp
  | n + 1 => by
    rw [Fin.prod_univ_succ, mul_pow]
    have h1 : ∀ a : Fin n, c ^ (-(((n + 1 : ℕ) : ℤ) - ((a.succ : Fin (n + 1)) : ℕ))) =
        c ^ (-((n : ℤ) - (a : ℕ))) := by
      intro a
      congr 1
      simp only [Fin.val_succ]
      push_cast
      ring
    simp only [h1, prod_tri hc n, Fin.val_zero]
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hc]
    congr 1
    push_cast
    ring

theorem prod_absNorm_differentIdealPowers (D : Formalism.BasicNotions.D7) :
    (∏ a : Fin (D.R.rS + 1), FractionalIdeal.absNorm (differentIdealPowers D a)) ^ 2 =
      (((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ^ (-((D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) := by
  have hd : (((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ≠ 0 := by
    have := NumberField.discr_ne_zero D.host.F
    positivity
  rw [Fin.prod_univ_castSucc]
  simp only [differentIdealPowers, Fin.snoc_castSucc, Fin.snoc_last, map_one, mul_one, map_zpow₀, absNorm_ddS]
  exact prod_tri hd D.R.rS

theorem abs_norm_negOnePow {K : Type} [Field K] [NumberField K] (k : ℕ) (y : K) :
    |(Algebra.norm ℚ ((-1) ^ k * y) : ℚ)| = |(Algebra.norm ℚ y : ℚ)| := by
  rw [map_mul, map_pow, abs_mul, abs_pow]
  have h1 : |(Algebra.norm ℚ (-1 : K) : ℚ)| = 1 := by
    have h2 : (Algebra.norm ℚ (-1 : K)) * (Algebra.norm ℚ (-1 : K)) = 1 := by
      rw [← map_mul]; simp
    have h3 : |(Algebra.norm ℚ (-1 : K) : ℚ)| * |(Algebra.norm ℚ (-1 : K) : ℚ)| = 1 := by
      rw [← abs_mul, h2, abs_one]
    nlinarith [abs_nonneg (Algebra.norm ℚ (-1 : K) : ℚ)]
  rw [h1, one_pow, one_mul]

theorem normMM_of (hN : NMPseudo) (hM : MMPseudo) (hΔ : DetGa) : NormMM := by
  intro D u u' hc F0 what₂ hr Z F' hz hZ hpos hint
  have hMM := hM D u u' hc F0 what₂ hr Z F' hz hZ hpos hint
  rw [hMM] at hint ⊢
  obtain ⟨hcm, hfix, -⟩ := field_dictionary_holds D
  have hG := gZ_ne_zero D _ _ Z hpos
  have hg := gS_ne_zero D
  have hdetGa := hΔ D (Tn u) (Tn u') (star_natCast _) (star_natCast _) Z
  have hdet := det_gram_flagDifference F0 F' Z hZ
  rw [hdetGa] at hdet
  have hdet0 : (gram (VS D).hT (flagDifferenceVectors D F0 F')).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hg)) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hG)
  have hstar : ∀ i, ∀ a ∈ ((Sum.elim (differentIdealPowers D) (differentIdealPowers D) i : FractionalIdeal _ _) : Submodule (𝓞 D.host.E) D.host.E),
      star a ∈ ((Sum.elim (differentIdealPowers D) (differentIdealPowers D) i : FractionalIdeal _ _) : Submodule (𝓞 D.host.E) D.host.E) := by
    rintro (a | a) <;> exact stable_differentIdealPowers D a
  have hne : ∀ i, (Sum.elim (differentIdealPowers D) (differentIdealPowers D) i) ≠ 0 := by
    rintro (a | a) <;> exact differentIdealPowers_ne_zero D a
  have hsq := hN D.host.E D.host.F (VS D).V _ (VS D).hT (UPair D F0 F') (flagDifferenceVectors D F0 F')
    (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) hcm hfix D.sp.cm.deg2 (VS D).herm hstar hne
    (linearIndependent_of_det_gram _ _ hdet0) (span_flagDifferenceBasis F0 F') hdet0 hint

  have hm : D.R.m = 2 * (D.R.rS + 1) := by
    have h2 := D.R.two_le_m
    obtain ⟨a, ha⟩ := D.R.m_even
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hy : (gram (VS D).hT (flagDifferenceVectors D F0 F')).det = (-1) ^ (D.R.rS + 1) * (GZ (Tn u) (Tn u') Z / ((gS D : D.host.E) ^ D.R.m)) := by
    rw [hdet, hm, div_eq_mul_inv, ← inv_pow]
    ring
  have hN2 : (FractionalIdeal.absNorm ((∏ i, (Sum.elim (differentIdealPowers D) (differentIdealPowers D) i) ^ 2) *
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (gram (VS D).hT (flagDifferenceVectors D F0 F')).det) : ℝ) =
      ((((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ^ (-((D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) : ℚ) ^ 2 *
        |(Algebra.norm ℚ (GZ (Tn u) (Tn u') Z / ((gS D : D.host.E) ^ D.R.m)) : ℚ)| := by
    rw [map_mul, FractionalIdeal.absNorm_span_singleton, hy, abs_norm_negOnePow, map_prod,
      Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, map_pow]
    rw [Finset.prod_pow, ← prod_absNorm_differentIdealPowers D]
    push_cast
    ring
  have hnm0 : 0 ≤ nM D.host.F (VS D).hT (UPair D F0 F') (pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D))) :=
    tprod_nonneg fun _ => by positivity
  have hr0 : 0 ≤ |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) *
      sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z := by
    unfold sqrtAbsNormOfScaledGram; positivity
  refine (pow_left_inj₀ hnm0 hr0 two_ne_zero).mp ?_
  rw [hsq, hN2, mul_pow]
  unfold sqrtAbsNormOfScaledGram
  rw [Real.sq_sqrt (abs_nonneg _)]
  congr 1
  have hcast : (((NumberField.discr D.host.F).natAbs : ℕ) : ℝ) = |(NumberField.discr D.host.F : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  push_cast
  rw [hcast]
  have e1 : (|(NumberField.discr D.host.F : ℝ)| ^ 2) ^ (-((D.R.rS : ℤ) * (D.R.rS + 1))) =
      |(NumberField.discr D.host.F : ℝ)| ^ (-(2 * (D.R.rS : ℤ) * (D.R.rS + 1))) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [e1]
  exact Rat.cast_abs _

theorem normMM_of_NM (hN : NMPseudo) : NormMM :=
  normMM_of hN mass_pseudo_basis gram_determinant_formula_alt

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
end
