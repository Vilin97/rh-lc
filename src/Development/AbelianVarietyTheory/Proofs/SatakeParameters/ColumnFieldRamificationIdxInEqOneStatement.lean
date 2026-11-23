module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

-- Source module: Formalism.LocalToGlobal.Columns.BaseHost

section

@[expose] public section

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)


end Host

section Host2

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)



variable (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (hE : H.EQ ≤ LL)




end Host2

section Host3

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)
variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)


end Host3

theorem ram_conj_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hrank : Module.finrank F E = 2) (c : 𝓞 E →+* 𝓞 E) (hcc : ∀ x, c (c x) = x)
    (hcF : ∀ a : 𝓞 F, c (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a)
    (P : HeightOneSpectrum (𝓞 E))
    (hP : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) (x : 𝓞 E) :
    c x - x ∈ P.asIdeal := by
  classical
  set p : Ideal (𝓞 F) := P.asIdeal.under (𝓞 F) with hp
  have hPmax : P.asIdeal.IsMaximal := P.isMaximal
  have hPprime : P.asIdeal.IsPrime := P.isPrime
  have hpmax : p.IsMaximal := Ideal.IsMaximal.under (𝓞 F) P.asIdeal
  have hp0 : p ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) P.ne_bot
  have hlies : P.asIdeal.LiesOver p := ⟨rfl⟩
  have hmap0 : p.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).not.2 hp0

  let Q : Ideal (𝓞 E) := P.asIdeal.comap c
  have hQprime : Q.IsPrime := Ideal.comap_isPrime c P.asIdeal
  have hQlies : Q.LiesOver p := by
    refine ⟨?_⟩
    ext a
    show a ∈ p ↔ c (algebraMap (𝓞 F) (𝓞 E) a) ∈ P.asIdeal
    rw [hcF]
    rfl
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hfr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← hrank]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  rw [hfr] at hsum
  have he : 2 ≤ P.asIdeal.ramificationIdx (𝓞 F) := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p P.asIdeal hmap0]
    have hfin : FiniteMultiplicity P.asIdeal (p.map (algebraMap (𝓞 F) (𝓞 E))) :=
      FiniteMultiplicity.of_not_isUnit (fun h => hPprime.ne_top (Ideal.isUnit_iff.1 h)) hmap0
    exact hfin.le_multiplicity_of_pow_dvd (Ideal.dvd_iff_le.2 hP)
  have hfP : 0 < P.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos P.asIdeal (𝓞 F)
  have hfQ : 0 < Q.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos Q (𝓞 F)
  have heQ : 0 < Q.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos (R := 𝓞 F) Q
  let P' : p.primesOver (𝓞 E) := ⟨P.asIdeal, hPprime, hlies⟩
  let Q' : p.primesOver (𝓞 E) := ⟨Q, hQprime, hQlies⟩

  have hQP : Q = P.asIdeal := by
    by_contra hne
    have hne' : Q' ≠ P' := fun h => hne (congrArg Subtype.val h)
    have h2 : ∑ q ∈ ({P', Q'} : Finset (p.primesOver (𝓞 E))), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) ≤
        ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair hne'.symm, hsum] at h2
    have h3 : 2 ≤ P.asIdeal.ramificationIdx (𝓞 F) * P.asIdeal.inertiaDeg (𝓞 F) := by nlinarith
    have h4 : 1 ≤ Q.ramificationIdx (𝓞 F) * Q.inertiaDeg (𝓞 F) := Nat.mul_pos heQ hfQ
    have h5 : P'.1 = P.asIdeal := rfl
    have h6 : Q'.1 = Q := rfl
    rw [h5, h6] at h2
    omega

  have hf1 : P.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    have h2 : P'.1.ramificationIdx (𝓞 F) * P'.1.inertiaDeg (𝓞 F) ≤
        ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) :=
      Finset.single_le_sum (f := fun q : p.primesOver (𝓞 E) => q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ P')
    rw [hsum] at h2
    have h5 : P'.1 = P.asIdeal := rfl
    rw [h5] at h2
    nlinarith
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P.asIdeal] at hf1
  let : Field (𝓞 F ⧸ p) := Ideal.Quotient.field p
  let : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  obtain ⟨a', ha'⟩ := (finrank_eq_one_iff_of_nonzero' (1 : 𝓞 E ⧸ P.asIdeal) one_ne_zero).1 hf1 (Ideal.Quotient.mk P.asIdeal x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  have hxa : x - algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq, ← ha', Algebra.smul_def, mul_one]
    rfl
  have hc : c (x - algebraMap (𝓞 F) (𝓞 E) a) ∈ P.asIdeal := by
    rw [← hQP]
    show c (c (x - algebraMap (𝓞 F) (𝓞 E) a)) ∈ P.asIdeal
    rw [hcc]
    exact hxa
  rw [map_sub, hcF] at hc
  have := P.asIdeal.sub_mem hc hxa
  have e : c x - algebraMap (𝓞 F) (𝓞 E) a - (x - algebraMap (𝓞 F) (𝓞 E) a) = c x - x := by ring
  rwa [e] at this

theorem Fields.Ok.ram_conj {X : Fields} (h : X.Ok) (P : HeightOneSpectrum (𝓞 X.E))
    (hP : (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2) (x : 𝓞 X.E) :
    X.conjO x - x ∈ P.asIdeal := by
  refine ram_conj_mem h.rankE X.conjO ?_ ?_ P hP x
  · intro y
    apply RingOfIntegers.ext
    show star (star (y : X.E)) = y
    exact star_star _
  · intro a
    apply RingOfIntegers.ext
    exact h.star_F (a : X.F)

theorem Fields.Ok.unram_of_inertia {X : Fields} (h : X.Ok)
    (hin : ∀ P : HeightOneSpectrum (𝓞 X.E), ¬ ∀ x : 𝓞 X.E, X.conjO x - x ∈ P.asIdeal) (P : HeightOneSpectrum (𝓞 X.E)) :
    ¬ (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2 :=
  fun hP => hin P (h.ram_conj P hP)

end Formalism.L2.Col
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldRamificationIdxInEqOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain

namespace GlobalTheory.ColumnField

theorem conj_notMem_inertia (D : D7) (X : Fields) (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    ¬ ∀ x : 𝓞 X.E, X.conjO x - x ∈ P.asIdeal := by
  intro hall
  let φ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE
  let P' : Ideal (𝓞 D.host.E) := P.asIdeal.comap (φ.symm : 𝓞 D.host.E →+* 𝓞 X.E)
  have hmax : P'.IsMaximal :=
    have := P.isMaximal
    Ideal.comap_isMaximal_of_surjective _ φ.symm.surjective
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host P' hmax
  have hcoe : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (φ y) = s.iE (algebraMap (𝓞 X.E) X.E y) := fun _ => rfl
  have e : φ.symm t = X.conjO (φ.symm θ) := by
    apply φ.injective
    apply RingOfIntegers.ext
    rw [RingEquiv.apply_symm_apply]
    change algebraMap (𝓞 D.host.E) D.host.E t = algebraMap (𝓞 D.host.E) D.host.E (φ (X.conjO (φ.symm θ)))
    rw [hcoe, h1]
    change _ = s.iE (star (algebraMap (𝓞 X.E) X.E (φ.symm θ)))
    rw [hs.2, ← hcoe, RingEquiv.apply_symm_apply]
  apply h2
  change φ.symm (θ - t) ∈ P.asIdeal
  rw [map_sub, e, ← neg_sub]
  exact P.asIdeal.neg_mem (hall _)

theorem ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok →
    ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  intro D X s hX hs v
  have : Algebra.IsQuadraticExtension X.F X.E := ⟨hX.rankE⟩
  have : IsGalois X.F X.E := inferInstance
  have := v.isMaximal
  obtain ⟨Q, hQ, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 X.E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let P : HeightOneSpectrum (𝓞 X.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hun := hX.unram_of_inertia (conj_notMem_inertia D X s hs) P
  have hcomap : Q.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) = v.asIdeal := (Ideal.over_def Q v.asIdeal).symm
  have hun' : ¬ v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 2 := by
    rw [← hcomap]
    exact hun
  have h1 : v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 1 := by
    rw [pow_one, Ideal.map_le_iff_le_comap, hcomap]
  have he : v.asIdeal.ramificationIdx' Q = 1 := Ideal.ramificationIdx_spec h1 hun'
  have := hQ.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (X.E ≃ₐ[X.F] X.E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
  exact he

end GlobalTheory.ColumnField
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldRamificationIdxInEqOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.columnField_ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok → ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  first | exact @GlobalTheory.ColumnField.ramificationIdxIn_eq_one | exact GlobalTheory.ColumnField.ramificationIdxIn_eq_one | (intros; apply GlobalTheory.ColumnField.ramificationIdxIn_eq_one <;> assumption)
end
end
