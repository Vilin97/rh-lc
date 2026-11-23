module

public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertiaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.ExistsDen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemIntegralClosureIffMemBall
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.DenseSurj
import Mathlib.Tactic.Linter.Style
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.NormLeOneOfInteger
public import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.GaloisValuations.GlobalB
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionGroupEquivPadicGalois

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DecGalois

theorem exists_continuousMulEquiv : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∃ i : ↥(A.decompositionSubgroup F) ≃ₜ*
      (PadicAlgCl p ≃ₐ[↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)))] PadicAlgCl p),
      ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x) := by
  intro p _ F Ω _ _ _ _ _ A j hj
  let K : Formalism.BasicNotions.Loc.FinExt p :=
    ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[p] (PadicAlgCl p) K.1
  let e2 : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K.1] PadicAlgCl p) :=
    e.trans (IntermediateField.fixingSubgroupEquiv K.1)
  refine ⟨{ e2 with continuous_toFun := hf.comp he, continuous_invFun := he'.comp hf' }, fun g x => ?_⟩
  exact hec g x

end GlobalTheory.DecGalois
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionGroupEquivPadicGaloisStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.exists_decompositionGroup_equiv_padicGalois : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∃ i : ↥(A.decompositionSubgroup F) ≃ₜ*
      (PadicAlgCl p ≃ₐ[↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)))] PadicAlgCl p),
      ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x) := by
  first | exact @GlobalTheory.DecGalois.exists_continuousMulEquiv | exact GlobalTheory.DecGalois.exists_continuousMulEquiv | (intros; apply GlobalTheory.DecGalois.exists_continuousMulEquiv <;> assumption)
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemSpanLIff

section

@[expose] public section

namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem mem_span_l_iff {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) (y : ↥(ball K)) :
    y ∈ Ideal.span {((l : ℕ) : ↥(ball K))} ↔
      ‖((y : ↥K.1) : Om l)‖ ≤ ‖((l : ℕ) : Om l)‖ := by
  have hl0' : ((l : ℕ) : Om l) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l))]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)
  have hl0 : ((l : ℕ) : ↥K.1) ≠ 0 := by
    intro h
    apply hl0'
    have h' : (((l : ℕ) : ↥K.1) : Om l) = 0 := by rw [h]; rfl
    simpa using h'
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : ‖((z : ↥K.1) : Om l)‖ ≤ 1 := z.2
    have hc : (((z * ((l : ℕ) : ↥(ball K)) : ↥(ball K)) : ↥K.1) : Om l) =
        ((z : ↥K.1) : Om l) * ((l : ℕ) : Om l) := by simp
    rw [hc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hz
  · intro h
    have hmem : ‖(((y : ↥K.1) / ((l : ℕ) : ↥K.1) : ↥K.1) : Om l)‖ ≤ 1 := by
      have hc : (((y : ↥K.1) / ((l : ℕ) : ↥K.1) : ↥K.1) : Om l) =
          ((y : ↥K.1) : Om l) / ((l : ℕ) : Om l) := by simp
      rw [hc, norm_div, div_le_one (norm_pos_iff.mpr hl0')]
      exact h
    refine ⟨⟨(y : ↥K.1) / ((l : ℕ) : ↥K.1), hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    push_cast
    exact div_mul_cancel₀ _ hl0

theorem locDegOf_of (hB : BallCard) (hD : DenseSurj) (hK : KerProp) (hN : NormCard) :
    LocDegOf := by
  intro l hl E _ _ φ K hφK hdense v hv hφv
  let ψ : 𝓞 E →+* ↥(ball K) :=
    { toFun := fun x => ⟨⟨φ (x : E), hφK _⟩, (hφv x).1⟩
      map_one' := Subtype.ext <| Subtype.ext <| by simp
      map_mul' := fun a b => Subtype.ext <| Subtype.ext <| by simp
      map_zero' := Subtype.ext <| Subtype.ext <| by simp
      map_add' := fun a b => Subtype.ext <| Subtype.ext <| by simp }
  let q := (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ↥(ball K))})).comp ψ
  have hsurj : Function.Surjective q := by
    intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨x, hx⟩ := hD l E φ K hφK hdense ((y : ↥K.1) : Om l) (y : ↥K.1).2 y.2
    refine ⟨x, ?_⟩
    show Ideal.Quotient.mk _ (ψ x) = Ideal.Quotient.mk _ y
    rw [Ideal.Quotient.eq, mem_span_l_iff]
    have hc : (((ψ x - y : ↥(ball K)) : ↥K.1) : Om l) = φ (x : E) - ((y : ↥K.1) : Om l) := rfl
    rw [hc, norm_sub_rev]
    exact hx
  have hker : RingHom.ker q = v.asIdeal ^ v.asIdeal.ramificationIdx ℤ := by
    ext x
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk _ (ψ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_span_l_iff K (ψ x)).trans (hK l E φ v hv hφv x)
  have hcard : Nat.card (𝓞 E ⧸ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) =
      Nat.card (↥(ball K) ⧸ Ideal.span {((l : ℕ) : ↥(ball K))}) := by
    rw [← hker]
    exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv
  rw [hN l E v hv, hB l K] at hcard
  exact (Nat.pow_right_injective hl.out.two_le hcard).symm

end PI.CompDegEF
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.SpanLIsMaximal

section

@[expose] public section

namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem span_l_isMaximal (l : ℕ) [hl : Fact l.Prime] : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal := by
  refine Ideal.IsPrime.isMaximal ?_ ?_
  · exact (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hl.out)
  · simp [hl.out.ne_zero]

theorem liesOver_of_mem {l : ℕ} [hl : Fact l.Prime] {E : Type} [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E l) :
    v.asIdeal.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := by
  constructor
  refine (span_l_isMaximal l).eq_of_le ?_ ?_
  · intro h
    rw [Ideal.comap_eq_top_iff] at h
    exact v.isPrime.ne_top h
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change algebraMap ℤ (𝓞 E) ((l : ℕ) : ℤ) ∈ v.asIdeal
    simpa using (show ((l : ℕ) : 𝓞 E) ∈ v.asIdeal from hv)

theorem normCard : NormCard := by
  intro l _ E _ _ v hv
  have := liesOver_of_mem hv
  have hmax := span_l_isMaximal l
  have hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have h1 : Nat.card (𝓞 E ⧸ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) =
      Ideal.absNorm (v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h1, map_pow, Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver v.asIdeal
    (Ideal.span {((l : ℕ) : ℤ)}) hmax.isPrime (by simp [(Fact.out : l.Prime).ne_zero]),
    Ideal.absNorm_span_natCast, Module.finrank_self, pow_one,
    Ideal.inertiaDeg'_eq_inertiaDeg, Formalism.MainNotions.N.locDeg, ← pow_mul, mul_comm]

end PI.CompDegEF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup

section

@[expose] public section

noncomputable section

namespace GlobalTheory.DecLocal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem exists_place_below : ∀ {p : ℕ} [Fact p.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
    ∃ w : HeightOneSpectrum (𝓞 F), w ∈ Formalism.BasicNotions.placesOver F p ∧ IsPlaceOver A w := by
  intro p _ F Ω _ _ _ _ A hp
  have hint : ∀ x : 𝓞 F, algebraMap F Ω (x : F) ∈ A := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)
  let f : 𝓞 F →+* A := RingHom.codRestrict ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)) A hint
  let I : Ideal (𝓞 F) := Ideal.comap f (IsLocalRing.maximalIdeal A)
  have hI : ∀ x : 𝓞 F, x ∈ I ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := fun x => by
    change f x ∈ IsLocalRing.maximalIdeal A ↔ _
    exact ValuationSubring.valuation_lt_one_iff A (f x)
  have hpI : ((p : 𝓞 F)) ∈ I := by
    rw [hI]; simpa using hp
  have hp0 : ((p : 𝓞 F)) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  let w : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := I, isPrime := Ideal.comap_isPrime f _,
      ne_bot := fun h => hp0 (by rw [← Ideal.mem_bot, ← h]; exact hpI) }
  exact ⟨w, hpI, fun x => (hI x).symm⟩

theorem exists_root_of_unity : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl p)
    (n : ℕ) (z : PadicAlgCl p), z ^ (p ^ n) = 1 → ∃ y : Ω, y ^ (p ^ n) = 1 ∧ j y = z := by
  intro p _ Ω _ _ j n z hz
  have hf : ((X ^ (p ^ n) - 1 : Polynomial Ω).map j) = X ^ (p ^ n) - 1 := by simp
  have hne : (X ^ (p ^ n) - 1 : Polynomial (PadicAlgCl p)) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) (1 : PadicAlgCl p)
  have hz' : z ∈ ((X ^ (p ^ n) - 1 : Polynomial Ω).map j).roots := by
    rw [hf, mem_roots hne]; simp [hz]
  rw [Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hz'
  obtain ⟨y, hy, rfl⟩ := hz'
  refine ⟨y, ?_, rfl⟩
  have := isRoot_of_mem_roots hy
  simpa [sub_eq_zero] using this

theorem norm_lt_one_iff {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p)
    (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (y : Ω) : ‖j y‖ < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', hA, hA]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h0 : 0 < ‖j y‖ := norm_pos_iff.2 ((map_ne_zero j).2 hy)
    rw [map_inv₀, norm_inv]
    simp only [hy, false_or]
    constructor
    · intro h
      exact ⟨h.le, not_le.2 ((one_lt_inv₀ h0).2 h)⟩
    · rintro ⟨h1, h2⟩
      refine lt_of_le_of_ne h1 fun h => h2 ?_
      rw [h, inv_one]

theorem finrank_closure_eq_locDeg : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v →
      Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x))) =
        locDeg v := by
  intro p _ F Ω _ _ _ _ A j hA v hv
  let φ : F →+* PadicAlgCl p := j.comp (algebraMap F Ω)
  obtain ⟨v', -, hφ⟩ := PI.CompDegEF.placeProp p F φ
  have hvp : v ∈ Formalism.BasicNotions.placesOver F p := by
    show ((p : 𝓞 F)) ∈ v.asIdeal
    rw [← hv, ← norm_lt_one_iff A j hA]
    simpa using GlobalTheory.PlaceBridge.norm_l_lt_one (l := p)
  exact PI.CompDegEF.locDegOf_of PI.CompDegEF.ballCard PI.CompDegEF.denseSurj PI.CompDegEF.kerProp
    PI.CompDegEF.normCard p F φ ⟨_, GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range φ⟩
    (fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
    (GlobalTheory.PlaceBridge.adjoin_range_subset_closure φ) v hvp
    (fun x => ⟨(hφ x).1, (norm_lt_one_iff A j hA _).trans (hv x)⟩)

theorem decEquiv : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  intro p _ F Ω _ _ _ _ _ A hp
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  obtain ⟨w, hw, hAw⟩ := exists_place_below (F := F) A hp
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding F Ω w A hw hAw
  obtain ⟨i, hi⟩ := GlobalTheory.T.exists_decompositionGroup_equiv_padicGalois p F Ω A j hj
  refine ⟨_, GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω)), i, ?_,
    fun g => GlobalTheory.T.localInertia_iff_mem_placeInertia p F Ω A j hj _ i.toMulEquiv hi g,
    fun v hv => finrank_closure_eq_locDeg p F Ω A j hj v hv⟩
  intro O _ ε hε g n ζ hζ
  obtain ⟨y, hy, rfl⟩ := exists_root_of_unity p Ω j n ζ hζ
  obtain ⟨a, ha, ha'⟩ := hε (i.symm g) n y hy
  refine ⟨a, ?_, ha'⟩
  have e := hi (i.symm g) y
  rw [ContinuousMulEquiv.apply_symm_apply] at e
  rw [e, ha, map_pow]

end GlobalTheory.DecLocal
end
end
end
