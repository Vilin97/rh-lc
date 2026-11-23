module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.LemmaX
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioOneKilled
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledA
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioEqOneOfCyclic
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledB
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeDefs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersDefs
public import GroundTheory.ProfiniteCohomology.DiscreteModules
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
public import Mathlib.Topology.Basic
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalVal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SUnits
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkEndx

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_endx

open PositivityTheory.Lit1.GEN.W_killed_a

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem mem_gsOpenSubgroup_placesOver_iff {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (K' L : FiniteSubfield) [Fact (K ≤ K')] [Fact (K ≤ L)] [Fact (K' ≤ L)]
    (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hL'' : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K'.1 ℚ̄ (placesOver S))
    (τ : galUnramifiedOutside K'.1 ℚ̄ (placesOver S)) :
    τ ∈ gsOpenSubgroup (placesOver S) hL'' ↔
      ((((gsBaseChange S hK').symm τ : (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) :
        galUnramifiedOutside K.1 ℚ̄ S) ∈ gsOpenSubgroup S hL) := by
  rw [mem_gsOpenSubgroup_iff, mem_gsOpenSubgroup_iff]
  refine forall_congr' fun x => ?_
  rw [Subtype.ext_iff, Subtype.ext_iff, coe_gsBaseChange_symm_apply]
  exact Iff.rfl

theorem ending_lemmaX (hX : GlobalEulerCharCoprime) (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) (hc : ℓ ≠ 2 ∨ NumberField.IsTotallyComplex L.1) :
    ∀ (K' : FiniteSubfield) [Fact (K ≤ K')]
      (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ →
      ∀ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S)
        (resTo S K' hK' M) ιr' = 1 := by
  intro K' _ hK' hle _ hcop ιr'
  have hKL : K' ≤ L := by
    intro x hx
    refine mem_of_forall_gsOpenSubgroup_fixes S hL ⟨x, hK' ⟨x, hx⟩⟩ fun σ hσ => ?_
    have h1 := (mem_gsOpenSubgroup_iff S hK' σ).1 (hle hσ) ⟨x, hx⟩
    exact h1
  have : Fact (K' ≤ L) := ⟨hKL⟩
  have hL'' : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K'.1 ℚ̄ (placesOver S) :=
    fun x => mem_of_restrictScalars_eq' (restrictScalars_maxUnramifiedOutside_eq S hK') (hL x)
  have hcomap : (gsOpenSubgroup (placesOver S) hL'' : Subgroup (galUnramifiedOutside K'.1 ℚ̄ (placesOver S))) =
      ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf
        (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).comap
        (gsBaseChange S hK').symm.toMulEquiv.toMonoidHom := by
    ext τ
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact mem_gsOpenSubgroup_placesOver_iff S K' L hK' hL hL'' τ
  haveI hfin : Finite (resTo S K' hK' M) := (inferInstanceAs (Finite M))
  refine hX K' (placesOver S) (placesOver_finite hS) ℓ (natCast_not_mem_of_not_mem_placesOver hSℓ) L hL''
    ?_ ?_ hζ hc ιr' (resTo S K' hK' M) ?_ ?_
  · rw [hcomap]
    exact (hN.subgroupOf _).comap _
  · rw [hcomap, Subgroup.index_comap_of_surjective _ (MulEquiv.surjective _)]
    exact hcop
  · intro m
    exact hℓ m
  · intro g hg
    exact htriv _ ((mem_gsOpenSubgroup_placesOver_iff S K' L hK' hL hL'' g).1 hg)

end PositivityTheory.Lit1.GEN.W_endx
end
end

-- Source module: GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.LevelModulesDefs

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory GroundTheory.Global

attribute [local instance 2000] Rep.hV2

noncomputable section

theorem isOpen_ker_ρ {k G : Type*} [CommRing k] [Group G] [TopologicalSpace G] (A : Rep k G) [IsDiscreteRep A]
    [Finite A] : IsOpen ((A.ρ.ker : Subgroup G) : Set G) := by
  have e : ((A.ρ.ker : Subgroup G) : Set G) = ⋂ a : A, (stabilizer A.ρ a : Set G) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter]
    constructor
    · intro h a
      change A.ρ g a = a
      rw [h, one_apply_eq_self]
    · intro h
      exact LinearMap.ext fun a => h a
  rw [e]
  exact isOpen_iInter_of_finite fun a => isOpen_stabilizer A a

end

end GroundTheory.ProfCoh
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkSplit

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_split

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem isTotallyComplex_of_sq_eq_neg_one {E : Type*} [Field E] (x : E) (hx : x ^ 2 = -1) :
    NumberField.IsTotallyComplex E := by
  refine ⟨fun w => ?_⟩
  by_contra hw
  have hr := InfinitePlace.not_isComplex_iff_isReal.1 hw
  have h := congrArg (InfinitePlace.embedding_of_isReal hr) hx
  rw [map_pow, map_neg, map_one] at h
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hr x)]

set_option maxHeartbeats 800000 in
theorem exists_split (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M] :
    ∃ (L : FiniteSubfield) (hKL : Fact (K ≤ L)),
      haveI := hKL
      ∃ hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S,
        (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal ∧ (∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) ∧
        (ℓ ≠ 2 ∨ NumberField.IsTotallyComplex L.1) ∧ ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1 := by
  classical
  have hℓ := (Fact.out : ℓ.Prime)

  let W : Set (galUnramifiedOutside K.1 ℚ̄ S) := (M.ρ.ker : Set (galUnramifiedOutside K.1 ℚ̄ S))
  have hWo : IsOpen W := isOpen_ker_ρ M
  have hW1 : (1 : galUnramifiedOutside K.1 ℚ̄ S) ∈ W := M.ρ.ker.one_mem
  obtain ⟨E, hEf, hEU⟩ := (krullTopology_mem_nhds_one_iff K.1 (maxUnramifiedOutside K.1 ℚ̄ S) W).1
    (hWo.mem_nhds hW1)
  set_option synthInstance.maxHeartbeats 100000 in
    let bE := Module.finBasis K.1 E

  let n : ℕ := if ℓ = 2 then 4 else ℓ
  have hn0 : n ≠ 0 := by
    by_cases h2 : ℓ = 2
    · simp [n, h2]
    · simp only [n, h2, ite_false]; exact hℓ.ne_zero
  have hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := by
    intro v hv hmem
    apply hv
    apply hSℓ v
    by_cases h2 : ℓ = 2
    · subst h2
      have h4 : ((4 : ℕ) : 𝓞 K.1) = ((2 : ℕ) : 𝓞 K.1) * ((2 : ℕ) : 𝓞 K.1) := by push_cast; ring
      simp only [n, ite_true] at hmem
      rw [h4] at hmem
      rcases v.isPrime.mem_or_mem hmem with h | h <;> exact h
    · simpa [n, h2] using hmem
  have : NeZero n := ⟨hn0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℚ̄ n
  have hξS : ξ ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    mem_maxUnramifiedOutside_of_pow_eq_one S hn0 hnS hξ.pow_eq_one
  let T : Finset ℚ̄ := insert ξ (Finset.univ.image fun i => ((bE i : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄))
  have hT : ∀ y ∈ T, y ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · exact h ▸ hξS
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (bE i : maxUnramifiedOutside K.1 ℚ̄ S).2
  obtain ⟨N, hKN, hNn, hN, hTN⟩ := exists_galois_level_finset S T hT
  have hL : ∀ x : N.1, algebraMap N.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S := fun x => hN x x.2
  have hξN : ξ ∈ N.1 := hTN ξ (Finset.mem_insert_self _ _)
  refine ⟨N, hKN, hL, gsOpenSubgroup_normal hL, ?_, ?_, ?_⟩
  ·
    by_cases h2 : ℓ = 2
    · subst h2
      refine ⟨-1, ?_⟩
      exact IsPrimitiveRoot.neg_one 0 (by norm_num)
    · have hξℓ : IsPrimitiveRoot ξ ℓ := by simpa [n, h2] using hξ
      refine ⟨⟨ξ, hξN⟩, IsPrimitiveRoot.of_map_of_injective (f := algebraMap N.1 ℚ̄) ?_
        (algebraMap N.1 ℚ̄).injective⟩
      exact hξℓ
  · by_cases h2 : ℓ = 2
    · right
      have hξ4 : IsPrimitiveRoot ξ 4 := by simpa [n, h2] using hξ
      refine isTotallyComplex_of_sq_eq_neg_one (⟨ξ, hξN⟩ : N.1) ?_
      apply (algebraMap N.1 ℚ̄).injective
      rw [map_pow, map_neg, map_one]
      change ξ ^ 2 = -1
      have h1 : (ξ ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hξ4.pow_eq_one
      have h2' : ξ ^ 2 ≠ 1 := hξ4.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
      have h3 : (ξ ^ 2 - 1) * (ξ ^ 2 + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd (sub_eq_zero.1 h) h2'
      · exact eq_neg_of_add_eq_zero_left h
    · exact Or.inl h2
  ·
    intro g hg
    have hgE : g ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hb : ∀ i, g (bE i : maxUnramifiedOutside K.1 ℚ̄ S) = (bE i : maxUnramifiedOutside K.1 ℚ̄ S) := by
        intro i
        have hmem : ((bE i : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1 :=
          hTN _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
        have key := (mem_gsOpenSubgroup_iff S hL g).1 hg (⟨_, hmem⟩ : N.1)
        have he : gsEmbedding (S := S) hL (⟨_, hmem⟩ : N.1) = (bE i : maxUnramifiedOutside K.1 ℚ̄ S) :=
          Subtype.ext (coe_embeddingOfRestrictScalarsEq _ _)
        rw [he] at key
        exact key
      have hsum : x = ∑ i, (bE.repr ⟨x, hx⟩ i) • (bE i : maxUnramifiedOutside K.1 ℚ̄ S) := by
        have := congrArg (fun e : E => (e : maxUnramifiedOutside K.1 ℚ̄ S)) (bE.sum_repr ⟨x, hx⟩)
        simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
        exact this.symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show ∀ (r : K.1) (y : maxUnramifiedOutside K.1 ℚ̄ S), g (r • y) = r • g y from
        fun r y => g.toLinearEquiv.map_smul r y, hb i]
    have hgW := hEU hgE
    exact MonoidHom.mem_ker.1 hgW

end PositivityTheory.Lit1.GEN.W_split
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkAssemble

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_assemble

open PositivityTheory.Lit1.GEN.W_killed_a

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem ratio_eq_one_of_coprime_cyclic' (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hK : ∀ (K' : FiniteSubfield) [Fact (K ≤ K')]
      (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ →
      ∀ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S)
        (resTo S K' hK' M) ιr' = 1) :
    gsEulerRatio S M ιr = 1 :=
  W_killed_c.ratio_eq_one_of_cyclic ℓ K S hS hSℓ ιr L hL hN M hℓ htriv
    (fun L' _ hL' hle hcyc => W_killed_b.ratio_coind_cyclic ℓ K S hS hSℓ ιr L hL hN M hℓ htriv hK L' hL' hle hcyc)

theorem ratioOneKilled_of_lemmaX (ℓ : ℕ) [Fact ℓ.Prime] (hX : GlobalEulerCharCoprime) :
    RatioOneKilled ℓ (fun _ => True) := by
  intro K S hS hSℓ _ ιr M _ _ hℓ
  obtain ⟨L, hKL, hsplit⟩ := W_split.exists_split ℓ K S hS hSℓ M
  letI := hKL
  obtain ⟨hL, hN, hζ, hc, htriv⟩ := hsplit
  exact ratio_eq_one_of_coprime_cyclic' ℓ K S hS hSℓ ιr L hL hN M hℓ htriv
    (W_endx.ending_lemmaX hX ℓ K S hS hSℓ ιr L hL hN M hℓ htriv hζ hc)

end PositivityTheory.Lit1.GEN.W_assemble
end
end
