module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.BigOm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MkTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.CharacterSubgroupOpenEvenIndexTamePower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Elts2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsDecompositionElementAtLXiPowFourNeOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsInertiaElementAtTwoXiPowFourNeOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.FixAb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.FixInf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.KxKapL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.NegVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.OddPowNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.BarFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PrimeEq
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PsiCc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.QuadEx
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Ok2B

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.ok2B :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → (∀ A : ValuationSubring Ω, Ine (F := T.F) A ≤ T.GalL) ∧ (∀ A : ValuationSubring Ω, Raw.Away {l} A → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 → D.ψ (resQ T.F g) = 1) ∧ (∃ m : ℕ, l.Coprime m ∧ ∀ g : G T.F Ω, cycZ T.F Ω l g = 1 → D.ψ (resQ T.F g) ^ m = 1) ∧ ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 := by
  intro Ω _ _ _ l hl c D hD X T hT
  obtain ⟨hpq, -, hxi, -, -⟩ := away D hD
  obtain ⟨-, -, -, -, -, hrb, -, -, -⟩ := barFacts D hD
  have hH : ∀ g : G T.F Ω, resQ T.F g ∈ X.H := fun g => hT.1 ▸ resQ_mem T.F g
  refine ⟨fun A g hg => ?_, fun A hA g hg h => ?_, ?_, fun A hA g hg => ?_⟩
  · have hg' := (resQ_Ine T.F A g).1 hg
    change resQ T.F g ∈ T.K.fixingSubgroup
    rw [hT.2]
    by_cases hp : A.valuation (X.p : Ω) < 1
    · have hp' : ¬ A.valuation (X.p' : Ω) < 1 := fun h =>
        X.hη'.nm (hpq A _ _ X.hη.prime X.hη'.prime hp h ▸ Finset.mem_insert_self _ _)
      exact (X.mem_H.1 (hH g)).2.1.trans (X.hη'.unr A hp' hg')
    · exact X.hη.unr A hp hg'
  · exact X.kap.kb A hA _ ((resQ_Ine T.F A g).1 hg) ((hrb _).1 h).2 (X.mem_H.1 (hH g)).2.2
  · obtain ⟨m, hm, h⟩ := X.kap.kc
    exact ⟨m, hm, fun g hg => h _ ((resQ_cyc T.F g).trans hg) (X.mem_H.1 (hH g)).2.2⟩
  · have hg' := (resQ_Ine T.F A g).1 hg
    have h3 : ¬ A.valuation (X.p₃ : Ω) < 1 := fun h =>
      X.hφ.nm (hpq A _ _ hl.out X.hφ.prime hA h ▸ hD.l_mem)
    have h1 : D.ξ (resQ T.F g) = 1 := hxi A hA hg'
    have h2 : X.φ (resQ T.F g) = 1 := X.hφ.unr A h3 hg'
    refine (hrb _).2 ⟨?_, ?_⟩
    · rw [Raw.bar, h1, Units.val_one, map_one]
    · rw [(X.mem_H.1 (hH g)).1, h2, Units.val_one, Int.cast_one]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Two2

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.two2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → ∀ k₀ : IntermediateField ℚ Ω, Module.finrank ℚ k₀ = 2 → IsTotallyReal k₀ → k₀.fixingSubgroup = X.φ.ker → T.Two := by
  intro Ω _ _ _ l hl c D hD X T hOn k₀ hk hr hfix
  obtain ⟨hne, -, -, -, -, -, hrb, -, -⟩ := barFacts D hD
  obtain ⟨-, -, -, -, haw⟩ := away D hD
  have hH : ∀ g : G T.F Ω, Raw.bar D.Psi (resQ T.F g) = ((X.φ (resQ T.F g) : ℤ) : ResidueField c.O) := fun g =>
    (X.mem_H.1 (hOn.1 ▸ resQ_mem T.F g)).1
  have hps : ∀ g : G T.F Ω, T.rb wPs g = ((X.φ (resQ T.F g) : ℤ) : ResidueField c.O) := fun g => by
    rw [hrb, hH]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h] <;> cases T.pr <;> simp [wPs]
  have hal : ∀ g : G T.F Ω, T.rb wAl g = Raw.bar D.ξ (resQ T.F g) := fun g => by
    rw [hrb]
    cases T.pr <;> simp [wAl]
  have hiff : ∀ g : G T.F Ω, T.rb wPs g = 1 ↔ X.φ (resQ T.F g) = 1 := fun g => by
    rw [hps]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h]
    · simp
    · constructor
      · intro h'
        exact absurd (by simpa using h') hne
      · intro h'
        exact absurd h' (by decide)
  have key : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A,
      Raw.bar D.Psi g = 1 → X.κ g = 1 → ∃ s : G T.F Ω, resQ T.F s = g := fun q hq A hA g hg h1 h2 => by
    have a : X.φ g = 1 := X.hφ.split q hq A hA hg
    have b : X.η g = 1 := X.hη.split q (Finset.mem_insert_of_mem hq) A hA hg
    have d : X.η' g = 1 := X.hη'.split q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq)) A hA hg
    refine exists_resQ ?_
    rw [hOn.1, X.mem_H]
    refine ⟨?_, b.trans d.symm, h2⟩
    rw [h1, a]
    simp
  refine ⟨fun g => ?_, fun A g hg => ?_, fun A hA g hg => ?_, ⟨k₀, hk, hr, fun p hp A hA => ?_, fun g => ?_⟩,
    X.ord, X.xi, fun A hA => ?_, fun A hA => ?_⟩
  · rw [hps]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h] <;> simp
  · have hg' := (resQ_Ine T.F A g).1 hg
    by_cases hA : A.valuation (X.p₃ : Ω) < 1
    · rw [hps, ← hH, Raw.bar, ((haw A X.p₃ X.hφ.prime X.hφ.nm hA).2 _ hg').1]
      simp
    · exact (hiff g).2 (X.hφ.unr A hA hg')
  · exact (hiff g).2 (X.hφ.split l hD.l_mem A hA ((resQ_Dec T.F A g).1 hg))
  · rw [hfix]
    refine X.hφ.split p ?_ A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hD.two_mem
    · exact hD.l_mem
  · rw [hfix, MonoidHom.mem_ker]
    exact hiff g
  · obtain ⟨g, hg, h1, h2, h3⟩ := X.bigL A hA
    obtain ⟨s, rfl⟩ := key l hD.l_mem A hA g hg h1 h2
    exact ⟨s, (resQ_Dec T.F A s).2 hg, by rw [hal]; exact h3⟩
  · obtain ⟨g, hg, h1, h2, h3⟩ := X.big2 A hA
    obtain ⟨s, rfl⟩ := key 2 hD.two_mem A (by exact_mod_cast hA) g (Ine_le_Dec A hg) h1 h2
    exact ⟨s, (resQ_Ine T.F A s).2 hg, by rw [hal]; exact h3⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ExistsTameTowerOkTwo

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.exists_tame_tower_ok_two :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ pr, LabOk D pr → ∃ T : Tower D, T.pr = pr ∧ T.Ok ∧ T.Two ∧ TameL l T.F := by
  intro Ω _ _ _ l _ c D hC pr hpr
  have hD := hC.1
  obtain ⟨κ, hκ⟩ : ∃ κ, Kap D κ := by
    obtain ⟨-, h, t, e, ψ, -, -, -, -, -, hO⟩ := hC
    exact kapEx D hD h.N ψ hO.psi
  obtain ⟨j, hj⟩ := hκ.pow
  obtain ⟨p₃, φ, hφ⟩ := quadEx Ω 1 D.S hD.S_prime
  have h1 : ∀ q ∈ insert p₃ D.S, q.Prime := Finset.forall_mem_insert _ _ _ |>.2 ⟨hφ.prime, hD.S_prime⟩
  obtain ⟨p, η, hη⟩ := quadEx Ω (-1) _ h1
  obtain ⟨p', η', hη'⟩ := quadEx Ω (-1) (insert p (insert p₃ D.S)) (Finset.forall_mem_insert _ _ _ |>.2 ⟨hη.prime, h1⟩)
  obtain ⟨x1, x2, x3⟩ := xi2 D hC
  let X : Set2 D := ⟨κ, p₃, p, p', φ, η, η', hκ, hφ, hη, hη', x3, x1, x2, ev2 D hC κ j hj, exists_decomposition_element_at_l_xi_pow_four_ne_one D hC κ j hj, exists_inertia_element_at_two_xi_pow_four_ne_one D hC κ j hj⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := characterSubgroup_open_even_index_tame_power D hD X
  obtain ⟨F, _, _, hF, dF⟩ := fixAb Ω X.H b1 b2
  obtain ⟨K, _, _, hK, dK⟩ := fixAb Ω η.ker hη.opn (Abelianization.commutator_subset_ker η)
  obtain ⟨k₀, _, _, hk, dk⟩ := fixAb Ω φ.ker hφ.opn (Abelianization.commutator_subset_ker φ)
  rw [hη.idx] at dK
  rw [hφ.idx] at dk
  haveI : IsTotallyReal F := (fixInf Ω F).1 (hF ▸ b3)
  haveI : IsCMField K := (fixInf Ω K).2 (fun σ hσ h => by
    rw [hK, MonoidHom.mem_ker, hη.cc σ hσ] at h
    exact absurd h (by decide)) dK
  have rk : IsTotallyReal k₀ := (fixInf Ω k₀).1 fun σ hσ => hk ▸ hφ.cc σ hσ
  have sp : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup :=
    fun q hq A hA => hK ▸ hη.split q (Finset.mem_insert_of_mem hq) A hA
  obtain ⟨a, u, t, hE⟩ := elts2 D hD X
  obtain ⟨g0, hg0⟩ := exists_resQ (F := F) (g := t) (hF ▸ hE.t_mem.1)
  obtain ⟨T, e1, e2, e3, e4⟩ := mkTower D hD pr K F dK (sp l hD.l_mem) g0
  have hT : X.On T := ⟨e3 ▸ hF, e2 ▸ hK⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := ok2A D hD X T hT a u t hE
  obtain ⟨c1, c2, c3, c4⟩ := ok2B D hD X T hT
  have ev : Even T.d := by
    rw [Tower.d, IntermediateField.finrank_eq_fixingSubgroup_index, hT.1]
    exact b4
  exact ⟨T, e1, ⟨e1 ▸ hpr, ev, c1, e2 ▸ sp, a1, a2, a3, a4, c2, c3, c4, a5 (e4.trans hg0), UpperTheory.V.Keep.loc2 D hC X T hT⟩,
    two2 D hD X T hT k₀ dk rk hk, fun A hA g hg => hT.1 ▸ b5 A hA g hg⟩
end
end
