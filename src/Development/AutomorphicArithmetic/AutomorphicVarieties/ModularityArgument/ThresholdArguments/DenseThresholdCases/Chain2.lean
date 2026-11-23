module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ChainSeedRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AffSmulOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.DiesEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FlagFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GlobalTheory
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GysinAl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.OverFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RestrT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.FlagMove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.FlagNew
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PlaceMove
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.LvSmulOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.MovePs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.RtFacts
import Mathlib.FieldTheory.Galois.Profinite

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.EntIff

section

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Chain.entIff :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k)
      (c : PD Φ.ι Γ k), Φ.IsRes a c →
      (Supp nP c.r → (Ent c.r (-wPs) ↔ ∃ g, c.r g 2 0 ≠ 0)) ∧ (Supp nM c.r → (Ent c.r (-wAl) ↔ ∃ g, c.r g 1 0 ≠ 0)) := by
  intro O Γ _ _ _ Φ k _ a c hc
  have hadj : ∀ g, adj (c.r g⁻¹) = a ↑(Φ.ν g⁻¹) • c.r g := by
    intro g
    have hm : adj (c.r g⁻¹) * c.r g⁻¹ = a ↑(Φ.ν g⁻¹) • 1 := hc.pair.mult g⁻¹
    calc adj (c.r g⁻¹) = adj (c.r g⁻¹) * (c.r g⁻¹ * c.r g) := by
          rw [← map_mul, inv_mul_cancel, map_one, mul_one]
      _ = a ↑(Φ.ν g⁻¹) • c.r g := by rw [← mul_assoc, hm, smul_mul_assoc, one_mul]
  have hν : ∀ g, a ↑(Φ.ν g) ≠ 0 := fun g => ((Φ.ν g).isUnit.map a).ne_zero
  have ent : ∀ {R : Type} [CommRing R] (X : M4 R), adj X 3 1 = - X 2 0 ∧ adj X 3 2 = X 1 0 := by
    intro R _ X
    simp [adj_apply, sgn]
  have e31 : ∀ g, c.r g 3 1 ≠ 0 → c.r g⁻¹ 2 0 ≠ 0 := by
    intro g hg h0
    have := (ent (c.r g⁻¹)).1
    rw [hadj, h0, neg_zero, Matrix.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero (hν _) hg this
  have e32 : ∀ g, c.r g 3 2 ≠ 0 → c.r g⁻¹ 1 0 ≠ 0 := by
    intro g hg h0
    have := (ent (c.r g⁻¹)).2
    rw [hadj, h0, Matrix.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero (hν _) hg this
  have wP : ∀ i j : Fin 4, wt i j = -wPs → (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [wt, lamW, muW, wPs, Prod.ext_iff]
  have wA : ∀ i j : Fin 4, wt i j = -wAl → (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [wt, lamW, muW, wAl, Prod.ext_iff]
  have w20 : wt 2 0 = -wPs := by simp [wt, lamW, muW, wPs]
  have w10 : wt 1 0 = -wAl := by simp [wt, lamW, muW, wAl]
  refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ⟨?_, ?_⟩⟩
  · rintro ⟨g, i, j, hw, hne⟩
    rcases wP i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨g, hne⟩
    · exact ⟨g⁻¹, e31 g hne⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, 2, 0, w20, hg⟩
  · rintro ⟨g, i, j, hw, hne⟩
    rcases wA i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨g, hne⟩
    · exact ⟨g⁻¹, e32 g hne⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, 1, 0, w10, hg⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.ExistsResidualDatumOverRestrictionToRationals

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Chain.exists_residual_datum_over_restriction_to_rationals :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) →
      ∀ c₀ : PD Unit (G ℚ Ω) k, (frQ D T.pr (resQ T.F T.g0)).IsRes a c₀ → c₀.In nP →
      ∃ s : PD T.ι (G T.F Ω) k, (T.fr ∅).IsRes a s ∧ T.OverQ c₀ s := by
  intro _ Ω _ _ _ l _ c D T hT k _ a ha c₀ hc₀ hin
  have hG : D.Good := by
    rcases hT.2 with h | h
    · exact h.1.1
    · exact h.1.1
  haveI : NumberField T.F := T.nF
  have hl : l.Prime := Fact.out
  have hpl : ∀ v, ∃ g : G ℚ Ω, (∀ x : Ω, g x ∈ T.pl v ↔ x ∈ D.pl l) ∧
      (∀ s ∈ Dec (T.pl v), g⁻¹ * resQ T.F s * g ∈ Dec (D.pl l)) ∧
      (∀ s ∈ Ine (T.pl v), g⁻¹ * resQ T.F s * g ∈ Ine (D.pl l)) := fun v =>
    Rq.placeMove T.F l hl (T.pl v) (D.pl l) (T.ovl v) (hG.pl_over l hl)
  choose g hg using hpl
  have hne : ∀ h : G ℚ Ω, a ((frQ D T.pr (resQ T.F T.g0)).ν h : c.O) ≠ 0 := by
    intro h
    exact ((Units.map a.toMonoidHom) ((frQ D T.pr (resQ T.F T.g0)).ν h)).ne_zero
  have hn : ∀ v, ∃ n' : UpperTheory.V.GradeZeroInterpolatingElement.M4 k, IsLow n' ∧ IsUp (adj n' * c₀.r (g v) * c₀.n ()) ∧
      (SuppM nP (c₀.r (g v)) ∧ SuppM qQ (c₀.n ()) → SuppM qQ n') := fun v =>
    Rt.flagNew k _ (c₀.r (g v)) (c₀.n ()) (hne (g v)) (hc₀.pair.mult (g v)) (hc₀.pair.low ())
      (Or.inl ⟨hin.1 (g v), hin.2 ()⟩)
  choose n' hn' using hn
  have key : ∀ v, ∀ s ∈ Dec (T.pl v), IsUp (adj (n' v) * c₀.r (resQ T.F s) * n' v) ∧
      ∀ i, (adj (n' v) * c₀.r (resQ T.F s) * n' v) i i = a ((frQ D T.pr (resQ T.F T.g0)).χ i (resQ T.F s) : c.O) := by
    intro v s hs
    have hconj := (hg v).2.1 s hs
    have hX : c₀.r (g v) * c₀.r (g v)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    obtain ⟨h1, h2⟩ := Rt.flagMove k (c₀.r (g v)) (c₀.r (g v)⁻¹)
      (c₀.r ((g v)⁻¹ * resQ T.F s * g v)) (c₀.n ()) (n' v) hX (hc₀.pair.low ()) (hn' v).1
      (hn' v).2.1 (hc₀.pair.flag () _ hconj)
    have he : c₀.r (g v) * c₀.r ((g v)⁻¹ * resQ T.F s * g v) * c₀.r (g v)⁻¹ =
        c₀.r (resQ T.F s) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [he] at h1 h2
    refine ⟨h1, fun i => ?_⟩
    rw [h2 i]
    refine (hc₀.res.char () _ hconj i).trans ?_
    rw [map_mul, map_mul, map_inv, mul_comm _ ((frQ D T.pr (resQ T.F T.g0)).χ i (resQ T.F s)), inv_mul_cancel_right]
  refine ⟨⟨c₀.r.comp (resQ T.F), n'⟩, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩,
    ⟨rfl, fun v => ⟨(), g v, (hg v).1, (hn' v).2.1⟩⟩⟩
  · intro h
    exact hc₀.pair.mult (resQ T.F h)
  · rintro h ⟨A, hA, hI, hb⟩
    show c₀.r (resQ T.F h) = 1
    have hAl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
    by_cases hS : ∃ p ∈ D.Sb, A.valuation (p : Ω) < 1
    · obtain ⟨p, hp, hpA⟩ := hS
      have hpS : p ∈ D.S := (Finset.mem_filter.1 hp).1
      have hpp : p.Prime := hG.S_prime p hpS
      obtain ⟨γ, -, -, hγ⟩ := Rq.placeMove T.F p hpp A (D.pl p) hpA (hG.pl_over p hpp)
      have hmem := hγ h hI
      have hψ : D.ψ (resQ T.F h) = 1 := by
        refine hT.1.kb A ?_ h hI hb
        intro q hq
        rw [Finset.mem_singleton] at hq
        subst hq
        exact hAl
      have hk := hc₀.pair.kill (γ⁻¹ * resQ T.F h * γ) (Or.inr ⟨p, hp, Subgroup.mem_inf.2 ⟨hmem, by
        rw [MonoidHom.mem_ker, map_mul, map_mul, hψ, mul_one, map_inv, inv_mul_cancel]⟩⟩)
      have hx : resQ T.F h = γ * (γ⁻¹ * resQ T.F h * γ) * γ⁻¹ := by group
      rw [hx, map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one]
    · push_neg at hS
      refine hc₀.pair.kill _ (Or.inl ⟨A, ?_, hI, hb⟩)
      intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact hAl
      · exact not_lt.2 (hS q hq)
  · exact hc₀.pair.nrm
  · intro v
    exact (hn' v).1
  · intro v s hs
    exact (key v s hs).1
  · intro v s hs i
    obtain ⟨hsD, m, hm⟩ := hs
    refine ((key v s hsD).2 i).trans ?_
    have hchar : CharP k l := by
      haveI := c.dvr
      haveI := c.fin
      have hmax : ((l : ℕ) : c.O) ∈ IsLocalRing.maximalIdeal c.O := by
        obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (R := ℤ_[l]) (S := c.O)
          (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _))
        change Q.comap (algebraMap ℤ_[l] c.O) = _ at hQc
        have hlQ : ((l : ℕ) : c.O) ∈ Q := by
          have h0 : ((l : ℕ) : ℤ_[l]) ∈ Q.comap (algebraMap ℤ_[l] c.O) := by
            rw [hQc, PadicInt.maximalIdeal_eq_span_p]
            exact Ideal.subset_span (Set.mem_singleton _)
          simpa using h0
        exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
          hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hlQ hu)
      rw [CharP.charP_iff_prime_eq_zero hl]
      have h0 := ha _ hmax
      simpa using h0
    let φ : G T.F Ω →* kˣ := (Units.map a.toMonoidHom).comp
      (((frQ D T.pr (resQ T.F T.g0)).χ i).comp (resQ T.F))
    have hφv : ∀ x, (φ x : k) = c₀.r (resQ T.F x) i i := fun x =>
      (hc₀.res.diag (resQ T.F x) i).symm
    have hlc : IsLocallyConstant (fun x : G T.F Ω => c₀.r (resQ T.F x) i i) := by
      have h1 := (hc₀.cont i i 1).comp_continuous (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω)
      refine IsLocallyConstant.desc _ (Ideal.Quotient.mk ((⊥ : Ideal k) ^ 1)) h1 ?_
      intro x y hxy
      rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot, sub_eq_zero] at hxy
      exact hxy
    have hcl : IsClosed ((φ.ker : Subgroup (G T.F Ω)) : Set (G T.F Ω)) := by
      have he : ((φ.ker : Subgroup (G T.F Ω)) : Set (G T.F Ω)) =
          (fun x : G T.F Ω => c₀.r (resQ T.F x) i i) ⁻¹' {1} := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff,
          ← hφv, Units.val_eq_one]
      rw [he]
      exact (hlc.isClopen_fiber 1).isClosed
    have hcomm : ⁅Dec (T.pl v), Dec (T.pl v)⁆ ≤ φ.ker :=
      le_trans (Subgroup.commutator_mono le_top le_top) (Abelianization.commutator_subset_ker φ)
    have hker := Subgroup.topologicalClosure_minimal _ hcomm hcl hm
    rw [MonoidHom.mem_ker, map_pow] at hker
    have hx : (φ s : k) ^ (l ^ m) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hker, Units.val_one]
    have hz : ((φ s : k) - 1) ^ (l ^ m) = 0 := by
      rw [sub_pow_char_pow, one_pow, hx, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero) |>.1 hz)
  · intro h i
    exact hc₀.res.diag (resQ T.F h) i
  · intro v s hs i
    exact (key v s hs).2 i
  · exact Or.inl ⟨fun h => hin.1 (resQ T.F h), fun v => (hn' v).2.2 ⟨hin.1 _, hin.2 ()⟩⟩
  · intro i j N
    exact (hc₀.cont i j N).comp_continuous
      (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Chain2

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
private theorem supp_mono {R : Type} [CommRing R] {S S' : Finset (ℤ × ℤ)} (h : S ⊆ S') {X : M4 R} (hX : SuppM S X) :
    SuppM S' X := fun i j hij hw => hX i j hij fun hs => hw (h hs)
theorem UpperTheory.V.Ws.deep_tower_residue_chain_exists :
    CohomologyHyp → _root_.UpperTheory.V.Ws.SeedIIAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx2 D → T₀.Ok → T₀.Two → TameL l T₀.F → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' → (T.fr ∅).Chain (𝔞.red c) c₀' (Q.map (𝔞.red c₁)) := by
  intro hP hS Ω _ _ _ l _ c D T₀ hC hO hT hL ι 𝔞 c₀ hc₀
  have hG : D.Good := hC.1
  have hF : T₀.Fit := ⟨hO, Or.inl ⟨hC, hT⟩⟩
  have ha : ∀ x ∈ maximalIdeal c.O, 𝔞.red c x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c) x hx)
  have hrt := (Chain.rtFacts D hG T₀ hO _ _ ha).1
  obtain ⟨s₀, hs₀, ho₀⟩ := Chain.exists_residual_datum_over_restriction_to_rationals hP D T₀ hF _ _ ha c₀ hc₀.res ⟨hc₀.supp, fun _ => hc₀.flag⟩
  have hq₀ := goodQ D hG T₀ hF _ _ ha _ c₀ s₀ hc₀ hrt ho₀ hs₀
  obtain ⟨W, s, -, -, hW, hs, -, hsQ, -, hsP, -, -, hsA⟩ :=
    gysinAl hP D T₀ hF _ _ ha ∅ (by simp) s₀ s₀ hs₀ hs₀ (hq₀ ∅).2.1 (hq₀ ∅).2.1
  obtain ⟨T₁, h01, hL1, hD⟩ := diesEx D hG T₀ hL hO W hW
  refine ⟨T₁, h01, hL1, fun T h1 hdeep => ?_⟩
  have h0 : T₀.Le T := (leFit D hG T₀ T₁ h01).2.2.2.2.2.2 T h1
  obtain ⟨lO, lT, -, -, lF, -⟩ := leFit D hG T₀ T h0
  have tO := lO hO
  have tT := lT hT
  have tF := lF hF
  have hDT : ∀ w ∈ W, Dies l w T.F := fun w hw θ h1' h2 =>
    (IntermediateField.fixingSubgroup_antitone h1.le).trans (hD w hw θ h1' h2)
  obtain ⟨c₁, h, Q, hQ, hQV, hQE⟩ := hS Ω l c D T hC tO tT hdeep ι
  refine ⟨c₁, h, Q, hQ, fun c₀' ho hr => ?_⟩
  obtain ⟨sR, sV, sE⟩ := _root_.UpperTheory.V.Ws.Chain.isRes_map_red_and_inV_ent_map_red_of_map_residue D T ι 𝔞 h Q hQ
  have sV := sV hQV
  obtain ⟨c₃, r₃, o₃⟩ := restrT D hG T₀ T h0 hF _ _ ha W hW hDT s hs (Or.inr (Or.inl hsQ.1))
  obtain ⟨t, rt, ot⟩ := restrT D hG T₀ T h0 hF _ _ ha W hW hDT s₀ (hq₀ W).1 (Or.inr (Or.inr hs₀))
  have hsP' : s.In nP := ⟨fun g => supp_mono (by decide) (hsQ.1 g), hsQ.2⟩
  have hsM : Supp nM s.r := fun g => supp_mono (by decide) (hsQ.1 g)
  obtain ⟨-, f2, f3, f4, -, -, f7, -⟩ := overFacts D hG T₀ T h0 hF _ _ ha W ∅ s s₀ c₃ t hs (hq₀ W).1 r₃ rt o₃ ot
  obtain ⟨-, -, -, -, -, -, -, g8⟩ := overFacts D hG T₀ T h0 hF _ _ ha W ∅ s₀ s t c₃ (hq₀ W).1 hs rt r₃ ot o₃
  obtain rfl : c₀' = t := g8 c₀ _ hc₀.res.pair ho₀ c₀' hr ho
  have q₃ : Supp qQ c₃.r := f2 _ hsQ.1
  have i₃ : c₃.In nP := f3 hsP'
  have m₃ : Supp nM c₃.r := f2 _ hsM
  have p₃ : c₃.SamePs c₀' := f4 hsP' (hq₀ W).2.1 hsP
  have a₃ : Ent c₃.r (-wAl) := (f7 hsM).1 hsA
  obtain ⟨-, i₀, g₀⟩ := goodQ D hG T tF _ _ ha (resQ T₀.F T₀.g0) c₀ c₀' (h0.pr ▸ hc₀) (h0.pr ▸ hrt) ho hr ∅
  have ok : (T.fr ∅).Ok (𝔞.red c) := (std hP D T tF ∅ c le_rfl).2 _ _ ha
  have hmu : ∀ v, ∀ s ∈ (T.fr ∅).Mu v, s ∈ (T.fr ∅).Gv v := fun v s hs => hs.1
  have hrb := (Chain.rtFacts D hG T tO _ _ ha).2
  obtain ⟨c₄', r₄', u₄', n₄', e₄'⟩ := Chain.levi (T.fr ∅) _ hmu c₃ r₃ m₃
  obtain ⟨c₄, r₄, e₄, n₄⟩ := Chain.movePs (T.fr ∅) _ ok.mul hmu
    (fun v s hs => (hrb _ _).2 (tT.atL _ (T.ovl v) s hs)) c₄' r₄' u₄' n₄' fun v => (Q.map (𝔞.red c₁)).n v 2 0
  have u₄ : Supp {-wAl} c₄.r := e₄ ▸ u₄'
  have m₄ : Supp nM c₄.r := fun g => supp_mono (by decide) (u₄ g)
  have v₄ : Supp vV c₄.r := fun g => supp_mono (by decide) (u₄ g)
  have al : c₃.SameAl c₄ := ⟨fun g => by rw [e₄, e₄'.1], fun v => ((n₄ v).2.1.trans (e₄'.2 v)).symm⟩
  have a₄ : Ent c₄.r (-wAl) := by
    obtain ⟨g, hg⟩ := ((Chain.entIff (T.fr ∅) (𝔞.red c) c₃ r₃).2 m₃).1 a₃
    exact ((Chain.entIff (T.fr ∅) (𝔞.red c) c₄ r₄).2 m₄).2 ⟨g, al.1 g ▸ hg⟩
  have G₀ : (T.fr ∅).Good (𝔞.red c) c₀' := g₀.elim (fun x => Or.inl ⟨x.1, Or.inl x.2⟩) fun x => Or.inr (Or.inr (Or.inl x))
  have G₃ : (T.fr ∅).Good (𝔞.red c) c₃ := by
    by_cases hp : Ent c₃.r (-wPs)
    · exact Or.inl ⟨hp, Or.inr a₃⟩
    rcases g₀ with x | x
    · obtain ⟨g, hg⟩ := ((Chain.entIff (T.fr ∅) (𝔞.red c) c₀' hr).1 i₀.1).1 x.1
      exact absurd (((Chain.entIff (T.fr ∅) (𝔞.red c) c₃ r₃).1 i₃.1).2 ⟨g, p₃.1 g ▸ hg⟩) hp
    refine Or.inr (Or.inr (Or.inl ⟨⟨fun g i j hij hw => ?_, fun v => ⟨i₃.2 v, p₃.2 v ▸ (x.1.2 v).2⟩⟩, a₃⟩))
    by_cases hq : wt i j = -wPs
    · by_contra hne
      exact hp ⟨g, i, j, hq, hne⟩
    · exact q₃ g i j hij (by revert hw hq; revert i j; decide)
  have G₄ : (T.fr ∅).Good (𝔞.red c) c₄ :=
    Or.inr (Or.inr (Or.inl ⟨⟨v₄, fun v => ⟨(n₄ v).1, (n₄ v).2.2 ▸ (sV.2 v).2⟩⟩, a₄⟩))
  have Gs : (T.fr ∅).Good (𝔞.red c) (Q.map (𝔞.red c₁)) := by
    rcases hQE with x | x
    · exact Or.inr (Or.inr (Or.inl ⟨sV, sE _ x⟩))
    refine Or.inr (Or.inr (Or.inr ⟨sV, sE _ x.1, sE _ x.2, fun v => ?_⟩))
    obtain ⟨g, hg, hne⟩ := tT.bigL _ (T.ovl v)
    exact ⟨g, hg, fun h1 => hne (by rw [(hrb _ _).1 h1, one_pow])⟩
  have L₁ := lineP (T.fr ∅) _ ok c₀' c₃ hr r₃ i₀ i₃ ⟨fun g => (p₃.1 g).symm, fun v => (p₃.2 v).symm⟩
  have L₂ := lineM (T.fr ∅) _ ok c₃ c₄ r₃ r₄ m₃ m₄ al
  have L₃ := lineP (T.fr ∅) _ ok c₄ _ r₄ sR ⟨fun g => supp_mono (by decide) (v₄ g), fun v => (n₄ v).1⟩
    ⟨fun g => supp_mono (by decide) (sV.1 g), fun v => (sV.2 v).1⟩
    ⟨fun g => (v₄ g 2 0 (by decide) (by decide)).trans (sV.1 g 2 0 (by decide) (by decide)).symm, fun v => (n₄ v).2.2⟩
  exact ⟨G₀, ((Relation.ReflTransGen.single ⟨G₃, L₁⟩).tail ⟨G₄, L₂⟩).tail ⟨Gs, L₃⟩⟩
end
end
end
