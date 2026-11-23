module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CocConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Descend
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import ReciprocityTheory.Hypotheses.GalCohDefs
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Mathlib.Data.FunLike.Fintype
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.LocHoms
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.ZunrFin

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CcOne

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.ccEx :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ c : InfinitePlace F → G F Ω, ∀ w, w.IsReal → IsCCAt w (c w) := by
  intro F Ω _ _ _ _ _
  classical
  have key : ∀ w : InfinitePlace F, w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
    intro w hw
    have hφ : ∀ a, (starRingEnd ℂ) (w.embedding a) = w.embedding a := by
      intro a
      have h := ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)
      exact RingHom.congr_fun h a
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let e : Ω ≃ₐ[F] algebraicClosure F ℂ := IsAlgClosure.equiv F Ω (algebraicClosure F ℂ)
    let κ : ℂ →ₐ[F] ℂ :=
      { (starRingEnd ℂ) with commutes' := fun a => hφ a }
    let j : Ω →ₐ[F] ℂ := (algebraicClosure F ℂ).val.comp e.toAlgHom
    have hmem : ∀ x : Ω, (κ.comp j) x ∈ (algebraicClosure F ℂ).toSubalgebra := by
      intro x
      show (κ.comp j) x ∈ algebraicClosure F ℂ
      rw [map_mem_algebraicClosure_iff, mem_algebraicClosure_iff]
      exact Algebra.IsAlgebraic.isAlgebraic x
    let f : Ω →ₐ[F] algebraicClosure F ℂ := (κ.comp j).codRestrict _ hmem
    let c0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f
    let c : G F Ω := AlgEquiv.ofBijective c0 (Algebra.IsAlgebraic.algHom_bijective c0)
    refine ⟨c, j.toRingHom, fun x => ?_, ?_⟩
    · show ((e (e.symm (f x)) : algebraicClosure F ℂ) : ℂ) = (starRingEnd ℂ) (j x)
      rw [AlgEquiv.apply_symm_apply]
      rfl
    · have hj : j.toRingHom.comp (algebraMap F Ω) = w.embedding := by
        ext a
        exact j.commutes a
      rw [hj, InfinitePlace.mk_embedding]
  refine ⟨fun w => if hw : w.IsReal then (key w hw).choose else 1, fun w hw => ?_⟩
  simp only [dif_pos hw]
  exact (key w hw).choose_spec
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GwLower

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.gwLower :
    GlobalFiniteness → GreenbergWiles → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContainsAbove S l → ContAction ρ →
      ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ L : LocCond ρ (locFam S Av),
        ∏ v : S, Nat.card (L v) ≤ Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) * (Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ Module.finrank ℚ F) *
          ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) := by
  classical
  intro hGF hGW F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl S ρ hS hρ Av hA L
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := 1) (S := S) hS
  obtain ⟨c, hc⟩ := UpperTheory.V.Ws.Gys.ccEx F Ω
  have e := hGW F Ω l 1 M S ρ one_pos hl hS hρ μ hμ Av hA c hc L
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI hfd : Finite (TDual (ZMod (l ^ 1)) M) := DFunLike.finite _
  haveI hf1 : Finite (H1 ρ) := (hGF F Ω l 1 M S ρ one_pos hS hρ).2.1
  have hM : 0 < Nat.card M := Nat.card_pos
  have p1 : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have p2 : 0 < Nat.card (H0 (twDual μ ρ)) := Nat.card_pos
  have p3 : 0 < ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have p4 : 0 < archH0Card S ρ c := by
    unfold archH0Card
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (pow_pos hM _)
    haveI : Nonempty {m : M // ρ (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  have b2 : Nat.card (H0 (twDual μ ρ)) ≤ Nat.card (TDual (ZMod (l ^ 1)) M) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have b4 : archH0Card S ρ c ≤ Nat.card M ^ Module.finrank ℚ F := by
    unfold archH0Card
    have h1 : (∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
        Nat.card {m : M // ρ (toGS Ω _ (c w)) m = m}) ≤ Nat.card M ^ InfinitePlace.nrRealPlaces F := by
      have h2 := Finset.prod_le_pow_card (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal))
        (fun w => Nat.card {m : M // ρ (toGS Ω _ (c w)) m = m}) (Nat.card M)
        (fun w _ => Nat.card_le_card_of_injective _ Subtype.val_injective)
      have h3 : (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal)).card = InfinitePlace.nrRealPlaces F := by
        rw [InfinitePlace.nrRealPlaces, Fintype.card_subtype]
      rwa [h3] at h2
    refine (Nat.mul_le_mul_right _ h1).trans ?_
    rw [← pow_add]
    refine Nat.pow_le_pow_right hM ?_
    have := InfinitePlace.card_add_two_mul_card_eq_rank F
    omega
  have hpos := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p1 p2) p3) p4
  refine (Nat.le_of_dvd hpos (Dvd.intro_left _ e.symm)).trans ?_
  calc _ = Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) * (Nat.card (H0 (twDual μ ρ)) * archH0Card S ρ c) *
          ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul b2 b4))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.RamCard

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.ramCard :
    ∀ (R D M : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R D M) (I : Subgroup D) (m0 : M), (∀ g, ρ g = 1) → m0 ≠ 0 → Finite (H1 ρ) →
      ∀ φ₁ ∈ Z1 (Representation.trivial R D R), ∀ φ₂ ∈ Z1 (Representation.trivial R D R), (∀ g ∈ I, φ₁ g = 0) → (∃ g, φ₁ g = 1) → (∃ g ∈ I, φ₂ g = 1) →
      2 * Nat.card M ≤ Nat.card (ramLine ρ I m0) := by
  rintro R D M _ _ _ _ _ _ _ _ _ _ ρ I m0 hρ hm0 _ φ₁ hφ₁ φ₂ hφ₂ hI1 ⟨g1, hg1⟩ ⟨g2, hg2I, hg2⟩
  obtain ⟨c1, a1⟩ := (mem_Z1_iff_cocycle _ _).1 hφ₁
  obtain ⟨c2, a2⟩ := (mem_Z1_iff_cocycle _ _).1 hφ₂
  let fn : R → M → D → M := fun t m g => φ₁ g • m + (t * φ₂ g) • m0
  have hz : ∀ t m, fn t m ∈ Z1 ρ := by
    intro t m
    rw [mem_Z1_iff_cocycle]
    refine ⟨(continuous_of_discreteTopology (f := fun p : R × R => p.1 • m + (t * p.2) • m0)).comp
      (c1.prodMk c2), ?_⟩
    intro g h
    simp [fn, hρ g, a1 g h, a2 g h, add_smul, mul_add] <;> abel
  let F : Bool × M → ramLine ρ I m0 := fun p =>
    ⟨Submodule.Quotient.mk ⟨fn (if p.1 then 1 else 0) p.2, hz _ _⟩,
      (mem_ramLine ρ I m0 _).2 ⟨⟨fn (if p.1 then 1 else 0) p.2, hz _ _⟩, fun g hg => by
        show fn _ _ g ∈ _
        simp only [fn, hI1 g hg, zero_smul, zero_add]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m0), rfl⟩⟩
  have hF : Function.Injective F := by
    rintro ⟨b, m⟩ ⟨b', m'⟩ h
    have h1 := congrArg Subtype.val h
    rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1] at h1
    obtain ⟨x, hx⟩ := h1
    have hpt : ∀ g, fn (if b then 1 else 0) m g = fn (if b' then 1 else 0) m' g := by
      intro g
      have h2 := hx g
      rw [hρ g, Module.End.one_apply, sub_self] at h2
      exact sub_eq_zero.1 h2
    have hb : b = b' := by
      have h3 := hpt g2
      simp only [fn, hI1 g2 hg2I, hg2, zero_smul, zero_add, mul_one] at h3
      cases b <;> cases b' <;> simp_all
    subst hb
    have h4 := hpt g1
    simp only [fn, hg1, one_smul] at h4
    rw [add_right_cancel h4]
  have hc := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hc
  exact hc
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SelBig

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.selBig :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), S₀ ⊆ S → ContainsAbove S₀ l → ContAction ρ →
      (∀ v ∈ S, v ∉ S₀ → TrivAt l (ρ.comp (toGS Ω _)) v) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ m0 : M, m0 ≠ 0 →
        2 ^ (S.card - S₀.card) ≤ Nat.card (gysSel S₀ S ρ Av m0) * (Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ (Module.finrank ℚ F + S₀.card)) := by
  classical
  intro P F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl S₀ S ρ hSS hS₀ hρ htr Av hA m0 hm0
  have hS : ContainsAbove S l := fun v hv => hSS (hS₀ v hv)
  have e := gwLower P.gf P.gw F Ω l M hl S ρ hS hρ Av hA (gysL S₀ S ρ Av m0)
  have h0 : ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) ≤ Nat.card M ^ S.card := by
    have := Finset.prod_le_pow_card Finset.univ (fun v : S => Nat.card (H0 (ρ.comp (locFam S Av v)))) (Nat.card M)
      (fun v _ => Nat.card_le_card_of_injective _ Subtype.val_injective)
    rwa [Finset.card_univ, Fintype.card_coe] at this
  have hloc : ∀ v : S, (if v.1 ∈ S₀ then 1 else 2 * Nat.card M) ≤ Nat.card (gysL S₀ S ρ Av m0 v) := by
    intro v
    by_cases hv : v.1 ∈ S₀
    · rw [if_pos hv, show gysL S₀ S ρ Av m0 v = ⊥ from if_pos hv]
      exact Nat.card_pos
    · rw [if_neg hv, show gysL S₀ S ρ Av m0 v = _ from if_neg hv]
      have ht := htr v.1 v.2 hv (Av v) (hA v)
      obtain ⟨φ₁, h1, φ₂, h2, a1, a2, g, a3, a4⟩ := locHoms P.loc.lt P.loc.le P.uo F Ω l (Av v) v.1 (hA v)
        (fun h => hv (hS₀ _ h)) (fun g hg => (ht g hg).2)
      have hc : ContAction (ρ.comp (locFam S Av v)) := hρ.comp ((continuous_locFam S Av v).prodMap continuous_id)
      obtain ⟨-, f1, -, -⟩ := P.loc.lf F Ω l 1 M (Av v) _ v.1 one_pos (hA v) hc
      exact ramCard _ _ M _ _ m0 (fun g => (ht g.1 g.2).1) hm0 f1 φ₁ h1 φ₂ h2 a1 a2 ⟨g, a3, a4⟩
  have h1 : (2 * Nat.card M) ^ (S.card - S₀.card) ≤ ∏ v : S, Nat.card (gysL S₀ S ρ Av m0 v) := by
    refine le_trans (le_of_eq ?_) (Finset.prod_le_prod' fun v _ => hloc v)
    rw [Finset.prod_coe_sort S (fun v => if v ∈ S₀ then 1 else 2 * Nat.card M), Finset.prod_ite, Finset.prod_const_one, one_mul,
      Finset.prod_const, ← Finset.sdiff_eq_filter, Finset.card_sdiff_of_subset hSS]
  have hpos : 0 < Nat.card M ^ (S.card - S₀.card) := pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [← mul_pow]
  refine h1.trans (e.trans ((Nat.mul_le_mul_left _ h0).trans (le_of_eq ?_)))
  have hc : Nat.card M ^ S.card = Nat.card M ^ S₀.card * Nat.card M ^ (S.card - S₀.card) := by
    rw [← pow_add, Nat.add_sub_cancel' (Finset.card_le_card hSS)]
  rw [hc, pow_add]
  ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SelMem

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.selMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), S₀ ⊆ S →
      (∀ v ∈ S, v ∉ S₀ → TrivAt l (ρ.comp (toGS Ω _)) v) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ (m0 : M) (f : Z1 ρ),
        Submodule.Quotient.mk f ∈ gysSel S₀ S ρ Av m0 →
        (fun g => f.1 (toGS Ω _ g)) ∈ Zunr (ρ.comp (toGS Ω _)) S ∧
        (∀ v ∈ S₀, ∀ A, IsPlaceOver A v → ∃ m, ∀ g ∈ Dec (F := F) A, f.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m) ∧
        ∀ v : S, v.1 ∉ S₀ → ∀ g ∈ Ine (F := F) (Av v), f.1 (toGS Ω _ g) ∈ Submodule.span R {m0} := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ _ _ S₀ S ρ hS htriv Av hA m0 f hf
  have hZ : (fun g => f.1 (toGS Ω _ g)) ∈ Z1 (ρ.comp (toGS Ω _) : Representation R (G F Ω) M) :=
    ⟨f.2.1.comp QuotientGroup.continuous_mk, fun a b => by
      have := f.2.2 (toGS Ω _ a) (toGS Ω _ b)
      rw [← map_mul] at this
      exact this⟩
  have hloc := (mem_Sel _ _ _ _ _).1 hf
  refine ⟨⟨hZ, fun v hv A hAv g hg => ?_⟩, fun v hv A hAv => ?_, fun v hv g hg => ?_⟩
  · have h1 : f.1 1 = 0 := by
      have := f.2.2 1 1
      rw [one_mul, map_one] at this
      exact left_eq_add.1 this
    have h2 : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g = 1 := by
      refine (QuotientGroup.eq_one_iff g).2 ?_
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hv, A, hAv, hg⟩
    show f.1 (toGS Ω _ g) = 0
    rw [h2, h1]
  · have h := hloc ⟨v, hS hv⟩
    rw [show gysL S₀ S ρ Av m0 ⟨v, hS hv⟩ = ⊥ from if_pos hv, Submodule.mem_bot] at h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h)
    exact (UpperTheory.V.Ws.Gys.cocConj F Ω R M (ρ.comp (toGS Ω _)) _ hZ v (Av ⟨v, hS hv⟩) A (hA ⟨v, hS hv⟩) hAv).1
      ⟨m, fun g hg => hm ⟨g, hg⟩⟩
  · have h := hloc v
    rw [show gysL S₀ S ρ Av m0 v = ramLine (ρ.comp (locFam S Av v)) ((Ine (F := F) (Av v)).subgroupOf (Dec (F := F) (Av v))) m0
      from if_neg hv, mem_ramLine] at h
    obtain ⟨f', h1, h2⟩ := h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 h2)
    have hd : g ∈ Dec (F := F) (Av v) := Ine_le_Dec _ hg
    have h3 := hm ⟨g, hd⟩
    have h4 : ρ (toGS Ω _ g) = 1 := (htriv v.1 v.2 hv (Av v) (hA v) g hd).1
    have h5 : f'.1 ⟨g, hd⟩ - f.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := h3
    rw [h4, Module.End.one_apply, sub_self, sub_eq_zero] at h5
    rw [← h5]
    exact h1 ⟨g, hd⟩ hg
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GysCore

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.gysCore :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (ρ : Representation (ZMod (l ^ 1)) (G F Ω) M) (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (Q : Set (HeightOneSpectrum (𝓞 F))), ContAction ρ → ContainsAbove S₀ l → UnrOut ρ S₀ →
      Q.Infinite → (∀ v ∈ Q, TrivAt l ρ v) → ∀ m0 : M, m0 ≠ 0 →
        ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ S, v ∈ S₀ ∨ v ∈ Q) ∧ ∃ c ∈ Zunr ρ S, (∀ v ∈ S₀, ∀ A, IsPlaceOver A v → ∃ m, ∀ g ∈ Dec (F := F) A, c g = ρ g m - m) ∧
          ∃ g, ρ g = 1 ∧ c g ≠ 0 ∧ c g ∈ Submodule.span (ZMod (l ^ 1)) {m0} := by
  classical
  intro hP F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl ρ S₀ Q hρ hS₀ hu hQ hT m0 hm0
  have hfin : Finite (Zunr ρ S₀) := UpperTheory.V.Ws.Gys.zunrFin hP.gf F Ω l M ρ S₀ hS₀ hρ hu
  obtain ⟨C, hC⟩ : ∃ C, C = Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ (Module.finrank ℚ F + S₀.card) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = Nat.card (Zunr ρ S₀) := ⟨_, rfl⟩
  obtain ⟨S₁, hS₁, hcard⟩ := (hQ.diff S₀.finite_toSet).exists_subset_card_eq (N * C)
  have hdisj : Disjoint S₀ S₁ := Finset.disjoint_left.2 fun v h0 h1 => (hS₁ (Finset.mem_coe.2 h1)).2 (Finset.mem_coe.2 h0)
  obtain ⟨S, hS⟩ : ∃ S, S = S₀ ∪ S₁ := ⟨_, rfl⟩
  have hsub : S₀ ⊆ S := hS ▸ Finset.subset_union_left
  have hSQ : ∀ v ∈ S, v ∈ S₀ ∨ v ∈ Q := fun v hv => by
    rw [hS, Finset.mem_union] at hv
    exact hv.imp_right fun h => (hS₁ (Finset.mem_coe.2 h)).1
  have hSc : S.card - S₀.card = N * C := by
    rw [hS, Finset.card_union_of_disjoint hdisj, hcard]; omega
  have huS : UnrOut ρ S := fun v hv => hu v fun h => hv (hsub h)
  obtain ⟨ρS, rfl, hρS⟩ := UpperTheory.V.Ws.Gys.descend F Ω _ M ρ S hρ huS
  have hTS : ∀ v ∈ S, v ∉ S₀ → TrivAt l (ρS.comp (toGS Ω _)) v := fun v hv h0 => hT v ((hSQ v hv).resolve_left h0)
  let Av : S → ValuationSubring Ω := fun v => placeOf Ω v.1
  have hAv : ∀ v, IsPlaceOver (Av v) v.1 := fun v => isPlaceOver_placeOf Ω v.1
  have hbig := UpperTheory.V.Ws.Gys.selBig hP F Ω l M hl S₀ S ρS hsub hS₀ hρS hTS Av hAv m0 hm0
  have hmem := UpperTheory.V.Ws.Gys.selMem F Ω l _ M S₀ S ρS hsub hTS Av hAv m0
  rw [← hC, hSc] at hbig
  refine ⟨S, hSQ, ?_⟩
  by_contra hno
  have hout : ∀ x : gysSel S₀ S ρS Av m0, Submodule.Quotient.mk (Quotient.out x.1) ∈ gysSel S₀ S ρS Av m0 := fun x => by
    have : (Submodule.Quotient.mk (Quotient.out x.1) : H1 ρS) = x.1 := Quotient.out_eq x.1
    rw [this]; exact x.2
  have hz : ∀ x : gysSel S₀ S ρS Av m0, (fun g => (Quotient.out x.1).1 (toGS Ω _ g)) ∈ Zunr (ρS.comp (toGS Ω _)) S₀ := fun x => by
    obtain ⟨h1, h2, h3⟩ := hmem _ (hout x)
    refine ⟨h1.1, fun v hv A hA => ?_⟩
    by_cases hvS : v ∈ S
    · refine (UpperTheory.V.Ws.Gys.cocConj F Ω _ M _ _ h1.1 v (Av ⟨v, hvS⟩) A (hAv ⟨v, hvS⟩) hA).2 fun g hg => ?_
      have hg1 := (hTS v hvS hv _ (hAv ⟨v, hvS⟩) g (Ine_le_Dec _ hg)).1
      refine ⟨hg1, ?_⟩
      by_contra hne
      exact hno ⟨_, h1, h2, g, hg1, hne, h3 ⟨v, hvS⟩ hv g hg⟩
    · exact h1.2 v hvS A hA
  have hinj : Function.Injective fun x : gysSel S₀ S ρS Av m0 => (⟨_, hz x⟩ : Zunr (ρS.comp (toGS Ω _)) S₀) := by
    intro x y hxy
    have h1 : Quotient.out x.1 = Quotient.out y.1 := by
      refine Subtype.ext (funext fun g => ?_)
      obtain ⟨σ, rfl⟩ : ∃ σ, toGS Ω _ σ = g := QuotientGroup.mk_surjective g
      exact congrFun (congrArg Subtype.val hxy) σ
    exact Subtype.ext (Quotient.out_injective h1)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [← hN] at hle
  have h2 : N * C < 2 ^ (N * C) := Nat.lt_two_pow_self
  exact absurd (hbig.trans (Nat.mul_le_mul_right C hle)) (not_le.2 h2)
end
end
